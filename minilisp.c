/* This software is licensed with The Unlicense,
** effectively making it released to the public domain. */

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* If you're having trouble getting this to compile,
** try removing __attribute__((noreturn)) from this function. */
static __attribute__((noreturn)) void error(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    exit(1);
}

/*====================================================================**
** Lisp objects
**====================================================================*/

/* The Lisp object type */
enum {
    /* Regular objects visible from the user */
    TINT = 1,
    TCELL,
    TSYMBOL,
    TPRIMITIVE,
    TFUNCTION,
    TMACRO,
    TENV,
    /* The marker that indicates the object has been moved to other location by GC. The new location
    ** can be found at the forwarding pointer. Only the functions to do garbage collection set and
    ** handle the object of this type. Other functions will never see the object of this type. */
    TMOVED,
    /* Const objects. They are statically allocated and will never be managed by GC. */
    TTRUE, TNIL, TDOT, TCPAREN
};

/* Typedef for the primitive function */
struct Obj;
typedef struct Obj *Primitive(void *root, struct Obj **env, struct Obj **args);

/* The object type */
typedef struct Obj {
    /* The first word of the object represents the type of the object. Any code that handles object
    ** needs to check its type first, then access the following union members. */
    int type;

    /* The total size of the object, including "type" field, this field, the contents, and the
    ** padding at the end of the object. */
    int size;

    /* Object values. */
    union ObjValue {
        /* Int */
        int value;
        /* Cell */
        struct Cell {
            struct Obj *car;
            struct Obj *cdr;
        } cell;
        /* Symbol */
        char name[1];
        /* Primitive */
        Primitive *fn;
        /* Function or Macro */
        struct Macro {
            struct Obj *params;
            struct Obj *body;
            struct Obj *env;
        } mcr;
        /* Environment frame. This is a linked list of association lists
        ** containing the mapping from symbols to their value. */
        struct Frame {
            struct Obj *vars;
            struct Obj *up;
        } frm;
        /* Forwarding pointer */
        void *moved;
    } obval;
} Obj;

/* Constants */
static Obj True   = { TTRUE,   sizeof(True),   { 0 } };
static Obj Nil    = { TNIL,    sizeof(Nil),    { 0 } };
static Obj Dot    = { TDOT,    sizeof(Dot),    { 0 } };
static Obj Cparen = { TCPAREN, sizeof(Cparen), { 0 } };

/* The list containing all symbols. Such data structure is traditionally called the "obarray",
** but I avoid using it as a variable name as this is not an array but a list. */
static Obj *Symbols;

/*====================================================================**
** Memory management
**====================================================================*/

/* The size of the heap in byte */
#define MEMORY_SIZE 65536

/* Typedef type used for pointer arithmetics and casts */
typedef unsigned char uchar;

/* The pointer pointing to the beginning of the current heap */
static void *memory;

/* The pointer pointing to the beginning of the old heap */
static void *from_space;

/* The number of bytes allocated from the heap */
static size_t mem_nused = 0;

/* Flags to debug GC */
static char gc_running = 0, debug_gc = 0, always_gc = 0;

static void gc(void *root);

/* Currently we are using Cheney's copying GC algorithm, with which the available memory is split
** into two halves and all objects are moved from one half to another every time GC is invoked. That
** means the address of the object keeps changing. If you take the address of an object and keep it
** in a C variable, dereferencing it could cause SEGV because the address becomes invalid after GC
** runs.
**
** In order to deal with that, all access from C to Lisp objects will go through two levels of
** pointer dereferences. The C local variable is pointing to a pointer on the C stack, and the
** pointer is pointing to the Lisp object. GC is aware of the pointers in the stack and updates
** their contents with the objects' new addresses when GC happens.
**
** The following is a macro to reserve the area in the C stack for the pointers. The contents of
** this area are considered to be GC root.
**
** Be careful not to bypass the two levels of pointer indirections. If you create a direct pointer
** to an object, it'll cause a subtle bug. Such code would work in most cases but fails with SEGV if
** GC happens during the execution of the code. Any code that allocates memory may invoke GC. */

#define ROOT_END ((void *)-1)

#define ADD_ROOT(size)                          \
    void *root_ADD_ROOT_[size + 2];             \
    int i;                                      \
    root_ADD_ROOT_[0] = root;                   \
    for (i = 1; i <= size; i++)                 \
        root_ADD_ROOT_[i] = NULL;               \
    root_ADD_ROOT_[size + 1] = ROOT_END;        \
    root = root_ADD_ROOT_

#define DEFINE1(var1)                           \
    Obj **var1;                                 \
    ADD_ROOT(1);                                \
    var1 = (Obj **)(root_ADD_ROOT_ + 1)

#define DEFINE2(var1, var2)                     \
    Obj **var1, **var2;                         \
    ADD_ROOT(2);                                \
    var1 = (Obj **)(root_ADD_ROOT_ + 1);        \
    var2 = (Obj **)(root_ADD_ROOT_ + 2)

#define DEFINE3(var1, var2, var3)               \
    Obj **var1, **var2, **var3;                 \
    ADD_ROOT(3);                                \
    var1 = (Obj **)(root_ADD_ROOT_ + 1);        \
    var2 = (Obj **)(root_ADD_ROOT_ + 2);        \
    var3 = (Obj **)(root_ADD_ROOT_ + 3)

#define DEFINE4(var1, var2, var3, var4)         \
    Obj **var1, **var2, **var3, **var4;         \
    ADD_ROOT(4);                                \
    var1 = (Obj **)(root_ADD_ROOT_ + 1);        \
    var2 = (Obj **)(root_ADD_ROOT_ + 2);        \
    var3 = (Obj **)(root_ADD_ROOT_ + 3);        \
    var4 = (Obj **)(root_ADD_ROOT_ + 4)

/* Round up the given value to a multiple of size. Size must be a power of 2. It adds size - 1
** first, then zero-ing the least significant bits to make the result a multiple of size. I know
** these bit operations may look a little bit tricky, but it's efficient and thus frequently used. */
static size_t roundup(const size_t var, const size_t size) {
    return (var + size - 1) & ~(size - 1);
}

/* Allocates memory block. This may start GC if we don't have enough memory. */
static Obj *alloc(void *root, const int type, size_t size) {
    Obj *obj;

    /* The object must be large enough to contain a pointer for the forwarding pointer. Make it
    ** larger if it's smaller than that. */
    size = roundup(size, sizeof(void *));

    /* Add the size of the type tag and size fields. */
    size += offsetof(Obj, obval.value);

    /* Round up the object size to the nearest alignment boundary, so that the next object will be
    ** allocated at the proper alignment boundary. Currently we align the object at the same
    ** boundary as the pointer. */
    size = roundup(size, sizeof(void *));

    /* If the debug flag is on, allocate a new memory space to force all the existing objects to
    ** move to new addresses, to invalidate the old addresses. By doing this the GC behavior becomes
    ** more predictable and repeatable. If there's a memory bug that the C variable has a direct
    ** reference to a Lisp object, the pointer will become invalid by this GC call. Dereferencing
    ** that will immediately cause SEGV. */
    if (always_gc && !gc_running) gc(root);

    /* Otherwise, run GC only when the available memory is not large enough. */
    if (!always_gc && MEMORY_SIZE < mem_nused + size)
        gc(root);

    /* Terminate the program if we couldn't satisfy the memory request. This can happen if the
    ** requested size was too large or the from-space was filled with too many live objects. */
    if (MEMORY_SIZE < mem_nused + size) error("Memory exhausted");

    /* Allocate the object. */
    obj = (Obj *)((uchar *)memory + mem_nused);
    obj->type = type, obj->size = size;
    mem_nused += size;
    return obj;
}

/*====================================================================**
** Garbage collector
**====================================================================*/

/* Cheney's algorithm uses two pointers to keep track of GC status. At first both pointers point to
** the beginning of the to-space. As GC progresses, they are moved towards the end of the
** to-space. The objects before "scan1" are the objects that are fully copied. The objects between
** "scan1" and "scan2" have already been copied, but may contain pointers to the from-space. "scan2"
** points to the beginning of the free space. */
static Obj *scan1, *scan2;

/* Moves one object from the from-space to the to-space. Returns the object's new address. If the
** object has already been moved, does nothing but just returns the new address. */
static Obj *forward(Obj *obj) {
    Obj *newloc;

    /* If the object's address is not in the from-space, the object is not managed by GC nor it
    ** has already been moved to the to-space. */
    ptrdiff_t offset = (uchar *)obj - (uchar *)from_space;
    if (offset < 0 || MEMORY_SIZE <= offset) return obj;

    /* The pointer is pointing to the from-space, but the object there was a tombstone. Follow the
    ** forwarding pointer to find the new location of the object. */
    if (obj->type == TMOVED) return obj->obval.moved;

    /* Otherwise, the object has not been moved yet. Move it. */
    newloc = scan2;
    memcpy(newloc, obj, obj->size);
    scan2 = (Obj *)((uchar *)scan2 + obj->size);

    /* Put a tombstone at the location where the object used to occupy, so that the following call
    ** of forward() can find the object's new location. */
    obj->type = TMOVED, obj->obval.moved = newloc;
    return newloc;
}

static void *alloc_semispace() { return calloc(1, MEMORY_SIZE); }

/* Copies the root objects. */
static void forward_root_objects(void *root) {
    void **frame; int i;
    Symbols = forward(Symbols);
    for (frame = root; frame; frame = *(void ***)frame)
        for (i = 1; frame[i] != ROOT_END; i++)
            if (frame[i]) frame[i] = forward(frame[i]);
}

/* Implements Cheney's copying garbage collection algorithm.
** http://en.wikipedia.org/wiki/Cheney%27s_algorithm */
static void gc(void *root) {
    size_t old_nused;
    assert(!gc_running);
    gc_running = 1;

    /* Allocate a new semi-space. */
    from_space = memory;
    memory = alloc_semispace();

    /* Initialize the two pointers for GC. Initially they point to the beginning of the to-space. */
    scan1 = scan2 = memory;

    /* Copy the GC root objects first. This moves the pointer scan2. */
    forward_root_objects(root);

    /* Copy the objects referenced by the GC root objects located between scan1 and scan2. Once it's
    ** finished, all live objects (i.e. objects reachable from the root) will have been copied to
    ** the to-space. */
    while (scan1 < scan2) {
        switch (scan1->type) {
        case TINT: /* FALLTHROUGH */
        case TSYMBOL: /* FALLTHROUGH */
        case TPRIMITIVE:
            /* Any of the above types does not contain a pointer to a GC-managed object. */
            break;
        case TCELL:
            scan1->obval.cell.car = forward(scan1->obval.cell.car);
            scan1->obval.cell.cdr = forward(scan1->obval.cell.cdr);
            break;
        case TFUNCTION: /* FALLTHROUGH */
        case TMACRO:
            scan1->obval.mcr.params = forward(scan1->obval.mcr.params);
            scan1->obval.mcr.body = forward(scan1->obval.mcr.body);
            scan1->obval.mcr.env = forward(scan1->obval.mcr.env);
            break;
        case TENV:
            scan1->obval.frm.vars = forward(scan1->obval.frm.vars);
            scan1->obval.frm.up = forward(scan1->obval.frm.up);
            break;
        default:
            error("Bug: copy: unknown type %d", scan1->type);
        }
        scan1 = (Obj *)((uchar *)scan1 + scan1->size);
    }

    /* Finish up GC. */
    free(from_space);
    from_space = NULL, old_nused = mem_nused;
    mem_nused = (size_t)((uchar *)scan1 - (uchar *)memory);
    if (debug_gc)
        fprintf(stderr, "GC: %lu bytes out of %lu bytes copied.\n", mem_nused, old_nused);
    gc_running = 0;
}

/*====================================================================**
** Constructors
**====================================================================*/

static Obj *make_int(void *root, const int value) {
    Obj *r = alloc(root, TINT, sizeof(int));
    r->obval.value = value;
    return r;
}

static Obj *cons(void *root, Obj **car, Obj **cdr) {
    Obj *cell = alloc(root, TCELL, sizeof(Obj *) * 2);
    cell->obval.cell.car = *car, cell->obval.cell.cdr = *cdr;
    return cell;
}

static Obj *make_symbol(void *root, const char *name) {
    Obj *sym = alloc(root, TSYMBOL, strlen(name) + 1);
    strcpy(sym->obval.name, name);
    return sym;
}

static Obj *make_primitive(void *root, Primitive *fn) {
    Obj *r = alloc(root, TPRIMITIVE, sizeof(Primitive *));
    r->obval.fn = fn;
    return r;
}

static Obj *make_function(void *root, Obj **env, int type, Obj **params, Obj **body) {
    Obj *r;
    assert(type == TFUNCTION || type == TMACRO);
    r = alloc(root, type, sizeof(Obj *) * 3);
    r->obval.mcr.params = *params, r->obval.mcr.body = *body, r->obval.mcr.env = *env;
    return r;
}

struct Obj *make_env(void *root, Obj **vars, Obj **up) {
    Obj *r = alloc(root, TENV, sizeof(Obj *) * 2);
    r->obval.frm.vars = *vars, r->obval.frm.up = *up;
    return r;
}

/* Returns ((x . y) . a) */
static Obj *acons(void *root, Obj **x, Obj **y, Obj **a) {
    DEFINE1(cell);
    *cell = cons(root, x, y);
    return cons(root, cell, a);
}

/*====================================================================**
** Parser
**
** This is a hand-written recursive-descendent parser.
**====================================================================*/

#define SYMBOL_MAX_LEN 200
static const char symbol_chars[] = "~!@#$%^&*-_=+:/?<>";

static Obj *read_expr(void *root);

static int peek(void) {
    int c = getchar();
    ungetc(c, stdin);
    return c;
}

/* Destructively reverses the given list. */
static Obj *reverse(Obj *p) {
    Obj *ret = &Nil;
    while (p != &Nil) {
        Obj *head = p;
        p = p->obval.cell.cdr, head->obval.cell.cdr = ret;
        ret = head;
    }
    return ret;
}

/* Skips the input until newline is found. Newline is one of \r, \r\n or \n. */
static void skip_line(void) {
    for (;;) {
        int c = getchar();
        if (c == EOF || c == '\n')
            return;
        if (c == '\r') {
            if (peek() == '\n')
                getchar();
            return;
        }
    }
}

/* Reads a list. Note that '(' has already been read. */
static Obj *read_list(void *root) {
    DEFINE3(obj, head, last);
    *head = &Nil;
    for (;;) {
        *obj = read_expr(root);
        if (!*obj) error("Unclosed parenthesis");
        if (*obj == &Cparen) return reverse(*head);
        if (*obj == &Dot) {
            Obj *ret;
            *last = read_expr(root);
            if (read_expr(root) != &Cparen)
                error("Closed parenthesis expected after dot");
            ret = reverse(*head);
            (*head)->obval.cell.cdr = *last;
            return ret;
        }
        *head = cons(root, obj, head);
    }
}

/* May create a new symbol. If there's a symbol with the same name, it will not create a new symbol
** but return the existing one. */
static Obj *intern(void *root, const char *name) {
    Obj *p;
    DEFINE1(sym);
    for (p = Symbols; p != &Nil; p = p->obval.cell.cdr)
        if (strcmp(name, p->obval.cell.car->obval.name) == 0)
            return p->obval.cell.car;
    *sym = make_symbol(root, name);
    Symbols = cons(root, sym, &Symbols);
    return *sym;
}

/* Reader marcro ' (single quote). It reads an expression and returns (quote <expr>). */
static Obj *read_quote(void *root) {
    Obj* PNil = &Nil;
    DEFINE2(sym, tmp);
    *sym = intern(root, "quote");
    *tmp = read_expr(root);
    *tmp = cons(root, tmp, &PNil);
    *tmp = cons(root, sym, tmp);
    return *tmp;
}

static int read_number(int val) {
    while (isdigit(peek()))
        val = val * 10 + (getchar() - '0');
    return val;
}

static Obj *read_symbol(void *root, char c) {
    char buf[SYMBOL_MAX_LEN + 1];
    int len = 1;
    buf[0] = c;
    while (isalnum(peek()) || strchr(symbol_chars, peek())) {
        if (SYMBOL_MAX_LEN <= len) error("Symbol name too long");
        buf[len++] = getchar();
    }
    buf[len] = '\0';
    return intern(root, buf);
}

static Obj *read_expr(void *root) {
    for (;;) {
        int c = getchar();
        if (isspace(c)) continue;
        if (c == EOF) return NULL;
        if (c == ';') { skip_line(); continue; }
        if (c == '(') return read_list(root);
        if (c == ')') return &Cparen;
        if (c == '.') return &Dot;
        if (c == '\'') return read_quote(root);
        if (isdigit(c)) return make_int(root, read_number(c - '0'));
        if (c == '-' && isdigit(peek())) return make_int(root, -read_number(0));
        if (isalpha(c) || strchr(symbol_chars, c)) return read_symbol(root, c);
        error("Don't know how to handle %c", c);
    }
}

/* Prints the given object. */
static void print(Obj *obj) {
    switch (obj->type) {
    case TCELL:
        printf("(");
        for (;;) {
            print(obj->obval.cell.car);
            if (obj->obval.cell.cdr == &Nil)
                break;
            if (obj->obval.cell.cdr->type != TCELL) {
                printf(" . ");
                print(obj->obval.cell.cdr);
                break;
            }
            printf(" ");
            obj = obj->obval.cell.cdr;
        }
        printf(")");
        return;
    case TINT:       printf("%d", obj->obval.value); return;
    case TSYMBOL:    printf("%s", obj->obval.name);  return;
    case TPRIMITIVE: printf("<primitive>");          return;
    case TFUNCTION:  printf("<function>");           return;
    case TMACRO:     printf("<macro>");              return;
    case TMOVED:     printf("<moved>");              return;
    case TTRUE:      printf("t");                    return;
    case TNIL:       printf("()");                   return;
    default:
        error("Bug: print: Unknown tag type: %d", obj->type);
    }
}

/* Returns the length of the given list. -1 if it's not a proper list. */
static int length(Obj *list) {
    int len = 0;
    for (; list->type == TCELL; list = list->obval.cell.cdr)
        len++;
    return list == &Nil ? len : -1;
}

/*====================================================================**
** Evaluator
**====================================================================*/

static Obj *eval(void *root, Obj **env, Obj **obj);

static void add_variable(void *root, Obj **env, Obj **sym, Obj **val) {
    DEFINE2(vars, tmp);
    *vars = (*env)->obval.frm.vars;
    *tmp = acons(root, sym, val, vars);
    (*env)->obval.frm.vars = *tmp;
}

/* Returns a newly created environment frame. */
static Obj *push_env(void *root, Obj **env, Obj **vars, Obj **vals) {
    DEFINE3(map, sym, val);
    *map = &Nil;
    for (; (*vars)->type == TCELL; *vars = (*vars)->obval.cell.cdr, *vals = (*vals)->obval.cell.cdr) {
        if ((*vals)->type != TCELL)
            error("Cannot apply function: number of argument does not match");
        *sym = (*vars)->obval.cell.car, *val = (*vals)->obval.cell.car;
        *map = acons(root, sym, val, map);
    }
    if (*vars != &Nil)
        *map = acons(root, vars, vals, map);
    return make_env(root, map, env);
}

/* Evaluates the list elements from head and returns the last return value. */
static Obj *progn(void *root, Obj **env, Obj **list) {
    DEFINE2(lp, r);
    for (*lp = *list; *lp != &Nil; *lp = (*lp)->obval.cell.cdr) {
        *r = (*lp)->obval.cell.car;
        *r = eval(root, env, r);
    }
    return *r;
}

/* Evaluates all the list elements and returns their return values as a new list. */
static Obj *eval_list(void *root, Obj **env, Obj **list) {
    DEFINE4(head, lp, expr, result);
    *head = &Nil;
    for (lp = list; *lp != &Nil; *lp = (*lp)->obval.cell.cdr) {
        *expr = (*lp)->obval.cell.car;
        *result = eval(root, env, expr);
        *head = cons(root, result, head);
    }
    return reverse(*head);
}

static char is_list(Obj *obj) { return obj == &Nil || obj->type == TCELL; }

static Obj *apply_func(void *root, Obj **fn, Obj **args) {
    DEFINE3(params, newenv, body);
    *params = (*fn)->obval.mcr.params, *newenv = (*fn)->obval.mcr.env;
    *newenv = push_env(root, newenv, params, args);
    *body = (*fn)->obval.mcr.body;
    return progn(root, newenv, body);
}

/* Apply fn with args. */
static Obj *apply(void *root, Obj **env, Obj **fn, Obj **args) {
    if (!is_list(*args))
        error("argument must be a list");
    if ((*fn)->type == TPRIMITIVE)
        return (*fn)->obval.fn(root, env, args);
    if ((*fn)->type == TFUNCTION) {
        DEFINE1(eargs);
        *eargs = eval_list(root, env, args);
        return apply_func(root, fn, eargs);
    }
    error("not supported");
}

/* Searches for a variable by symbol. Returns null if not found. */
static Obj *find(Obj **env, Obj *sym) {
    Obj *p, *cell, *bind;
    for (p = *env; p != &Nil; p = p->obval.frm.up) {
        for (cell = p->obval.frm.vars; cell != &Nil; cell = cell->obval.cell.cdr) {
            bind = cell->obval.cell.car;
            if (sym == bind->obval.cell.car) return bind;
        }
    }
    return NULL;
}

/* Expands the given macro application form. */
static Obj *macroexpand(void *root, Obj **env, Obj **obj) {
    if ((*obj)->type == TCELL && (*obj)->obval.cell.car->type == TSYMBOL)
    {
        DEFINE3(bind, macro, args);
        *bind = find(env, (*obj)->obval.cell.car);
        if (!*bind || (*bind)->obval.cell.cdr->type != TMACRO) return *obj;
        *macro = (*bind)->obval.cell.cdr, *args = (*obj)->obval.cell.cdr;
        return apply_func(root, macro, args);
    }
    return *obj;
}

/* Evaluates the S expression. */
static Obj *eval(void *root, Obj **env, Obj **obj) {
    switch ((*obj)->type) {
    case TINT:
    case TPRIMITIVE:
    case TFUNCTION:
    case TTRUE:
    case TNIL:
        /* Self-evaluating objects */
        return *obj;
    case TSYMBOL: {
        /* Variable */
        Obj *bind = find(env, *obj);
        if (!bind) error("Undefined symbol: %s", (*obj)->obval.name);
        return bind->obval.cell.cdr;
    }
    case TCELL: {
        /* Function application form */
        DEFINE3(fn, expanded, args);
        *expanded = macroexpand(root, env, obj);
        if (*expanded != *obj) return eval(root, env, expanded);
        *fn = (*obj)->obval.cell.car;
        *fn = eval(root, env, fn);
        *args = (*obj)->obval.cell.cdr;
        if ((*fn)->type != TPRIMITIVE && (*fn)->type != TFUNCTION)
            error("The head of a list must be a function");
        return apply(root, env, fn, args);
    }
    default:
        error("Bug: eval: Unknown tag type: %d", (*obj)->type);
    }
}

/*====================================================================**
** Primitive functions and special forms
**====================================================================*/

/* 'expr */
static Obj *prim_quote(void *root, Obj **env, Obj **list) {
    if (length(*list) != 1) error("Malformed quote");
    return (*list)->obval.cell.car;
}

/* (cons expr expr) */
static Obj *prim_cons(void *root, Obj **env, Obj **list) {
    Obj *cell;
    if (length(*list) != 2) error("Malformed cons");
    cell = eval_list(root, env, list);
    cell->obval.cell.cdr = cell->obval.cell.cdr->obval.cell.car;
    return cell;
}

/* (car <cell>) */
static Obj *prim_car(void *root, Obj **env, Obj **list) {
    Obj *args = eval_list(root, env, list);
    if (args->obval.cell.car->type != TCELL || args->obval.cell.cdr != &Nil)
        error("Malformed car");
    return args->obval.cell.car->obval.cell.car;
}

/* (cdr <cell>) */
static Obj *prim_cdr(void *root, Obj **env, Obj **list) {
    Obj *args = eval_list(root, env, list);
    if (args->obval.cell.car->type != TCELL || args->obval.cell.cdr != &Nil)
        error("Malformed cdr");
    return args->obval.cell.car->obval.cell.cdr;
}

/* (setq <symbol> expr) */
static Obj *prim_setq(void *root, Obj **env, Obj **list) {
    if (length(*list) == 2 && (*list)->obval.cell.car->type == TSYMBOL) {
        DEFINE2(bind, value);
        *bind = find(env, (*list)->obval.cell.car);
        if (!*bind) error("Unbound variable %s", (*list)->obval.cell.car->obval.name);
        *value = (*list)->obval.cell.cdr->obval.cell.car;
        *value = eval(root, env, value);
        (*bind)->obval.cell.cdr = *value;
        return *value;
    }
    error("Malformed setq");
}

/* (setcar <cell> expr) */
static Obj *prim_setcar(void *root, Obj **env, Obj **list) {
    DEFINE1(args);
    *args = eval_list(root, env, list);
    if (length(*args) != 2 || (*args)->obval.cell.car->type != TCELL)
        error("Malformed setcar");
    (*args)->obval.cell.car->obval.cell.car = (*args)->obval.cell.cdr->obval.cell.car;
    return (*args)->obval.cell.car;
}

/* (while cond expr ...) */
static Obj *prim_while(void *root, Obj **env, Obj **list) {
    if (length(*list) >= 2) {
        DEFINE2(cond, exprs);
        *cond = (*list)->obval.cell.car;
        while (eval(root, env, cond) != &Nil) {
            *exprs = (*list)->obval.cell.cdr;
            eval_list(root, env, exprs);
        }
        return &Nil;
    }
    error("Malformed while");
}

/* (gensym) */
static Obj *prim_gensym(void *root, Obj **env, Obj **list) {
    static unsigned short count = 0;
    char buf[10];
    sprintf(buf, "G__%u", count++);
    return make_symbol(root, buf);
}

/* (+ <integer> ...) */
static Obj *prim_plus(void *root, Obj **env, Obj **list) {
    int sum = 0; Obj *args;
    for (args = eval_list(root, env, list); args != &Nil; args = args->obval.cell.cdr) {
        if (args->obval.cell.car->type != TINT) error("+ takes only numbers");
        sum += args->obval.cell.car->obval.value;
    }
    return make_int(root, sum);
}

/* (- <integer> ...) */
static Obj *prim_minus(void *root, Obj **env, Obj **list) {
    Obj *args = eval_list(root, env, list), *p; int r;
    for (p = args; p != &Nil; p = p->obval.cell.cdr)
        if (p->obval.cell.car->type != TINT)
            error("- takes only numbers");
    if (args->obval.cell.cdr == &Nil)
        return make_int(root, -args->obval.cell.car->obval.value);
    else r = args->obval.cell.car->obval.value;
    for (p = args->obval.cell.cdr; p != &Nil; p = p->obval.cell.cdr)
        r -= p->obval.cell.car->obval.value;
    return make_int(root, r);
}

/* (* <integer> ...) */
static Obj *prim_mult(void *root, Obj **env, Obj **list) {
    int product = 1; Obj *args;
    for (args = eval_list(root, env, list); args != &Nil; args = args->obval.cell.cdr) {
        if (args->obval.cell.car->type != TINT) error("* takes only numbers");
        product *= args->obval.cell.car->obval.value;
    }
    return make_int(root, product);
}

/* (/ <integer> ...) */
static Obj *prim_div(void *root, Obj **env, Obj **list) {
    Obj *args = eval_list(root, env, list), *p; int r;
    for (p = args; p != &Nil; p = p->obval.cell.cdr)
        if (p->obval.cell.car->type != TINT)
            error("- takes only numbers");
    r = args->obval.cell.car->obval.value;
    for (p = args->obval.cell.cdr; p != &Nil; p = p->obval.cell.cdr)
        r /= p->obval.cell.car->obval.value;
    return make_int(root, r);
}

/* (< <integer> <integer>) */
static Obj *prim_lt(void *root, Obj **env, Obj **list) {
    Obj *args = eval_list(root, env, list), *x, *y;
    if (length(args) != 2) error("malformed <");
    x = args->obval.cell.car, y = args->obval.cell.cdr->obval.cell.car;
    if (x->type != TINT || y->type != TINT)
        error("< takes only numbers");
    return x->obval.value < y->obval.value ? &True : &Nil;
}

static Obj *handle_function(void *root, Obj **env, Obj **list, int type) {
    Obj *p;
    DEFINE2(params, body);
    if ((*list)->type != TCELL || !is_list((*list)->obval.cell.car) || (*list)->obval.cell.cdr->type != TCELL)
        error("Malformed lambda");

    for (p = (*list)->obval.cell.car; p->type == TCELL; p = p->obval.cell.cdr)
        if (p->obval.cell.car->type != TSYMBOL)
            error("Parameter must be a symbol");
    if (p != &Nil && p->type != TSYMBOL)
        error("Parameter must be a symbol");
    *params = (*list)->obval.cell.car, *body = (*list)->obval.cell.cdr;
    return make_function(root, env, type, params, body);
}

/* (lambda (<symbol> ...) expr ...) */
static Obj *prim_lambda(void *root, Obj **env, Obj **list)
{ return handle_function(root, env, list, TFUNCTION); }

static Obj *handle_defun(void *root, Obj **env, Obj **list, int type) {
    DEFINE3(fn, sym, rest);
    if ((*list)->obval.cell.car->type != TSYMBOL || (*list)->obval.cell.cdr->type != TCELL)
        error("Malformed defun");
    *sym = (*list)->obval.cell.car, *rest = (*list)->obval.cell.cdr;
    *fn = handle_function(root, env, rest, type);
    add_variable(root, env, sym, fn);
    return *fn;
}

/* (defun <symbol> (<symbol> ...) expr ...) */
static Obj *prim_defun(void *root, Obj **env, Obj **list) {
    return handle_defun(root, env, list, TFUNCTION);
}

/* (define <symbol> expr) */
static Obj *prim_define(void *root, Obj **env, Obj **list) {
    DEFINE2(sym, value);
    if (length(*list) != 2 || (*list)->obval.cell.car->type != TSYMBOL)
        error("Malformed define");
    *sym = (*list)->obval.cell.car, *value = (*list)->obval.cell.cdr->obval.cell.car;
    *value = eval(root, env, value);
    add_variable(root, env, sym, value);
    return *value;
}

/* (defmacro <symbol> (<symbol> ...) expr ...) */
static Obj *prim_defmacro(void *root, Obj **env, Obj **list) {
    return handle_defun(root, env, list, TMACRO);
}

/* (macroexpand expr) */
static Obj *prim_macroexpand(void *root, Obj **env, Obj **list) {
    if (length(*list) == 1) {
        DEFINE1(body);
        *body = (*list)->obval.cell.car;
        return macroexpand(root, env, body);
    }
    error("Malformed macroexpand");
}

/* (println expr) */
static Obj *prim_println(void *root, Obj **env, Obj **list) {
    DEFINE1(tmp);
    *tmp = (*list)->obval.cell.car;
    print(eval(root, env, tmp));
    printf("\n");
    return &Nil;
}

/* (if expr expr expr ...) */
static Obj *prim_if(void *root, Obj **env, Obj **list) {
    DEFINE3(cond, then, els);
    if (length(*list) < 2) error("Malformed if");
    *cond = (*list)->obval.cell.car;
    *cond = eval(root, env, cond);
    if (*cond != &Nil) {
        *then = (*list)->obval.cell.cdr->obval.cell.car;
        return eval(root, env, then);
    }
    *els = (*list)->obval.cell.cdr->obval.cell.cdr;
    return *els == &Nil ? &Nil : progn(root, env, els);
}

/* (= <integer> <integer>) */
static Obj *prim_num_eq(void *root, Obj **env, Obj **list) {
    Obj *values, *x, *y;
    if (length(*list) != 2) error("Malformed =");
    values = eval_list(root, env, list);
    x = values->obval.cell.car, y = values->obval.cell.cdr->obval.cell.car;
    if (x->type != TINT || y->type != TINT)
        error("= only takes numbers");
    return x->obval.value == y->obval.value ? &True : &Nil;
}

/* (eq expr expr) */
static Obj *prim_eq(void *root, Obj **env, Obj **list) {
    Obj *values;
    if (length(*list) != 2) error("Malformed eq");
    values = eval_list(root, env, list);
    return values->obval.cell.car == values->obval.cell.cdr->obval.cell.car ? &True : &Nil;
}

/* (exit) */
static Obj *prim_exit(void *root, Obj **env, Obj **list) { exit(0); }

static void add_primitive(void *root, Obj **env, char *name, Primitive *fn) {
    DEFINE2(sym, prim);
    *sym = intern(root, name);
    *prim = make_primitive(root, fn);
    add_variable(root, env, sym, prim);
}

static void define_constants(void *root, Obj **env) {
    Obj *PTrue = &True;
    DEFINE1(sym);
    *sym = intern(root, "t");
    add_variable(root, env, sym, &PTrue);
}

static void define_primitives(void *root, Obj **env) {
    add_primitive(root, env, "quote", prim_quote);
    add_primitive(root, env, "cons", prim_cons);
    add_primitive(root, env, "car", prim_car);
    add_primitive(root, env, "cdr", prim_cdr);
    add_primitive(root, env, "setq", prim_setq);
    add_primitive(root, env, "setcar", prim_setcar);
    add_primitive(root, env, "while", prim_while);
    add_primitive(root, env, "gensym", prim_gensym);
    add_primitive(root, env, "+", prim_plus);
    add_primitive(root, env, "-", prim_minus);
    add_primitive(root, env, "*", prim_mult);
    add_primitive(root, env, "/", prim_div);
    add_primitive(root, env, "<", prim_lt);
    add_primitive(root, env, "define", prim_define);
    add_primitive(root, env, "defun", prim_defun);
    add_primitive(root, env, "defmacro", prim_defmacro);
    add_primitive(root, env, "macroexpand", prim_macroexpand);
    add_primitive(root, env, "lambda", prim_lambda);
    add_primitive(root, env, "if", prim_if);
    add_primitive(root, env, "=", prim_num_eq);
    add_primitive(root, env, "eq", prim_eq);
    add_primitive(root, env, "println", prim_println);
    add_primitive(root, env, "exit", prim_exit);
}

/*====================================================================**
** Entry point
**====================================================================*/

/* Returns true if the environment variable is defined and not the empty string. */
static char getEnvFlag(char *name) {
    char *val = getenv(name);
    return val && val[0];
}

/* Free allocated garbage collection memory at exit. */
static void free_all(void) {
    free(memory);
    if(from_space) free(from_space);
}

int main(void) {
    /* Variable declarations */
    void *root = NULL;
    Obj *PNil = &Nil;
    DEFINE2(env, expr);

    /* Debug flags */
    debug_gc = getEnvFlag("MINILISP_DEBUG_GC");
    always_gc = getEnvFlag("MINILISP_ALWAYS_GC");

    /* Call free_all on exit */
    atexit(free_all);

    /* Memory allocation */
    memory = alloc_semispace();

    /* Constants and primitives */
    Symbols = &Nil;
    *env = make_env(root, &PNil, &PNil);
    define_constants(root, env);
    define_primitives(root, env);

    /* The main loop */
    for (;;) {
        *expr = read_expr(root);
        if (!*expr) return 0;
        if (*expr == &Cparen)
            error("Stray close parenthesis");
        if (*expr == &Dot)
            error("Stray dot");
        print(eval(root, env, expr));
        printf("\n");
    }
}
