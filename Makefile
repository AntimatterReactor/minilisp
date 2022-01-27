CFLAGS=-std=c89 -O3 -Wall

.PHONY: clean test

minilisp: minilisp.c

clean:
	rm -f minilisp *~

test: minilisp
	@./test.sh
