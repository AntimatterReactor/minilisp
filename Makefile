CFLAGS=-std=c89 -march=native -O3 -Wall

.PHONY: clean test

minilisp: minilisp.c

clean:
	rm -f minilisp *~

test: minilisp
	@./test.sh
