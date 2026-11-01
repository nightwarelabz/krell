CC      ?= cc
CFLAGS  ?= -O2 -std=c11 -Wall -Wextra -Werror
SRC      = src/ir.c src/binary.c src/print.c src/verify.c src/cost.c src/interp.c \
           src/opt.c src/be.c src/be_x86.c src/be_arm64.c src/be_rv64.c src/be_llvm.c src/surface.c
OBJ      = $(SRC:.c=.o)
LIB      = libkrell.a

all: $(LIB) krellc

$(LIB): $(OBJ)
	ar rcs $@ $(OBJ)

krellc: src/main.o $(LIB)
	$(CC) $(CFLAGS) -o $@ src/main.o $(LIB) -lm

src/%.o: src/%.c src/krell.h
	$(CC) $(CFLAGS) -Isrc -c $< -o $@

tests: $(LIB)
	$(CC) $(CFLAGS) -Isrc -o /tmp/test-kernels tests/kernels.c $(LIB) -lm
	/tmp/test-kernels
	$(CC) $(CFLAGS) -Isrc -o /tmp/test-roundtrip tests/roundtrip.c tests/kernels.c -DKERNELS_NO_MAIN $(LIB) -lm
	/tmp/test-roundtrip

clean:
	rm -f $(OBJ) src/main.o $(LIB) krellc

.PHONY: all tests clean
