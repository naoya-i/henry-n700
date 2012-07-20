
OBJS=src/algorithm.o src/function.o src/scoring.o src/ilp.o

CC=g++
LDFLAGS=-lpython2.7

ifneq ($(shell grep -E '^\#define USE_GUROBI' src/defs.h),)
LDFLAGS+=-lgurobi_c++ -lgurobi50 -lpthread
endif

ifneq ($(shell grep -E '^\#define USE_LOCALSOLVER' src/defs.h),)
CFLAGS+=-I/opt/localsolver_2_0/include
LDFLAGS+=-llocalsolver
endif

%.o: %.cpp
	$(CC) $(CFLAGS) $(OPTIONS) -c $< -o $@

all: $(OBJS)
	mkdir -p ./bin
	$(CC) $(CFLAGS) $(OBJS) $(LDFLAGS) $(OPTIONS) -o ./bin/henry

