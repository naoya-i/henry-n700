
OBJS=src/algorithm.o src/function.o src/ilp.o src/knowledge_base.o

CC=g++
LDFLAGS=-lpython2.7 -lsqlite3 -lpcre -lpcrecpp -lcdb

ifneq ($(shell grep -E '^\#define USE_OMP' src/defs.h),)
LDFLAGS+=-fopenmp
CFLAGS+=-fopenmp
endif

ifneq ($(shell grep -E '^\#define USE_GUROBI' src/defs.h),)
LDFLAGS+=-lgurobi_c++ -lgurobi55 -lpthread
endif

ifneq ($(shell grep -E '^\#define USE_LOCALSOLVER' src/defs.h),)
CFLAGS+=-I/opt/localsolver_3_0/include
LDFLAGS+=-llocalsolver
endif

ifneq ($(shell grep -E '^\#define USE_LPSOLVE' src/defs.h),)
LDFLAGS+=-llpsolve55
endif

%.o: %.cpp
	$(CC) $(CFLAGS) $(OPTIONS) -c $< -o $@

all: $(OBJS)
	mkdir -p ./bin
	$(CC) $(CFLAGS) $(OBJS) $(LDFLAGS) $(OPTIONS) -o ./bin/henry
