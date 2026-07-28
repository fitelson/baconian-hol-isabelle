CC ?= cc
CFLAGS ?= -O3 -DNDEBUG -std=c11 -Wall -Wextra -Wpedantic

all: finite_core_size4 finite_core_context1

finite_core_size4: finite_core_size4.c
	$(CC) $(CFLAGS) -o $@ $<

finite_core_context1: finite_core_context1.c
	$(CC) $(CFLAGS) -o $@ $<

clean:
	rm -f finite_core_size4 finite_core_context1
