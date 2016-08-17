#include <stdio.h>
#include "universe.h"

int read_life105(FILE *f, 
                 void (*cb)(void *, char, int, int, int, char), 
                 void (*paramcb)(void *, const char *, const char *),
                 void *cbdata);

void write_life105(FILE *f, generation *g);
void write_life105_text(FILE *f, generation *g);

universe *read_text(const char *filename);
