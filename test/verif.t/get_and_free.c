// Extracted from the CN tutorial — see THIRD_PARTY for license.
#include "malloc.h"

unsigned int *malloc_and_set (unsigned int x)
/*@
  ensures take P = RW<unsigned int>(return);
            P == x;
@*/
{
  unsigned int *p = malloc__unsigned_int();
  *p = x;
  return p;
}

unsigned int get_and_free (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p);
    ensures return == P;
@*/
{
  unsigned int v = *p;
  free__unsigned_int (p);
  return v;
}

unsigned int tester()
/*@ ensures return == 42u32;
@*/
{
  unsigned int *p = malloc_and_set(42);
  unsigned int v = get_and_free(p);
  return v;
}