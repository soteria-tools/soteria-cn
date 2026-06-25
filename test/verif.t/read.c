// Extracted from the CN tutorial — see THIRD_PARTY for license.

unsigned int read (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
            return == P;
            P_post == P;
@*/
{
  return *p;
}

unsigned int read_leak(unsigned int *p)
/*@
  requires take P = RW<unsigned int>(p);
@*/
{
  return *p;
}

unsigned int read_invalid(unsigned int *p)
/* no spec */
{
  return *p;
}
