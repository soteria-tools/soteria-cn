// Extracted from the CN tutorial — see THIRD_PARTY for license.

void incr_unsigned (unsigned int *p)
/*@ requires take P = RW<unsigned int>(p);
    ensures take P_post = RW<unsigned int>(p);
            P_post == P + 1u32;
@*/
{
  unsigned int n = *p;
  unsigned int m = n + 1;
  *p = m;
}

void incr_signed_no_ovf (int *p)
/*@ requires take P = RW<int>(p); P <= 2147483646i32;
    ensures take P_post = RW<int>(p);
            P_post == P + 1i32;
@*/
{
  int n = *p;
  int m = n + 1;
  *p = m;
}

void incr_signed_ovf (int *p)
/*@ requires take P = RW<int>(p);
    ensures take P_post = RW<int>(p);
            P_post == P + 1i32;
@*/
{
  int n = *p;
  int m = n + 1;
  *p = m;
}