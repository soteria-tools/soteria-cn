// Three trivial functions used to exercise the `verify -f/--function` flag.

unsigned int one(void)
/*@ ensures return == 1u32; @*/
{
  return 1;
}

unsigned int two(void)
/*@ ensures return == 2u32; @*/
{
  return 2;
}

unsigned int three(void)
/*@ ensures return == 3u32; @*/
{
  return 3;
}
