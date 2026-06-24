  $ soteria-cn verify min3.c -v
  Verifying function min3...
  Successfully verified min3
  $ soteria-cn verify leak.c -v
  warning: Memory leak in to_verify
      --> leak.c:3:1
    2 |      
    3 |      int to_verify() {
      | /----'
      | | /--^
    4 | | |    int *p = malloc(sizeof(int));
      | | |             ------------------- 2: Memory allocated here leaked
    5 | | |    return 0;
    6 | | |  
      | \-|  ' 1: Verifying function
      |   \--^ Memory leftover after this function
