  $ soteria-cn verify min3.c -v
  Verifying function min3...
  Successfully verified min3
  Verifying function min3_invalid_spec...
  error: `Lfail (((V|1| <=s V|2|) && (V|3| <=s V|1|))) in min3_invalid_spec
      --> min3.c:21:13
   19 |      
   20 | /    unsigned int min3_invalid_spec(unsigned int x, unsigned int y, unsigned int z)
   21 | |    /*@ ensures return <= x
      | | /--------------^
   22 | | |              && return <= y
   23 | | |              && z <= return; // This doesn't hold
      | | \---------------------------^ Could not prove this hold
   24 | |    @*/
      . |    
   34 | |        }
   35 | |    }
      | \----' 1: Verifying function
   36 |      
  error: `Lfail (((V|2| <=s V|1|) && (V|3| <=s V|2|))) in min3_invalid_spec
      --> min3.c:21:13
   19 |      
   20 | /    unsigned int min3_invalid_spec(unsigned int x, unsigned int y, unsigned int z)
   21 | |    /*@ ensures return <= x
      | | /--------------^
   22 | | |              && return <= y
   23 | | |              && z <= return; // This doesn't hold
      | | \---------------------------^ Could not prove this hold
   24 | |    @*/
      . |    
   34 | |        }
   35 | |    }
      | \----' 1: Verifying function
   36 |      
  error: Null pointer dereference in min3_invalid_code
      --> min3.c:47:16
   36 |    
   37 | /  unsigned int min3_invalid_code(unsigned int x, unsigned int y, unsigned int z)
   38 | |  /*@ ensures return <= x
      . |  
   47 | |          return *((unsigned int*) 0);
      | |                 ^^^^^^^^^^^^^^^^^^^^ Invalid memory load
      . |  
   51 | |      }
   52 | |  }
      | \--' 1: Verifying function
   53 |    

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

  $ soteria-cn verify read.c
  Verifying function read...
  Successfully verified read
