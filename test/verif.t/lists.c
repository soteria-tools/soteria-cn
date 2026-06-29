#include <stdlib.h>

struct sllist {
  int head;
  struct sllist* tail;
};

typedef struct sllist* SLL;

/*@
predicate [rec] (u32) SLList_At(pointer p) {
  if (is_null(p)) {
    return 0u32;
  } else {
    take H = RW<struct sllist>(p);
    take L = SLList_At(H.tail);
    return (1u32 + L);
  }
}
  
predicate (u32) SLList(pointer p) {
  take P = RW<SLL>(p);
  take L = SLList_At(P);
  return L;
}
@*/

extern struct sllist *malloc_sllist_node ();
/*@ spec malloc_sllist_node();
    ensures take P = W<struct sllist>(return);
@*/

extern struct sllist *free_sllist_node (struct sllist *node);
/*@ spec free_sllist_node(pointer node);
    requires take P = RW<struct sllist>(node);
    ensures true;
@*/


SLL empty_list()
/*@
  ensures take P = SLList_At(return);
          P == 0u32;
@*/
{
  return NULL;
}

void prepend(int head, SLL* list)
/*@
  requires take L = SLList(list);
  ensures  take L_post = SLList(list);
           L_post == (1u32 + L);
@*/
{
  SLL new_node = malloc_sllist_node();
  new_node->head = head;
  new_node->tail = *list;
  *list = new_node;
}

void free_list(SLL* list)
/*@
  requires take P = SLList(list);
  ensures  take P_post = SLList(list);
           P_post == 0u32;
@*/
{
  if ( *list != NULL ) {
    SLL tail = (*list)->tail; // save the tail value
    free_sllist_node(*list);  // free the head node
    *list = tail;             // advance the list pointer to the tail
    free_list(list);          // continue
  }
}

void slcopy (SLL* l, SLL* out)
/*@ requires take L = SLList(l);
             take N = W<SLL>(out); 
    ensures  take L_post = SLList(l);
             take Out = SLList(out);
             L == L_post;
             L == Out;
@*/
{
  SLL src = *l;

  if (src == NULL) {
    *out = empty_list();
    return;
  }

  SLL copied_tail;
  slcopy(&(src->tail), &copied_tail);

  SLL copied_node = malloc_sllist_node();
  copied_node->head = src->head;
  copied_node->tail = copied_tail;
  *out = copied_node;
}

void slappend(SLL* xs, SLL* ys)
/*@ requires take L1 = SLList(xs);
             take L2 = SLList(ys); 
    ensures  take L1_post = SLList(xs);
             take L2_post = SLList(ys);
             L1_post == (L1 + L2);
             L2_post == 0u32;  @*/
{
  if (*xs == NULL) {
    *xs = *ys;
    *ys = NULL;
  } else {
    slappend(&((*xs)->tail), ys);
  }
}

unsigned int length (SLL* l)
/*@ requires take L = SLList(l);
    ensures take L_post = SLList(l);
            L == L_post;
            return == L;
@*/
{
  if (*l == 0) {
    return 0;
  } else {
    return 1 + length(&(*l)->tail);
  }
}

// ----------------------------------------------------------------------------
// Tests: build lists from scratch into caller-provided slots, run a sequence
// of operations, check properties about their lengths, then free everything.
// The (now empty) lists are handed back through the postcondition.
// ----------------------------------------------------------------------------

// Create a list, prepend three elements, and check that its length is 3.
void test1 (SLL* slot)
/*@ requires take Pre  = W<SLL>(slot);
    ensures  take Post = SLList(slot);
             Post == 0u32;
@*/
{
  *slot = empty_list();
  prepend(1, slot);
  prepend(2, slot);
  prepend(3, slot);

  unsigned int n = length(slot);
  /*@ assert (n == 3u32); @*/

  free_list(slot);
}

// Create two lists, concatenate them with slappend, and check that the
// resulting length is the sum of the two original lengths (2 + 3 == 5).
void test2 (SLL* a, SLL* b)
/*@ requires take Pa = W<SLL>(a);
             take Pb = W<SLL>(b);
    ensures  take Qa = SLList(a);
             take Qb = SLList(b);
             Qa == 0u32;
             Qb == 0u32;
@*/
{
  *a = empty_list();
  prepend(1, a);
  prepend(2, a);          // a has length 2

  *b = empty_list();
  prepend(3, b);
  prepend(4, b);
  prepend(5, b);          // b has length 3

  slappend(a, b);         // a has length 5, b is now empty

  unsigned int n = length(a);
  /*@ assert (n == 5u32); @*/

  free_list(a);           // b is already empty after slappend
}

// Create a list, copy it with slcopy, and check that the copy has the same
// length as the original (both 3) while the original is preserved.
void test3 (SLL* a, SLL* c)
/*@ requires take Pa = W<SLL>(a);
             take Pc = W<SLL>(c);
    ensures  take Qa = SLList(a);
             take Qc = SLList(c);
             Qa == 0u32;
             Qc == 0u32;
@*/
{
  *a = empty_list();
  prepend(10, a);
  prepend(20, a);
  prepend(30, a);         // a has length 3

  slcopy(a, c);           // c is a copy of a (length 3), a is preserved

  unsigned int na = length(a);
  unsigned int nc = length(c);
  /*@ assert (na == 3u32); @*/
  /*@ assert (nc == 3u32); @*/
  /*@ assert (na == nc); @*/

  free_list(a);
  free_list(c);
}

// A long test exercising ~25 operations: build two lists, copy one, append
// them together, prepend some more, and check the running length at each
// stage before freeing everything.
void test4 (SLL* a, SLL* b, SLL* c)
/*@ requires take Pa = W<SLL>(a);
             take Pb = W<SLL>(b);
             take Pc = W<SLL>(c);
    ensures  take Qa = SLList(a);
             take Qb = SLList(b);
             take Qc = SLList(c);
             Qa == 0u32;
             Qb == 0u32;
             Qc == 0u32;
@*/
{
  *a = empty_list();              // (1)
  prepend(1, a);                  // (2)  a: 1
  prepend(2, a);                  // (3)  a: 2
  prepend(3, a);                  // (4)  a: 3
  prepend(4, a);                  // (5)  a: 4
  unsigned int n1 = length(a);    // (6)
  /*@ assert (n1 == 4u32); @*/

  *b = empty_list();              // (7)
  prepend(5, b);                  // (8)  b: 1
  prepend(6, b);                  // (9)  b: 2
  prepend(7, b);                  // (10) b: 3
  unsigned int n2 = length(b);    // (11)
  /*@ assert (n2 == 3u32); @*/

  slcopy(a, c);                   // (12) c: copy of a (4), a preserved (4)
  unsigned int n3 = length(c);    // (13)
  unsigned int n4 = length(a);    // (14)
  /*@ assert (n3 == 4u32); @*/
  /*@ assert (n4 == 4u32); @*/

  slappend(a, b);                 // (15) a: 4 + 3 = 7, b: 0
  unsigned int n5 = length(a);    // (16)
  unsigned int n6 = length(b);    // (17)
  /*@ assert (n5 == 7u32); @*/
  /*@ assert (n6 == 0u32); @*/

  slappend(a, c);                 // (18) a: 7 + 4 = 11, c: 0
  unsigned int n7 = length(a);    // (19)
  /*@ assert (n7 == 11u32); @*/

  prepend(8, a);                  // (20) a: 12
  prepend(9, a);                  // (21) a: 13
  unsigned int n8 = length(a);    // (22)
  /*@ assert (n8 == 13u32); @*/

  free_list(a);                   // (23) a: 0
  free_list(b);                   // (24) b: 0
  free_list(c);                   // (25) c: 0
}

// A very long test exercising 60 operations across 6 different lists: build
// four of them, copy two into the remaining slots, fold everything together
// with a chain of appends, prepend some more, rebuild, then free all six.
// The running length is checked at every stage.
void test5 (SLL* a, SLL* b, SLL* c, SLL* d, SLL* e, SLL* f)
/*@ requires take Pa = W<SLL>(a);
             take Pb = W<SLL>(b);
             take Pc = W<SLL>(c);
             take Pd = W<SLL>(d);
             take Pe = W<SLL>(e);
             take Pf = W<SLL>(f);
    ensures  take Qa = SLList(a);
             take Qb = SLList(b);
             take Qc = SLList(c);
             take Qd = SLList(d);
             take Qe = SLList(e);
             take Qf = SLList(f);
             Qa == 0u32;
             Qb == 0u32;
             Qc == 0u32;
             Qd == 0u32;
             Qe == 0u32;
             Qf == 0u32;
@*/
{
  // --- Build a (length 4) ---
  *a = empty_list();              // (1)
  prepend(1, a);                  // (2)  a: 1
  prepend(2, a);                  // (3)  a: 2
  prepend(3, a);                  // (4)  a: 3
  prepend(4, a);                  // (5)  a: 4

  // --- Build b (length 3) ---
  *b = empty_list();              // (6)
  prepend(5, b);                  // (7)  b: 1
  prepend(6, b);                  // (8)  b: 2
  prepend(7, b);                  // (9)  b: 3

  // --- Build c (length 2) ---
  *c = empty_list();              // (10)
  prepend(8, c);                  // (11) c: 1
  prepend(9, c);                  // (12) c: 2

  // --- Build f (length 5) ---
  *f = empty_list();              // (13)
  prepend(10, f);                 // (14) f: 1
  prepend(11, f);                 // (15) f: 2
  prepend(12, f);                 // (16) f: 3
  prepend(13, f);                 // (17) f: 4
  prepend(14, f);                 // (18) f: 5

  // --- Check the freshly built lengths ---
  unsigned int la = length(a);    // (19)
  unsigned int lb = length(b);    // (20)
  unsigned int lc = length(c);    // (21)
  unsigned int lf = length(f);    // (22)
  /*@ assert (la == 4u32); @*/
  /*@ assert (lb == 3u32); @*/
  /*@ assert (lc == 2u32); @*/
  /*@ assert (lf == 5u32); @*/

  // --- Copy a into d and f into e (d, e were still uninitialized) ---
  slcopy(a, d);                   // (23) d: 4, a preserved 4
  unsigned int ld = length(d);    // (24)
  unsigned int la2 = length(a);   // (25)
  /*@ assert (ld == 4u32); @*/
  /*@ assert (la2 == 4u32); @*/

  slcopy(f, e);                   // (26) e: 5, f preserved 5
  unsigned int le = length(e);    // (27)
  unsigned int lf2 = length(f);   // (28)
  /*@ assert (le == 5u32); @*/
  /*@ assert (lf2 == 5u32); @*/

  // --- Fold everything into a with a chain of appends ---
  slappend(a, b);                 // (29) a: 4 + 3 = 7,  b: 0
  unsigned int s1 = length(a);    // (30)
  unsigned int z1 = length(b);    // (31)
  /*@ assert (s1 == 7u32); @*/
  /*@ assert (z1 == 0u32); @*/

  slappend(a, c);                 // (32) a: 7 + 2 = 9,  c: 0
  unsigned int s2 = length(a);    // (33)
  unsigned int z2 = length(c);    // (34)
  /*@ assert (s2 == 9u32); @*/
  /*@ assert (z2 == 0u32); @*/

  slappend(a, d);                 // (35) a: 9 + 4 = 13, d: 0
  unsigned int s3 = length(a);    // (36)
  unsigned int z3 = length(d);    // (37)
  /*@ assert (s3 == 13u32); @*/
  /*@ assert (z3 == 0u32); @*/

  slappend(e, f);                 // (38) e: 5 + 5 = 10, f: 0
  unsigned int s4 = length(e);    // (39)
  unsigned int z4 = length(f);    // (40)
  /*@ assert (s4 == 10u32); @*/
  /*@ assert (z4 == 0u32); @*/

  slappend(a, e);                 // (41) a: 13 + 10 = 23, e: 0
  unsigned int s5 = length(a);    // (42)
  unsigned int z5 = length(e);    // (43)
  /*@ assert (s5 == 23u32); @*/
  /*@ assert (z5 == 0u32); @*/

  // --- Prepend four more onto a ---
  prepend(15, a);                 // (44) a: 24
  prepend(16, a);                 // (45) a: 25
  prepend(17, a);                 // (46) a: 26
  prepend(18, a);                 // (47) a: 27
  unsigned int s6 = length(a);    // (48)
  /*@ assert (s6 == 27u32); @*/

  // --- Rebuild b (it was emptied by the first append) ---
  prepend(19, b);                 // (49) b: 1
  prepend(20, b);                 // (50) b: 2
  prepend(21, b);                 // (51) b: 3
  unsigned int s7 = length(b);    // (52)
  /*@ assert (s7 == 3u32); @*/

  slappend(a, b);                 // (53) a: 27 + 3 = 30, b: 0
  unsigned int s8 = length(a);    // (54)
  /*@ assert (s8 == 30u32); @*/

  // --- Free all six lists ---
  free_list(a);                   // (55) a: 0
  free_list(b);                   // (56) b: 0
  free_list(c);                   // (57) c: 0
  free_list(d);                   // (58) d: 0
  free_list(e);                   // (59) e: 0
  free_list(f);                   // (60) f: 0
}

