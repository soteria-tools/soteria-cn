#include <stdlib.h>

struct dllist {
  int data;
  struct dllist* prev;
  struct dllist* next;
};

typedef struct dllist* DLL;

/*@
// A doubly-linked list segment starting at [p], whose first node (if any) is
// expected to have its [prev] field pointing back at [prev]. The recursion
// threads the current node down as the [prev] of the next one, so every
// node's back-pointer is pinned. Returns the length of the segment.
predicate [rec] (u32) DLL_At(pointer p, pointer prev) {
  if (is_null(p)) {
    return 0u32;
  } else {
    take H = RW<struct dllist>(p);
    assert (ptr_eq(H.prev, prev));
    take L = DLL_At(H.next, p);
    return (1u32 + L);
  }
}

// A whole list stored at [p]: the head's [prev] is NULL.
predicate (u32) DLList(pointer p) {
  take P = RW<DLL>(p);
  take L = DLL_At(P, NULL);
  return L;
}
@*/

extern struct dllist *malloc_dll_node ();
/*@ spec malloc_dll_node();
    ensures take P = W<struct dllist>(return);
@*/

extern struct dllist *free_dll_node (struct dllist *node);
/*@ spec free_dll_node(pointer node);
    requires take P = RW<struct dllist>(node);
    ensures true;
@*/


DLL empty_list()
/*@
  ensures take P = DLL_At(return, NULL);
          P == 0u32;
@*/
{
  return NULL;
}

// Insert a fresh node at the front of the list. The old head (if it exists)
// gets its back-pointer redirected at the new node.
void prepend(int head, DLL* list)
/*@
  requires take L = DLList(list);
  ensures  take L_post = DLList(list);
           L_post == (1u32 + L);
@*/
{
  DLL new_node = malloc_dll_node();
  new_node->data = head;
  new_node->prev = NULL;
  new_node->next = *list;
  if ( *list != NULL ) {
    (*list)->prev = new_node;
  }
  *list = new_node;
}

// Free a segment whose first node points back at [prev]. We can't recurse
// through DLList here: the [next] node's [prev] points at the *current* node,
// not at NULL, so we have to thread the expected back-pointer down by hand.
void free_at(struct dllist* p, struct dllist* prev)
/*@ requires take L = DLL_At(p, prev);
    ensures  true;
@*/
{
  if ( p != NULL ) {
    struct dllist* next = p->next; // save the next value
    free_dll_node(p);              // free the head node
    free_at(next, p);              // continue
  }
}

// Free the whole list, head first, walking via [next].
void free_dll(DLL* list)
/*@
  requires take P = DLList(list);
  ensures  take P_post = DLList(list);
           P_post == 0u32;
@*/
{
  free_at(*list, NULL);
  *list = NULL;
}

// Helper that copies the segment [src] (whose first node points back at
// [oldprev]) into a brand new segment whose first node points back at
// [newprev]. The original segment is left untouched. We build the new
// back-pointers on the way *down* (each node knows its own [newprev]),
// which is what makes the doubly-linked copy go through.
struct dllist* copy_at(struct dllist* src, struct dllist* oldprev,
                       struct dllist* newprev)
/*@ requires take L = DLL_At(src, oldprev);
    ensures  take L_post = DLL_At(src, oldprev);
             take Out = DLL_At(return, newprev);
             L == L_post;
             L == Out;
@*/
{
  if (src == NULL) {
    return NULL;
  }

  struct dllist* new_node = malloc_dll_node();
  new_node->data = src->data;
  new_node->prev = newprev;

  struct dllist* copied_tail = copy_at(src->next, src, new_node);
  new_node->next = copied_tail;

  return new_node;
}

void dllcopy (DLL* l, DLL* out)
/*@ requires take L = DLList(l);
             take N = W<DLL>(out);
    ensures  take L_post = DLList(l);
             take Out = DLList(out);
             L == L_post;
             L == Out;
@*/
{
  *out = copy_at(*l, NULL, NULL);
}

// Length of a segment whose first node points back at [prev]. As with
// [free_at], the back-pointer has to be threaded down explicitly.
unsigned int length_at (struct dllist* p, struct dllist* prev)
/*@ requires take L = DLL_At(p, prev);
    ensures take L_post = DLL_At(p, prev);
            L == L_post;
            return == L;
@*/
{
  if (p == 0) {
    return 0;
  } else {
    return 1 + length_at(p->next, p);
  }
}

unsigned int length (DLL* l)
/*@ requires take L = DLList(l);
    ensures take L_post = DLList(l);
            L == L_post;
            return == L;
@*/
{
  return length_at(*l, NULL);
}

// ----------------------------------------------------------------------------
// Tests: build lists from scratch into caller-provided slots, run a sequence
// of operations, check properties about their lengths, then free everything.
// ----------------------------------------------------------------------------

// Create a list, prepend three elements, and check that its length is 3.
void test1 (DLL* slot)
/*@ requires take Pre  = W<DLL>(slot);
    ensures  take Post = DLList(slot);
             Post == 0u32;
@*/
{
  *slot = empty_list();
  prepend(1, slot);
  prepend(2, slot);
  prepend(3, slot);

  unsigned int n = length(slot);
  /*@ assert (n == 3u32); @*/

  free_dll(slot);
}

// Create a list, copy it with dllcopy, and check that the copy has the same
// length as the original (both 3) while the original is preserved.
void test2 (DLL* a, DLL* c)
/*@ requires take Pa = W<DLL>(a);
             take Pc = W<DLL>(c);
    ensures  take Qa = DLList(a);
             take Qc = DLList(c);
             Qa == 0u32;
             Qc == 0u32;
@*/
{
  *a = empty_list();
  prepend(10, a);
  prepend(20, a);
  prepend(30, a);         // a has length 3

  dllcopy(a, c);          // c is a copy of a (length 3), a is preserved

  unsigned int na = length(a);
  unsigned int nc = length(c);
  /*@ assert (na == 3u32); @*/
  /*@ assert (nc == 3u32); @*/
  /*@ assert (na == nc); @*/

  free_dll(a);
  free_dll(c);
}

// A long test exercising ~60 operations across 6 different lists: build four
// of them, copy two into the remaining slots, then grow everything with lots
// of prepends, checking the running length at every stage before freeing all
// six. (There is no append for these lists, so growth is all prepend/copy.)
void test3 (DLL* a, DLL* b, DLL* c, DLL* d, DLL* e, DLL* f)
/*@ requires take Pa = W<DLL>(a);
             take Pb = W<DLL>(b);
             take Pc = W<DLL>(c);
             take Pd = W<DLL>(d);
             take Pe = W<DLL>(e);
             take Pf = W<DLL>(f);
    ensures  take Qa = DLList(a);
             take Qb = DLList(b);
             take Qc = DLList(c);
             take Qd = DLList(d);
             take Qe = DLList(e);
             take Qf = DLList(f);
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
  dllcopy(a, d);                  // (23) d: 4, a preserved 4
  unsigned int ld = length(d);    // (24)
  unsigned int la2 = length(a);   // (25)
  /*@ assert (ld == 4u32); @*/
  /*@ assert (la2 == 4u32); @*/

  dllcopy(f, e);                  // (26) e: 5, f preserved 5
  unsigned int le = length(e);    // (27)
  unsigned int lf2 = length(f);   // (28)
  /*@ assert (le == 5u32); @*/
  /*@ assert (lf2 == 5u32); @*/

  // --- Grow a with three more prepends ---
  prepend(15, a);                 // (29) a: 5
  prepend(16, a);                 // (30) a: 6
  prepend(17, a);                 // (31) a: 7
  unsigned int s1 = length(a);    // (32)
  /*@ assert (s1 == 7u32); @*/

  // --- Grow b with two more prepends ---
  prepend(20, b);                 // (33) b: 4
  prepend(21, b);                 // (34) b: 5
  unsigned int s2 = length(b);    // (35)
  /*@ assert (s2 == 5u32); @*/

  // --- Grow c with two more prepends ---
  prepend(8, c);                  // (36) c: 3
  prepend(9, c);                  // (37) c: 4
  unsigned int s3 = length(c);    // (38)
  /*@ assert (s3 == 4u32); @*/

  // --- Grow the copy d with two more prepends ---
  prepend(30, d);                 // (39) d: 5
  prepend(31, d);                 // (40) d: 6
  unsigned int s4 = length(d);    // (41)
  /*@ assert (s4 == 6u32); @*/

  // --- Grow the copy e with three more prepends ---
  prepend(40, e);                 // (42) e: 6
  prepend(41, e);                 // (43) e: 7
  prepend(42, e);                 // (44) e: 8
  unsigned int s5 = length(e);    // (45)
  /*@ assert (s5 == 8u32); @*/

  // --- Grow f with two more prepends ---
  prepend(50, f);                 // (46) f: 6
  prepend(51, f);                 // (47) f: 7
  unsigned int s6 = length(f);    // (48)
  /*@ assert (s6 == 7u32); @*/

  // --- Two final prepends onto a ---
  prepend(60, a);                 // (49) a: 8
  prepend(61, a);                 // (50) a: 9
  unsigned int s7 = length(a);    // (51)
  /*@ assert (s7 == 9u32); @*/

  // --- Re-check every list's length one last time ---
  unsigned int ra = length(a);    // (52)
  unsigned int rb = length(b);    // (53)
  unsigned int rc = length(c);    // (54)
  unsigned int rd = length(d);    // (55)
  unsigned int re = length(e);    // (56)
  unsigned int rf = length(f);    // (57)
  /*@ assert (ra == 9u32); @*/
  /*@ assert (rb == 5u32); @*/
  /*@ assert (rc == 4u32); @*/
  /*@ assert (rd == 6u32); @*/
  /*@ assert (re == 8u32); @*/
  /*@ assert (rf == 7u32); @*/

  // --- Free all six lists ---
  free_dll(a);                    // (58) a: 0
  free_dll(b);                    // (59) b: 0
  free_dll(c);                    // (60) c: 0
  free_dll(d);                    // (61) d: 0
  free_dll(e);                    // (62) e: 0
  free_dll(f);                    // (63) f: 0
}
