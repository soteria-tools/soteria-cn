#include <stdlib.h>

typedef struct ln {
  int data;
  struct ln* next;
} SLL;

/* Allocating functions return 0 on success and 1 on allocation failure,
   handing back their result through an out-parameter. */

int listAppend(SLL* x, int v, SLL** out) {
  if (x == NULL) {
    SLL* el = malloc(sizeof(SLL));
    if (el == NULL) return 1;
    el->data = v;
    el->next = NULL;
    *out = el;
    return 0;
  } else {
    SLL* tailp;
    int err = listAppend(x->next, v, &tailp);
    if (err) return err;
    x->next = tailp;
    *out = x;
    return 0;
  };
}

int listPrepend(SLL* x, int v, SLL** out) {
  SLL* new_node = malloc(sizeof(SLL));
  if (new_node == NULL) return 1;
  new_node->data = v;
  new_node->next = x;
  *out = new_node;
  return 0;
}

int listLength(SLL* x) {
  if (x == NULL) {
    return 0;
  } else {
    return 1 + listLength(x->next);
  };
}

int listCopy(SLL* x, SLL** out) {
  if (x == NULL) {
    *out = NULL;
    return 0;
  } else {
    SLL* t;
    int err = listCopy(x->next, &t);
    if (err) return err;
    SLL* r = malloc(sizeof(SLL));
    if (r == NULL) return 1;
    r->data = x->data;
    r->next = t;
    *out = r;
    return 0;
  };
}

/* Pure pointer rearrangement: never allocates, so it cannot fail. */
SLL* listConcat(SLL* x, SLL* y) {
  if (x == NULL) {
    return y;
  } else {
    x->next = listConcat(x->next, y);
    return x;
  };
}

int sum(SLL* x) {
  if (x == NULL) {
    return 0;
  } else {
    return x->data + sum(x->next);
  }
}

int main() {
  SLL* x = NULL;
  if (listAppend(x, 2, &x)) return 0;
  if (listPrepend(x, 1, &x)) return 0;
  SLL* y;
  if (listCopy(x, &y)) return 0;
  x = listConcat(x, y);
  return !((sum(x) == 6) && (listLength(x) == 4)); /* returns 0 */
}
