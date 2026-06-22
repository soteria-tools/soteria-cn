#include <stdlib.h>
#define LOOP_COUNT 100

void add(int* x, int y) {
  *x += y;
}

int main() {
int* x = (int*) malloc(sizeof(int));
  *x = 0;
  for (int y = 0; y < LOOP_COUNT; y++) {
    add(x, y);
  }
  return *x;
}