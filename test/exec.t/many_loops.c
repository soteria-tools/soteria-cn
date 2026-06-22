#include <stdlib.h>

void add(int* x, int y) {
  *x += y;
}

int main() {
  int* x = (int*) malloc(sizeof(int));
  *x = 0;
  for (int y = 0; y < 1000; y++) {
    add(x, y);
  }
}