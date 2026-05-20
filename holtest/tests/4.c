#include <stdint.h>

/*@ 
    requires *x == *y && *y == 3;
    ensures \old(*x) == 3 && \result != 0;
*/ 
int swap(uint64_t* x, uint64_t* y) {
  uint64_t a, b;
  a = * x;
  b = * y;
  if (a == b)
    return 1;
  * x = b;
  * y = a;
  return 0;
}