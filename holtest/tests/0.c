#include <stdint.h>

// Weird testcase for many random operations

/*@ 
    requires (*x == *y && *y == 3) ^^ (*x == *y) || \valid(x) && \aligned(x,8) || !\valid(y) && \let x=\true; x;
    ensures (*y==*x ==> ~\old(*x) == ~3) || (\let w = *x; (w & 0x1337) == 0) || (1/2 == *y) || (3*3 == *y);
*/ 
void swap(uint64_t* x, uint64_t* y) {
  uint64_t a, b;
  a = * x;
  b = * y;
  if (a == b)
    return;
  * x = b;
  * y = a;
}