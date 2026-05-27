#include <stdint.h>

// Filter check, auto simplify

/*@ 
    requires (*x == *y && *y == 3) || (\false && \true);
    ensures \true ==> ~\old(*x) == ~3;
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