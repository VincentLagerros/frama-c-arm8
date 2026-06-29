#include <stdint.h>

/*@ 
    requires (*x == *y && *y == 3) || (\false && \true);
    ensures z == z+1 ==> ~\old(*x) == ~3;
*/ 
void swap(uint64_t* x, uint64_t* y, int z) {
  uint64_t a, b;
  a = * x;
  b = * y;
  if (a == b)
    return;
  * x = b;
  * y = a;
}