#include <stdint.h>

/*@ 
  requires \true;
  ensures (\result == \old(x) || \result == \old(y)) && \old(x) <= \result && \old(y) <= \result;
*/
int64_t max(int64_t x, int64_t y) {
  if (x > y) {
    return x;
  } else {
    return y;
  }
}

int main(void) {
  int64_t a = 5;
  int64_t b = 7;
  return max(a, b);
}
