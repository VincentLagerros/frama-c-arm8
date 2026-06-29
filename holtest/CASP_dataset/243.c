#include <limits.h>

int e;

/*@ requires
    INT_MIN / 4 <= x <= INT_MAX / 4;
  ensures
    \result == 4 * x && e == 4 * x;
  assigns e;
*/
int f(int x) {
  int y = 4 * x;
  e = y;
  return y;
}

int main() {
  f(42);
  return 0;
}