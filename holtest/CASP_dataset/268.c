#include "limits.h"

/*@ requires b != 0;
  @ requires !(a == INT_MIN && b == -1);
  @ ensures \result == a/b;
  @ assigns \nothing;
  @*/
int div(int a, int b) {
  return a / b;
}