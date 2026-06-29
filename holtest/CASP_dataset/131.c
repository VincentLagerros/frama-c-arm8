#include <limits.h>

/*@ requires x > INT_MIN;
    assigns \nothing;

  behavior positive:
    assumes x >= 0;
    ensures \result == x;
  
  behavior negative:
    assumes x < 0;
    ensures \result == -x;

  complete behaviors;
  disjoint behaviors;
*/

int abs(int x) {
  
  if (x < 0)
    return -x;
  else if(x >= 0)
    return x;

  return 0;
}
