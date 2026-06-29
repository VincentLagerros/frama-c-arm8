#include "limits.h"

/*@
requires 
 a*x <= INT_MAX
 && a*x+b <= INT_MAX
 && a*x >= INT_MIN
 && a*x+b >= INT_MIN;
ensures \result >= INT_MIN && \result <= INT_MAX && \result == a*x+b;
*/
int f(int a,int b,int x) {
  return a*x+b;
}