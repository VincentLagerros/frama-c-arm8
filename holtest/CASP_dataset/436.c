#include <limits.h>
/*@
requires
    0 < x0 && x0 < 100 &&
    0 < x1 && x1 < 100 &&
    \valid(x2 + (0..(x0 * x1) - 1)) &&
    (\forall integer i; 0 <= i < (x0 * x1) ==> 0 <= x2[i] < 256);
assigns x2[0..(x0*x1)-1];
ensures \forall integer i; 0 <= i < (x0 * x1) ==> x2[i] == 7;
*/
void p(int  x0, int  x1, int  * x2) {
  /*@
  loop invariant 0<=x5<=x0;
  loop invariant (\forall integer i; 0 <= i < (x5 * x1) ==> x2[i] == 7);
  loop invariant (\forall integer i; (x5 * x1) <= i < (x0 * x1) ==> 0 <= x2[i] < 256);
  loop assigns x5, x2[0..(x0*x1)-1];
  loop variant x0-x5;
  */
  for(int x5=0; x5 < x0; x5++) {
    int x11 = x5 * x1;
    /*@
    loop invariant 0<=x13<=x1;
    loop invariant (x11==(x5*x1));
    loop invariant (\forall integer i; 0 <= i < (x5 * x1 + x13) ==> x2[i] == 7);
    loop invariant (\forall integer i; (x5 * x1 + x13) <= i < (x0 * x1) ==> (0 <= x2[i] < 256 || x2[i] == 7));
    loop assigns x13, x2[0..(x0*x1)-1];
    loop variant x1-x13;
    */
    for(int x13=0; x13 < x1; x13++) {
      int x42 = x11 + x13;
      int x43 = x2[x42];
      x2[x42] = 7;
      //@ assert x2[x42] == 7;
    }
  }
}
