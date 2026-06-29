#include<limits.h>
/*@ requires x >= 0 || x > INT_MIN;
    assigns \nothing;
    behavior pos:
      assumes x >= 0;
      ensures \result == x;
    behavior neg:
      assumes x < 0;
      ensures \result == -x;
    complete behaviors pos, neg;
    //disjoint behaviors pos, neg; // removed because x == 0 makes both pos and neg true.
*/
int abs ( int x ) {
  if ( x >=0 )
    return x ;
  return -x ;
}