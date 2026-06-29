#include <stdio.h>
#include <stdlib.h>

int n, at, x;
int t[1000];

//@ predicate ord{L}(int direc_var) = \forall integer i; 0 <= i <= n-2 ==> (direc_var ? t[i] < t[i+1] : t[i] > t[i+1]);
//@ predicate noin{L} = \forall integer i; 0 <= i < n ==> t[i] != x;

/*@
  axiomatic zalozenia_zadania {
    axiom n_in_range{L}: 2 <= n <= 1000;
    axiom all_in_range{L}:
      \forall integer i; 0 <= i < n ==> -100000 <= t[i] <= 100000;
    axiom x_in_range{L}: -100000 <= x <= 100000;
    axiom strong_order_one_way_or_another{L}:
      ord((int)0) || ord((int)1);
  }
 */

/*@
  assigns at;
  ensures at==-1 && noin || t[at]==x;
 */
void bins() {
  int from = 0;
  int to = n-1;
  //@ assert from<to;
  int direc = t[0]<=t[1];
  //@ assert ord(direc);
  /*@
    loop assigns at, to, from;
    loop invariant from<=to;
    loop invariant from==to && at==-1 && noin ||
      at==from-1 && (direc? t[at]<x : t[at]>x) ||
      at==to+1 && (direc? t[at]>x : t[at]<x) ||
      from <= at && at <= to;
    loop variant to-from;
  */
  while(1) {
    //@ assert from>=0;
    //@ assert from<to;
    at = (from+to)/2;
    //@ assert from <= at && at <= to;
    //@ assert to==from+1 ==> at==from && at==to-1;
    //@ assert to==from+2 ==> at==from+1 && at==to-1;
    if(direc? t[at]<x : t[at]>x) {
      //nope: @ assert from < at;
      //@ ghost int old_to = to;
      to = at-1;
      //@ assert old_to > to;
      //@ assert from <= to;
    } else if(direc? t[at]>x : t[at]<x) {
      //@ assert at < to;
      //@ ghost int old_from = from;
      from = at+1;
      //@ assert from > old_from;
      //@ assert from <= to;
    } else {
      //@ assert t[at]==x;
      break;
    }
    if(from==to) {
      //@ assert t[from]!=x;
      //@ assert noin;
      at = -1;
      break;
    }
  }
}

int main() {
  scanf("%d", &n);
  for(int i=0;i<n;i++)
    scanf("%d", &t[i]);
  scanf("%d", &x);
  bins();
  printf("%d\n", at);
  return 0;
}
