#include <stddef.h>
#include <stdio.h>

/*@
  predicate valid_range_rw(int* arr, integer n) =
    n >= 0 && \valid(arr + (0 .. n-1));
  predicate valid_range_r(int* arr, integer n) =
    n >= 0 && \valid_read(arr + (0 .. n-1));
  predicate sorted(int* arr, integer n) =
    \forall integer i, j; 0 <= i <= j < n ==> arr[i] <= arr[j];
  predicate contains(int* arr, integer n, integer elem) =
    \exists integer off; 0 <= off < n && arr[off] == elem;
*/

/*@
  requires valid_range_r(arr, len);
  requires sorted(arr, len);
  assigns \nothing;
  behavior in:
    assumes contains(arr, len, value);
    ensures arr[\result] == value;
    ensures 0 <= \result <= len-1;
  behavior notin:
    assumes !contains(arr, len, value);
    ensures \result == -1;
  disjoint behaviors;
  complete behaviors;
*/
int bsearch(int* arr, int len, int value){
  if(len == 0) return -1 ;
  int low = 0 ;
  int up = len-1 ;
  /*@
    loop invariant 0 <= low && up <= len-1;
    loop invariant \forall integer i; 0 <= i < low ==> arr[i] != value;
    loop invariant \forall integer i; up < i <= len-1 ==> arr[i] != value;
    loop assigns low, up;
    loop variant up - low;
  */
  while(low <= up){
    int mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid-1 ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return -1 ;
}

int main(){
  int i;
  int a[] = {1,2,3,4,5,6,7,8,9,10};
  i = bsearch(a, 10, 3);
  //@ assert i == 2;
  i = bsearch(a, 10, 0);
  //@ assert i == -1;
  //printf("i = %d\n", i);
  return 0;
}
