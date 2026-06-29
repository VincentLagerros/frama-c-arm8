#include<limits.h>

/*@ requires 0 < length <= INT_MAX && \valid_read(arr+(0..length-1));
    requires \forall integer i,j; 0 <= i < j < length ==> arr[i] <= arr[j];
    assigns \nothing;
    ensures -1 <= \result < length &&
      (\result == -1 ==> (\forall integer i; 0 <= i < length ==> arr[i] != query)) &&
      (\result >= 0 ==>  arr[\result] == query) ;
*/
int binary_search(int* arr, int length, int query) {
  int low = 0;
  int high = length - 1;
  /*@
    loop invariant 0 <= low <= high+1 <= length;
    loop invariant \forall integer i; 0 <= i < low ==> arr[i] < query;
    loop invariant \forall integer i; high < i < length ==> arr[i] > query;
    loop assigns low, high;
    loop variant high - low;
  */
  while (low <= high) {
    int mean = low + (high -low) / 2;
    //@ assert low <= mean <= high;
    if (arr[mean] == query) return mean;
    if (arr[mean] < query) low = mean + 1;
    else high = mean - 1;
  }
  return -1;
}
