#include <stdio.h>
#include <stdlib.h>

/*@
 requires n>=0;
 requires n <= 0 || \valid_read(a + (0..n-1));
 assigns \nothing;

 behavior sorted:
  assumes n <= 1 || (\forall integer k; 0 <= k < n-1 ==> a[k] <= a[k+1]);
  ensures \result == 1;

 behavior not_sorted:
  assumes n > 1 && (\exists integer k; 0 <= k < n-1 && a[k] > a[k+1]);
  ensures \result == 0;

 complete behaviors sorted, not_sorted;
 disjoint behaviors sorted, not_sorted;
*/
int arraySorted(int a[], int n){
 int i = 0;
 if (n <= 1) return 1;
 /*@
 loop invariant 0 <= i <= n;
 loop invariant \forall integer k; 0 <= k < i ==> a[k] <= a[k+1];
 loop assigns i;
 loop variant n - i;
 */
 while (i < n-1){
    /*@ assert i < n; */
    if(a[i] > a[i+1]){
        return 0;
    }
    i = i + 1;
 }
 return 1;
}

/*@ assigns \nothing; */
int main(){
    int a[] = {1,2,3,4,5};
    int n = 5;
    arraySorted(a,n);
    return 0;
}
