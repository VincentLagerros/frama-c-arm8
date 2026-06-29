/*@
  @ requires n > 0;
  @ requires \valid(a+(0..n-1));
  @ 
  @ assigns \nothing;
  @ behavior true_:
  @   assumes \forall integer i; 0 <= i < n / 2 ==> a[i] == a[n - i - 1];
  @   ensures \result == 1;
  @ behavior false_:
  @   assumes \exists integer i; 0 <= i < n / 2 &&  a[i] != a[n - i - 1];
  @   ensures \result == 0;
  @ complete behaviors true_, false_;
  @ disjoint behaviors true_, false_;
*/
int palindrome(int a[], int n) {
    /*@
      @ loop invariant 0 <= i <= n / 2;
      @ loop invariant \forall integer j; 0 <= j < i ==> a[j] == a[n - j - 1];
      @ loop assigns i;
      @ loop   variant n - 2 * i;
    */
    for (int i = 0; i < n / 2; ++i) {
        if (a[i] != a[n - i - 1]) return 0;
    }
    return 1;
}