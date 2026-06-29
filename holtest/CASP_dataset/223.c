/*@
  @ requires n > 0;
  @ requires \valid_read(a+(0..n - 1));
  @ requires \valid_read(b+(0..n - 1));
  @ requires \valid(c+(0..n - 1));
  @ requires \separated(a+(0..n-1), b+(0..n-1), c+(0..n-1));
  @ requires \forall integer i; 0 <= i < n ==> -10000 <= a[i] <= 10000;
  @ requires \forall integer i; 0 <= i < n ==> -10000 <= b[i] <= 10000;
  @ ensures \forall integer i; 0 <= i < n ==> c[i] == a[i] + b[i];
  @ assigns c[0..n-1];
*/
void sum_array(int a[], int b[], int c[], int n) {
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \valid_read(a+(0..n - 1));
      @ loop invariant \valid_read(b+(0..n - 1));
      @ loop invariant \valid(c+(0..n - 1));
      @ loop invariant \forall integer j; 0 <= j < i ==> c[j] == a[j] + b[j];
      @ loop assigns i, c[0..n-1];
      @ loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        c[i] = a[i] + b[i]; 
    }
}