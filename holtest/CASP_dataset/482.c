/*@
  predicate canSee{L} (integer N, int *x, integer i) =
    \forall integer j; i < j < N ==> \at(x[i], L) > \at(x[j], L);
*/

/*@
  predicate countTall{L} (integer N, int *x, integer i, integer c) =
    i >= N ? c == 0 :
      canSee{L}(N, x, i) ? countTall{L}(N, x, i + 1, c - 1)
                         : countTall{L}(N, x, i + 1, c);
*/

/*@
  requires N >= 1 && N <= 1000000;
  requires \valid (x + (0 .. N -1));
  ensures \forall integer i; 0 <= i < N ==> x[i] == \old(x[i]);
  ensures countTall (N, x, 0, \result);
*/
int countWhoCanSee (int N, int x[]) {
  int tallest = x[N - 1];
  int count = 1;

  /*@
    loop invariant -1 <= i < N -1;
    loop invariant count + i <= N - 1;
    loop invariant \forall integer j; i < j < N ==> tallest >= x[j];
    loop invariant \exists integer j; i < j < N && tallest == x[j];
    loop invariant countTall (N, x, i + 1, count);
    loop assigns tallest, i, count;
    loop variant i + 1;
  */
  for (int i = N - 2; i >= 0; --i)
    if (tallest < x[i]) {
      tallest = x[i];
      count++;
    }

  return count;
}