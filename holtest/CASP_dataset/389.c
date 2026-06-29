/*@ predicate valid_subseq{L}(int *x, integer left, integer right) = 
  @     left < right ==> \forall integer i, j; left <= i < right && left <= j < right ==> x[i] == x[j];
*/

/*@ requires 1 <= N <= 1000000;
  @ requires \valid(x + (0..N-1));
  @ ensures 1 <= \result <= N;
  @ ensures \exists integer k; 0 <= k < N && valid_subseq(x, k, k + \result);
  @ assigns \nothing;
*/
int countSameConsecutive(int N, int x[]) {
    int best = 0, i = 0;

    /*@ loop invariant 0 <= i <= N;
      @ loop invariant i == 0 ==> best == 0;
      @ loop invariant i > 0 ==> 1 <= best <= i;
      @ loop invariant i > 0 ==> \exists integer k; 0 <= k < i && valid_subseq(x, k, k + best);
      @ loop assigns i, best;
      @ loop variant N - i;
    */
    while (i < N) {
        int j = i+1;

        /*@ loop invariant i < j <= N;
          @ loop invariant valid_subseq(x, i, j);
          @ loop assigns j;
          @ loop variant N - j;
        */
        while (j < N && x[j] == x[i]) ++j;

        /*@ assert (j < N ==> (x[j] != x[i] && x[j] != x[j - 1])) || j == N;*/
        /*@ assert i == 0 && j == N ==> valid_subseq(x, 0, N);*/
        if (j-i > best) best = j-i;

        /*@ assert j - i <= best;*/
        i = j;
    }

    /*@ assert best <= N;*/
    return best;
}