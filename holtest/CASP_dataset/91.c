/*
Software versions:
  frama-c : 18.0 (Argon)
  alt-ergo : 2.2.0

This script was run using this command:
  frama-c -wp -wp-prover alt-ergo -wp-rte -wp-timeout 300 -wp-verbose 0 countSameConsecutive.c -then -report
*/

// This predicate is true if there is a subsequence of length "answer"
// with all its elements equal.
/*@ predicate isValidAnswer(integer N, int *x, int answer) =  
  @ \exists integer i; 0 <= i <= N-answer &&
  @   (\forall integer j; i <= j <= i+answer-1 ==> x[j] == x[i]);
  @*/

// This predicate is true if there is no subsequence of length "answer+1"
// with all its elements equal.
/*@
  @ predicate noBetterAnswerExists(integer N, int *x, int answer) =
  @  (N == answer) || 
  @  ((1 <= answer < N) && (\forall integer i; 0 <= i <= N-1-answer ==>
  @    (\exists integer j; i < j <= i+answer && x[j] != x[i])));
  @*/


/*@
  @ predicate isBest(integer N, int *x, int answer) =  
  @   isValidAnswer(N, x, answer) &&
  @   noBetterAnswerExists(N, x, answer); 
  @*/

/*@ requires 1 <= N <= 1000000;
  @ requires \valid(x + (0 .. N-1));
  @ assigns \nothing;
  @ ensures isBest(N, x, \result);
  @*/
int countSameConsecutive(int N, int x[]) {
    int best = 0, i = 0;
    /*@ loop invariant 0 <= i <= N;
      @ loop invariant i == 0 ==> best == 0;
      @ loop invariant 0 < i <= N ==> isBest(i, x, best);
      @ loop invariant 0 < i <  N ==> x[i] != x[i-1];
      @ loop assigns i, best;
      @ loop variant N-i;
      @*/
    while (i < N) {
        int j = i+1;
        /*@ loop invariant i+1 <= j <= N;
          @ loop invariant \forall integer k; i+1 <= k < j ==> x[i] == x[k];
          @ loop assigns j;
          @ loop variant N-j;
          @*/
        while (j < N && x[j] == x[i]) ++j;
        if (j-i > best) best = j-i;
        i = j;
    }
    return best;
}
