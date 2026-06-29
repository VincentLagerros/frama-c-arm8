/*
 * A simple string matching
 * Takuo Watanabe (Tokyo Institute of Technology)
 *
 * This file can be successfully verified using Frama-C with Jessie plugin.
 *   Frama-C Carbon-20110201
 *   Alt-Ergo 0.92.2 / CVC3 2.2
 */

/*@ predicate MatchAt{L}(char *t, char *p, integer k, integer m) = 
  @   \forall integer l; 0 <= l < m ==> t[k + l] == p[l];
  @*/

/*@ predicate Match{L}(char *t, integer n, char *p, integer m) = 
  @   \exists integer k; 0 <= k <= n - m && MatchAt(t, p, k, m);
  @*/

// Needed to prove (in ATP) that the loop variant >= 0
/*@ lemma nzmul:
  @   \forall integer x, y; x >= 0 ==> y >= 0 ==> x * y >= 0;
  @*/

/*@ requires n >= 0 && \valid(t+(0..n-1));
  @ requires m >= 0 && \valid(p+(0..m-1));
  @ assigns \nothing;
  @ behavior success:
  @   assumes Match(t, n, p, m);
  @   ensures 0 <= \result <= n - m && MatchAt(t, p, \result, m);
  @   ensures \forall integer k;
  @           0 <= k < \result ==> !MatchAt(t, p, k, m);
  @ behavior failure:
  @   assumes !Match(t, n, p, m);
  @   ensures \result == -1;
  @ complete behaviors success, failure;
  @ disjoint behaviors success, failure;
  @*/
int smatch (char t[], int n, char p[], int m) {
    int i = 0, j = 0;
    /*@ loop invariant 0 <= i <= n && 0 <= j <= m;
      @ loop invariant i >= j;
      @ loop invariant MatchAt(t, p, i - j, j);
      @ loop invariant \forall integer k; 0 <= k < i - j ==> !MatchAt(t, p, k, m);
      @ loop assigns i, j;
      @ loop variant m * (n - (i - j)) + (m - j);
      @*/
    while (i < n && j < m) {
        if (t[i] == p[j]) {
            i++;
            j++;
        }
        else {
            i = i - j + 1;
            j = 0;
        }
    }
    return j == m ? i - j : -1;
}