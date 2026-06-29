/* Run with:
 *
 * frama-c -wp -wp-prover alt-ergo -wp-rte -wp-print -wp-timeout 300 -wp-verbose 0 ex9_final.c -then -report
 *
 * Tested with Frama-C Sulfur-20171101.
 * Η ορθότητα του προγράμματος εξασφαλίζεται πρώτον από το loop invariant της γραμμής 52, που λέει ουσιαστικά ότι, από
 * όλες τις θέσεις του a που η επανάληψη έχει προσπεράσει, καμία τιμή σε αυτές τις θέσεις
 * δεν έχει αντίγραφο σε προηγούμενη θέση του a, και δεύτερον από το ensures της γραμμής 38, της οποίας το predicate 
 * ελέγχει για την ορθότητα του αποτελέσματος που επιστρέφεται από τη συνάρτηση.
 */

#include <stdbool.h>

#define MAXV 1000000

/*@ predicate noDouble{L}(int n, int *a) =
  @     \forall integer i; 0 <= i < n-1 ==>
  @         \forall integer j; i+1 <= j < n ==> \at(a[i], L) != \at(a[j], L);
  @*/


/*@ predicate existsDoubleRes{L}(int n, int *a, int res) =
  @     \exists integer i, j; 0 <= i < j < n ==> res == \at(a[i], L) && res == \at(a[j], L);
  @*/

/*@ predicate validateResult{L}(int n, int *a, int res) =
  @     res == 0 ?
  @         noDouble{L}(n, a) :
  @         existsDoubleRes{L}(n, a, res);
  @*/



/*@ requires 0 < N <= MAXV;
  @ requires \valid(a + (0..(N-1)));
  @ requires \forall integer i; 0 <= i < N ==> 1 <= a[i] <= MAXV;
  @ assigns \nothing;
  @ ensures 0 <= \result <= MAXV;
  @ ensures validateResult(N, a, \result);
  @*/
int findDouble(int N, int a[]) {
    bool f[MAXV];

    /*@ loop assigns i, f[0..(MAXV-1)];
      @ loop invariant 1 <= i <= (MAXV+1);
      @ loop invariant \forall integer k; 1 <= k < i ==> f[k-1] == false;
      @ loop variant MAXV-i;
      @*/
    for (int i = 1; i <= MAXV; ++i)
        f[i-1] = false;

    /*@ loop assigns i, f[0..(MAXV-1)];
      @ loop invariant 0 <= i <= N;
      @ loop invariant \forall integer k; 0<=k<i ==> f[a[k]-1] == true;
      @ loop invariant \forall integer k; 0 < k < i ==>
      @                    \forall integer l; 0 <= l < k ==>  a[k] != a[l];
      @ loop variant N-i;
      @*/
    for (int i = 0; i < N; ++i)
        if (f[a[i]-1])
            return a[i];
        else
            f[a[i]-1] = true;
    return 0;
}