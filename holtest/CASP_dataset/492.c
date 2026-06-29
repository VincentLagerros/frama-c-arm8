/*@
requires n > 0;
requires \valid(a+(0..n-1));
requires \valid(b+(0..n-1));

assigns \nothing;

behavior same:
assumes \forall integer k; 0 <= k < n ==> a[k] == b[k];
ensures \result==1;

behavior different:
assumes \exists integer k; 0 <= k < n && a[k] != b[k];
ensures \result==0;

complete behaviors same, different;
disjoint behaviors same, different;

 */


/* NOTE : the opposite of the proposition
   \forall integer k; 0 <= k < n ==> a[k] == b[k]
 is the proposition
   \exists integer k; 0 <= k < n && a[k] != b[k]
INDEED !
- the negation of (A ==> B) is A && (negation of B)
- seen from another point of view, "the negation of forall k, A"
  is "exists k, the negation of A"

(this is 100% logical if you think of it a bit)
*/

int equal(const int* a, int n, const int* b) {

  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == b[k];
    
    loop assigns i;
    loop variant n-i;
   */
  
  for(int i=0; i<n; i++) {
    if (a[i] != b[i]) {
      return 0;
    }
  }
  return 1;
}
