#ifndef _FIND_H_
#define _FIND_H_

/*@
   requires    \valid_read(a + (0..n-1));
   ensures        0 <= \result <= n;

   behavior some:
        assumes        \exists integer i; 0 <= i < n && a[i] == v;
        ensures        0 <= \result < n;
        ensures        a[\result] == v;
        ensures        \forall integer i; 0 <= i < \result ==> a[i] != v;

   behavior none:
        assumes        \forall integer i; 0 <= i < n ==> a[i] != v;
        ensures        \result == n;

   assigns \nothing;
   complete behaviors some, none;
   disjoint behaviors some, none;
 */
unsigned int find(const int* a, unsigned int n, int v) {
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer j; 0 <= j < i ==> a[j] != v;
        loop assigns i;
        loop variant n-i;
    */
    for (unsigned int i = 0; i < n; i++) {
            /*@ assert 0 <= i <= n; */
        if (a[i] == v) {
            return i;
        }
    }
    return n;
}


#endif