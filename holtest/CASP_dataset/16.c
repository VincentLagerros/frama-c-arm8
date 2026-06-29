/*@
    requires n>0;
    requires \valid_read(a + (0..n-1));
    behavior sorted:
        assumes \forall integer i;
            1<=i<n ==> a[i]>=a[i-1];
        ensures \result ==1;
    behavior unsorted:
        assumes \exists integer i;
            1<=i<n && a[i]< a[i-1];
        ensures \result ==0;
    complete behaviors;
    disjoint behaviors;
*/
int is_sorted(int a[],int n){
    /*@
        loop invariant \forall integer j;
            1<=j<i ==> a[j]>=a[j-1];
        loop invariant 1<= i <= n;
        loop assigns i;
        loop variant n-i;
    */
    for (int i=1;i<n;i++){
        if (a[i-1]>a[i]){
            return 0;
        }
    }
        return 1;
}
