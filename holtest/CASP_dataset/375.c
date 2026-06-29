/*@ 
requires n>0;
requires \valid_read(a+(0..n-1));
ensures \forall integer k; 0<=k<n ==> \result>=a[k];
*/
int max(int a[], int n){
    int m=a[0];
/*@
    loop invariant \forall integer j; 0<=j<i ==> m>=a[j];
    loop invariant 1<=i<=n;
    loop assigns i,m;
    loop variant n-i;

*/
    for(int i=1;i<n;i++){
        if(m<a[i]){
            m=a[i];
        }
    }
    return m;
}