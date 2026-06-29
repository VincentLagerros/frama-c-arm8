/*@ predicate Swap{L1,L2}(int *a, integer i, integer j) =
  @   \at(a[i],L1) == \at(a[j],L2) &&
  @   \at(a[j],L1) == \at(a[i],L2) &&
  @   \forall integer k; k != i && k != j
  @       ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/*@ predicate sorted(int *t,integer i,integer j) =
  @   \forall integer k, integer l; i <= k < l <= j ==> t[k] <= t[l];
  @*/

/*@ requires N>=1 && \valid(A+(0..N-1));
  @ assigns A[0..N-1];
  @ ensures sorted(A,0,N-1);
  @*/
void selectionSort(int A[], int N)
{
    int i, j, min, temp;

    /*@ loop assigns i,j,min,temp, A[0..N-1];
      @ loop invariant 0<=i<=N-1 && sorted(A,0,i) && (\forall integer k1, integer k2; (0<=k1<i<k2<N)==>A[k1]<=A[k2]);
      @ loop variant N-i;
      @*/
    for (i = 0; i < N-1; i++)
    {
        min = i;

        /*@ loop assigns j,min;
          @ loop invariant i+1<=j<=N && i<=min<j && (\forall integer k; (i<=k<j)==>A[min]<=A[k]);
          @ loop variant N-j;
          @*/
        for (j = i+1; j < N; j++){
          if (A[j] < A[min]){
            min = j;
          }
        }

        if(min!=i){
            temp = A[i];
            A[i] = A[min];
            A[min] = temp;
        }
    }
}
