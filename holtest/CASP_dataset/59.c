/*@ predicate sorted{L}(int* a, int length) =
     \forall integer i,j; 0<=i<=j<length ==> a[i]<=a[j];
*/
/*@ requires \valid(a+(0..length-1));
    requires sorted(a,length);
    requires length >=0;

    assigns \nothing;

    behavior exists:
      assumes \exists integer i; 0<=i<length && a[i] == key;
      ensures 0<=\result<length && a[\result] == key;

    behavior not_exists:
      assumes \forall integer i; 0<=i<length ==> a[i] != key;
      ensures \result == -1;

    complete behaviors;
    disjoint behaviors;
*/
int binary_search(int* a, int length, int key) {
  int low = 0, high = length - 1;
  /*@ loop invariant 0<=low<=high+1;
      loop invariant high<length;
      loop assigns low,high;
      loop invariant \forall integer k; 0<=k<low ==> a[k] < key;
      loop invariant \forall integer k; high<k<length ==> a[k] > key;
      loop variant high-low;
  */
  while (low<=high) {
    int mid = low+(high-low)/2;
    if (a[mid] == key) return mid;
    if (a[mid] < key) { low = mid+1; }
    else { high = mid - 1; }
  }
  return -1;
}
