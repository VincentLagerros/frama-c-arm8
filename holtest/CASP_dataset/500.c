/*@ requires length > 0 && \valid(a+(0..length-1));
    assigns \nothing; // Changed assigns clause to \nothing
    ensures 0<=\result<length &&
      (\forall integer j; 0<=j<length ==> a[\result]<=a[j]);
*/
int find_min(int* a, int length) {
  int min, min_idx;
  min_idx = 0;
  min = a[0];
  /*@ loop invariant 0<=i<=length ;
      loop invariant 0<=min_idx<length;
      loop invariant \forall integer j; 0<=j<i ==> min<=a[j];
      loop invariant a[min_idx]==min;
      loop assigns min, min_idx, i;
      loop variant length - i; */
  for (int i = 1; i<length; i++) { // Corrected loop condition to i < length
    if (a[i] < min) {
      min_idx = i; /* min_idx = i; */
      min = a[i];
    }
  }
  return min_idx;
}
