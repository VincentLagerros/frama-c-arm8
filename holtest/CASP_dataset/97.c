/*@ predicate sorted{L}(int* a, integer length) =
      \forall integer i,j; 0<=i<=j<length ==> a[i]<=a[j];
*/
/*@ requires \valid(a+(0..length-1));
    requires length > 0;
    assigns a[0..length-1];
    ensures sorted(a,length);
*/
void sort (int* a, int length) {
  int current;
  /*@ loop invariant 0<=current<length;
      loop assigns a[0..length-1],current;
      loop invariant sorted(a,current);
      loop invariant
        \forall integer i,j; 0<=i<current<=j<length ==> a[i] <= a[j];
      loop variant length-current;
   */
  for (current = 0; current < length - 1; current++) {
    int min_idx = current;
    int min = a[current];
    /*@ loop invariant current+1<=i<=length;
        loop assigns i,min,min_idx;
        loop invariant current<=min_idx<i;
        loop invariant a[min_idx] == min;
        loop invariant
          \forall integer j; current<=j<i ==> min <= a[j];
        loop variant length -i;
    */
    for (int i = current + 1; i < length; i++) {
      if (a[i] < min) {
	min = a[i];
	min_idx = i;
      }
    }
    if(min_idx != current) {
       L: a[min_idx]=a[current];
       a[current]=min;
    }
  }
}
