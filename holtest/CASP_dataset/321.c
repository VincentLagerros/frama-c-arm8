/*@ requires size >= 0 && \valid(t+(0..size-1));
  @ assigns t[0..size-1];
  @ ensures \forall integer i; 0 <= i < size ==> t[i] == 0;
@*/
void out_ecount(char *t, int size) {
  int i;

  /*@ loop assigns i, t[0..size-1];
      loop invariant 0 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==> t[k] == 0;
      loop invariant \forall integer k; i <= k < size ==> t[k] == \at(t[k], Pre);
      loop variant size - i;
  */
  for (i = 0; i < size; i++)
	  t[i] = 0;

  //@ assert \forall integer k; 0 <= k < size ==> t[k] == 0;
}