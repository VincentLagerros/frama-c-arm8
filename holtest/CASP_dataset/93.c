/*@
  @    requires
  @      \valid(t + (0..size - 1)) &&
  @      0 <= i < size &&
  @      0 <= j < size;
  @
  @    ensures
  @      \forall integer k;
  @        0 <= k < size && k != i && k != j ==>
  @        t[k] == \old(t[k]);
  @
  @    ensures
  @      t[i] == \old(t[j]) &&
  @      t[j] == \old(t[i]);
  @
  @    assigns
  @      t[i], t[j];
  @
  @*/
void swap(int t[], int size, int i, int j) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

