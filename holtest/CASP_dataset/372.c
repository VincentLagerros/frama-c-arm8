/*@
  @ requires \valid(p);
  @ requires \valid(q);
  @ requires -1000 <= *p <= 10000;
  @ requires -1000 <= *q <= 10000;
  @ assigns *p, *q;
  @ ensures *p == \old(*q);
  @ ensures *q == \old(*p);
*/
void swap(int *p, int *q) {
    int temp = *p;
    *p = *q;
    *q = temp;
}