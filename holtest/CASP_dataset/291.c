/*@ requires \valid_read(p+(0..n-1));
  @ ensures \result > 0;
  @ assigns \nothing;
  @ */
int somefun(char *p, int n) {
  return 1;
}