struct S {
  char *x;
  int *y;
};

/*@
   requires \valid(s) && \valid_read(s->x) && \valid_read(s->y) &&
            (int)(*s->x) + *s->y >= -2147483648 && (int)(*s->x) + *s->y <= 2147483647;
   ensures \result == (int)(*s->x) + *s->y;
   assigns \nothing;
*/
int f(struct S* s) {
  return *s->x + *s->y;
}