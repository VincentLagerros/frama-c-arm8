struct S { int x; };

#include <limits.h>

/*@
  requires \valid(s);
  assigns s->x;
  ensures s->x == 0;
*/
void reset (struct S* s) {
  s->x = 0;
}

/*@
  requires \valid(s);
  requires s->x < INT_MAX;
  assigns s->x;
  ensures s->x > \at(s->x,Pre);
*/
void inc(struct S* s) {
  //@ assert s->x < INT_MAX;
  s->x++;
}

/*@
  requires \valid(s);
  requires s->x > INT_MIN;
  assigns s->x;
  ensures s->x < \at(s->x,Pre);
*/
void dec(struct S* s) {
  //@ assert s->x > INT_MIN;
  s->x--;
}

/*@
  requires \valid(s);
  assigns \nothing;

  behavior is_true:
    assumes s->x > 0;
    ensures \result == 1;

  behavior is_false:
    assumes s->x <= 0;
    ensures \result == 0;

  complete behaviors is_true, is_false;
  disjoint behaviors is_true, is_false;
*/
int is_pos(struct S* s) {
  return s->x > 0;
}