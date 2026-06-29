/* UNSAFE because `assigns *q;` and not `assigns **q;`. */

int g = 42;

/*@
  requires \valid(p) && \valid(q) && \valid(*q);
  assigns *p, **q, g;
*/
void foo(int* p, int** q) {
  *p  = 42;
  **q = 42;
  g   = 42;
}