// In some versions of Frama-C, an additional option -pp-annot should be used to parse this example

#include <limits.h>

/*@
  requires (*b >= 0 && *a <= INT_MAX - *b);
  requires (*b < 0 && *a >= INT_MIN - *b);
  requires \valid(a) && \valid(a);
  assigns *a;
  ensures *a == \old(*a) + *b;
*/
void incr_a_by_b(int* a, int const* b){
  *a += *b;
}
