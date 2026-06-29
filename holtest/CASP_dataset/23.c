#include<assert.h>

/*@
  @ ensures \result == 1;
  @
 */
int gimmeOne() {
  return 1;
}

int main() {
  int x = gimmeOne();

  assert(x == 1);
}
