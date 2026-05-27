#include <limits.h>

/*@
  @ requires b >= 0 ? (a <= INT_MAX - b) : (a >= INT_MIN - b);
  @ 
  @ assigns \nothing;
  @ 
  @ ensures \result == a + b;
  @*/
int safe_add(int a, int b) {
    if (b > 0 && a > INT_MAX - b) {
        // Handle overflow error safely
        return -1; 
    } else if (b < 0 && a < INT_MIN - b) {
        // Handle underflow error safely
        return -1;
    }
    return a + b;
}