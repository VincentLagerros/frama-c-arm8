#include <stdint.h>

/*@ 
    ensures \result == x || \result == y; 
    ensures \result >= x;
    ensures \result >= y; 
    assigns \nothing;
*/ 
int64_t max(int64_t x, int64_t y) {
    if (x > y) {
        return x; 
    } else {
        return y;
    }
}