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

/*@ 
    ensures *a == b[1];
*/
void incrstar(int *a, int* b) {
    *a = 10;
    *b = 10;
}