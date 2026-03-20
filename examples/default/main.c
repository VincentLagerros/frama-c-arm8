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
    requires \valid(p);
    requires \valid(q);

    assigns \nothing;
    
    ensures (\result == *p) || (\result == *q);
    
    ensures \result >= *p;
    ensures \result >= *q;
*/
int max_ptr(int* p, int* q) {
    if (*p >= *q) {
        return *p;
    } else {
        return *q;
    }
}