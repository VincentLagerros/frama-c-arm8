#include <stdint.h>

/*@ 
    ensures \result == x || \result == y; 
    ensures \result >= x;
    ensures \result >= y; 
    assigns \nothing;
*/ 
int max(int x, int y) {
    if (x > y) {
        return x; 
    } else {
        return y;
    }
}

/*@ 
    ensures (boolean)x; 
*/ 
uint32_t bitneg(uint32_t x) {
    return x;
}

// /*@
//     requires \valid(p);
//     requires \valid(q);
// 
//     assigns \nothing;
//     
//     ensures (\result == *p) || (\result == *q);
//     
//     ensures \result >= *p;
//     ensures \result >= *q;
// */
// int max_ptr(int* p, int* q) {
//     if (*p >= *q) {
//         return *p;
//     } else {
//         return *q;
//     }
// }