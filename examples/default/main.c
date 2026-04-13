#include <stdint.h>
#include <limits.h>
#include <string.h>
/*@ 
    requires \true;
    ensures (\result == \old(x) || \result == \old(y)) && \old(x) <= \result && \old(y) <= \result;
*/ 
uint64_t max(uint64_t x, uint64_t y) {
    if (x > y) {
        return x; 
    } else {
        return y;
    }
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