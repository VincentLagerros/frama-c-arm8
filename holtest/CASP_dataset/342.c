#include <limits.h>
/*@
    requires x+y <= INT_MAX;
    requires x+y >= INT_MIN;
    requires x >= INT_MIN &&  y >= INT_MIN;
    ensures \result == x+y;
    assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}
