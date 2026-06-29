#include <limits.h>
/*@
    requires (x > INT_MIN) && (y > INT_MIN) && (x >= y && x - y <= INT_MAX || x < y && x - y >= INT_MIN);
    ensures y == x-\result;
    assigns \nothing;
*/
int diff (int x, int y) {
    return x-y;
}

/*@ assigns \nothing; */
void main() {
    int t = diff(10, 5);
    //@ assert t == 5;
}