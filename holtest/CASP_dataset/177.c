// pour INT_MIN
#include <limits.h>

// valeur absolue
/*@
 requires a != INT_MIN;
 ensures \result >= 0;
 ensures \result == a || \result == -a;
 */
int abs(int a)
{
	return (a > 0) ? a : -a;
}
