#define INT_MAX 2147483647

/*@ requires (a * 2) <= INT_MAX;
    assigns \nothing;
    ensures \result == a * 2;
 */
unsigned lshift(unsigned a)
{
	return a << 1;
}
