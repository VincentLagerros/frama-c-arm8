#define INT_MIN (-2147483648)
#define INT_MAX 2147483647

/*@ requires INT_MIN <= a + b <= INT_MAX;
    assigns \nothing;
    ensures \result == a + b;
 */
int sum(int a, int b)
{
	return a + b;
}
