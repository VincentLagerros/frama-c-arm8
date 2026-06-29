#define INT_MIN (-2147483648)

/*@ requires v != INT_MIN;
    assigns \nothing;
    ensures \result == \abs(v);
 */
int abs(int v)
{
	return v >= 0 ? v : -v;
}
