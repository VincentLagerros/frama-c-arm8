/*@ assigns \nothing;
    ensures \result == \max(\max(a, b), \max(b, c));
 */
int max3(int a, int b, int c)
{
	return a > b ? (a > c ? a : c) : (b > c ? b : c);
}
