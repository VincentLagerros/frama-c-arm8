/*@ assigns \nothing;
    ensures \result == \max(a, b) - \min(a, b);
 */
unsigned distance(unsigned a, unsigned b)
{
	return (a > b) ? (a - b) : (b - a);
}
