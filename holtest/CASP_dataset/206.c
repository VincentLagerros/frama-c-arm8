
/*@ assigns \nothing;
    ensures \result == a / 2;
 */
unsigned rshift(unsigned a)
{
	return a >> 1;
}
