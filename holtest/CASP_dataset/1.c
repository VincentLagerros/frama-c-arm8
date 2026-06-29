/*@ assigns \nothing;
    ensures \result == \min(\max(min, v), max);
 */
int clamp(int v, int min, int max)
{
	int low = v > min ? v : min;
	return low < max ? low : max;
}
