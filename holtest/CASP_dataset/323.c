/*@ requires n > 0;
    requires \valid(p + (0..n-1));
    assigns \nothing;
    ensures 0 <= \result < n;
    ensures \forall int i; 0 <= i < n ==> p[\result] >= p[i];
*/
int array_max(int *p, int n)
{
	int max_idx = 0;
	int max = p[max_idx];

	/*@ loop invariant 0 <= i <= n;
	    loop invariant 0 <= max_idx < n;
	    loop invariant max == p[max_idx];
	    loop invariant \forall integer j; 0 <= j < i ==> p[max_idx] >= p[j];
	    loop invariant \forall integer j; 0 <= j < i ==> max >= p[j];
	    loop assigns max_idx, max, i;
	    loop variant n - i;
	 */
	for (int i = 0; i < n; i++) {
		if (max < p[i]) {
			max_idx = i;
			max = p[i];
		}
	}

	return max_idx;
}