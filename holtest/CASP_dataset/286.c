/*@
 requires \valid (s+(0..n-1));
 requires \valid (t+(0..n-1));
 requires n > 0;
 assigns \nothing;
 ensures \result <==> (\forall integer i; 0 <= i < n ==> s[i] == t[i]);
 */
int compare_array(int s[], int t[], int n)
{
	int i = 0;

	/*@
	 loop invariant \forall integer j; 0 <= j < i ==> s[j] == t[j];
	 loop invariant 0 <= i <= n;
	 loop assigns i;
	 loop variant n-i;
	 */
	while (i < n && s[i] == t[i])
	{
		i++;
	}

	return i == n;
}