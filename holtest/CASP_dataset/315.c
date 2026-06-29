// teste si un tableau est un palindrome
// ESOPE RESTE ELU PAR CETTE CRAPULE ET SE REPOSE
/*@
 requires \valid (t+(0..n-1));
 requires n > 0;
 assigns \nothing;
 ensures \result <==> (\forall integer i; 0 <= i < n/2 ==> t[i] == t[n-i-1]);
 */
int is_palindrome(int t[], int n)
{
	int mid = n/2;
	int i = 0;

	/*@
	 loop invariant 0 <= i <= mid;
	 loop invariant \forall integer j; 0 <= j < i ==> t[j] == t[n-1-j];
	 loop assigns i;
	 loop variant mid - i;
	 */
	while (i < mid && t[i] == t[n-i-1])
	{
		i++;
	}

	return i == mid;
}