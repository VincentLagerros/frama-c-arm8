// remplir un tableau avec une valeur donnée
/*@
 requires \valid (t+(0..n-1));
 requires n > 0;
 assigns t[0..n-1];
 ensures \forall integer i; 0 <= i < n ==> t[i] == val;
 */
void fill_array(int t[], int n, int val)
{

	int i = 0;

	/*@
	 loop invariant \forall integer j; 0 <= j < i ==> t[j] == val;
	 loop invariant 0 <= i <= n;
	 loop variant n-i;
	 */
	while (i < n)
	{
		t[i] = val;
		i++;
	}
}
