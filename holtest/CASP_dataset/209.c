/*@ predicate swapped{L1,L2}(int *a, int *b) = 
\at(*a, L2) == \at(*b,L1) && 
\at(*b, L2) == \at(*a,L1);
*/
/*@ requires \valid(a);
requires \valid(b);
assigns *a, *b;
ensures swapped{Pre, Post}(a, b);
*/
void swap(int *a, int *b)
{
	int tmp = *a;
	*a = *b;
	*b = tmp;
}
