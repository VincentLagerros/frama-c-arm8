/*@ 
	ensures \result==a || \result==b;
*/
int max(int a,int b)
{
	if(a==b) return a;
	return a>b?a:b;
}
