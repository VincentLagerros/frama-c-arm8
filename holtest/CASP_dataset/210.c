/*@
	requires a >= -2147483648 && a <= 2147483647;
	requires b >= -2147483648 && b <= 2147483647;
	ensures \result == a;
*/
int trans(int a, int b){
	int c = a;
	b = c;
	return b;
}
