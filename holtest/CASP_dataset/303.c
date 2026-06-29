/*@
requires n > 0;
requires \valid_read(t+(0..n-1));
ensures \result <==> (\forall integer i; 0 <= i < n ==> t[i] == 0);
*/

int arraynull(int t[], int n){
	/*@
		loop invariant 0 <= i <= n;
		loop invariant \forall integer j ; 0 <= j < i ==> t[j] == 0; 
		loop assigns i;
		loop variant n-i;
	*/
	for(int i = 0; i < n ; i++){
		if (t[i] != 0) {
			return 0;
		}	
	}
	return 1;
}