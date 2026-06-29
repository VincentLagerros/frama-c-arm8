/*@
	requires \valid(t+(0..taille-1)) && taille>0 && 2*(taille-1) < 2147483647;
	assigns t[0..taille-1];
	ensures \forall integer i; 0<=i<taille ==> t[i] == 2*i;
*/
void doubled(int t[], int taille){
	/*@
		loop invariant 0 <= i <= taille;
		loop invariant \forall integer j; 0 <= j < i ==> t[j] == 2*j;
		loop assigns i, t[0..taille-1];
		loop variant taille-i;
	*/
	for (int i=0; i<taille; i++) {
		t[i] = 2*i;
		/*@ assert t[i] == 2*i; */
	}
}