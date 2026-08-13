/*@
	ensures (x > 0) ==> \result == 1;
	ensures (x <= 0) ==> \result == 0;
*/
int is_positive(int x) {
    return x > 0;
}