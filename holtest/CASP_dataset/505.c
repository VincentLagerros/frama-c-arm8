/*@ requires \true;
    assigns \nothing;
    ensures \result == b;
 */
int deadcode(int a, int b)
{
	if (a > b) {
		if (a < b) {
			return a / b;
		} else if (a == b) {
			//@ assert 0 == 1;
		}
	}

	return b;
}
