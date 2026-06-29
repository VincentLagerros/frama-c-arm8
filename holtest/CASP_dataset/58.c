/*@ requires b != 0;
    requires b != -1;
    assigns \nothing;
    ensures \result == a;
 */
int divmult(int a, int b)
{
	return (a / b) * b + (a % b);
}
