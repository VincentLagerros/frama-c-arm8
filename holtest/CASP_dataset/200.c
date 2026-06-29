/*@ requires b != 0;
    requires b != -1;
    assigns \nothing;
    ensures \result == a / b;
 */
int divide(int a, int b)
{
	return a / b;
}
