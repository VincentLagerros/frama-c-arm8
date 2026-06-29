/*@ requires b != 0 && (a != -2147483648 || b != -1); // Prevent potential overflow
	assigns \nothing;
	ensures \result == (a % b);
 */
int mod(int a, int b)
{
	return a % b;
}