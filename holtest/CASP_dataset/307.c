#include <limits.h>

/*@
  assigns \nothing;
*/
void try_initialize_array ( void )
{
	int array[5];

	// To prove asserts at the end of this function,
	// uncomment following loop invariant. It might also be helpful to ensure
	// that i has proper bounds (or use -wp-invariants).
	/*@ loop invariant I1:
		0 <= i <= 5 &&
		( \forall integer j; 0 <= j < i ==> array[j] == 1 - j);
		loop assigns i, array[0 .. 4];
		loop variant 5 - i; */
	for (int i = 0; i < 5; i++)
	{
		// Try uncommenting one of following lines:
		// i = -1; // Runtime error
		// i = 0;  // No error, but does not terminate. Invariant is preserved

		array[i] = 1 - i;
	}

	if ( array[2] == -2 )
		array[2]++;

	/*@ assert array[2] != -2; */	
	/*@ assert array[3] == -2; */
}


/*@
	requires len > 0;
	requires \valid ( array + ( 0 .. len - 1 ) );
	// In specifications we use mathematical integers.
	requires len + base_value < INT_MAX;

	// i++ may overflow elsewhere
	requires len < INT_MAX;
	assigns array[0 .. len-1];
	ensures \forall integer i; 0 <= i < len ==>
		array [i] == base_value + i;
 */
void try_initialize_given_array ( int *array, int len, int base_value )
{
	/*@
		loop invariant
			// WP somehow knows this
			 0 <= i <= len &&
			(
				\forall integer j; 0 <= j < i ==>
				array[j] == base_value + j
			);
			// BTW an error happens when using this syntax:
			// loop assigns array + (0 .. len - 1);

			// It is easy to forget 'i'
		loop assigns i, array[0 .. len - 1];
		loop variant len - i;

	 */
	for ( int i = 0; i < len; i++)
	{
		array[i] = base_value + i;
	}
}

/*@
  assigns \nothing;
*/
int main ( int argc, char *argv[] )
{
	try_initialize_array();
	int array[17];
	try_initialize_given_array ( array, 5, 0 );
	/*@ assert array[1] == 1; */
	/*@ assert array[3] == 3; */

	try_initialize_given_array ( array + 3, 11, 5 );
	/*@ assert \forall integer i; 0 <= i < 11 ==> array[i+3] == 5 + i; */
	/*@ assert \forall integer i; 0 <= i < 11 ==> array[i+3] == 5 + i; */
	/*@ assert array[8+3] == 5 + 8; */
	/*@ assert array[11] == 13; */
	
	// This fails, because precondition is not met
	//try_initialize_given_array ( array, 18, 0 );
	return 0;
}
