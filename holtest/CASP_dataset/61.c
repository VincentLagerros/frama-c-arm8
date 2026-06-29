/*@ requires \valid(arr + (0..size-1));
    requires \forall integer i; 0 <= i < size ==> 0 <= arr[i] < size;
    requires 0 <= addr < size;
    assigns arr[0..size-1];
    ensures arr[\at(arr[addr],Pre)] == 0;
 */
void indaddr(unsigned size, int arr[size], unsigned addr)
{
	arr[arr[addr]] = 0;
}
