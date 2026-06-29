/*@ requires a < 2147483647 && a >= -1;
  ensures (a >= 0) ==> (\result == a + 1);
  ensures (a < 0) ==> (\result == 0);
*/
int plus_one(int a) {
  if (a >= 0) {
    return a + 1;
  } else {
    return 0;
  }
}