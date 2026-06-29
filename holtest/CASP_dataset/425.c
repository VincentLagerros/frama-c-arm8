/* run.config
   OPT: -rpp
*/

/*
 * Based on http://stackoverflow.com/questions/23907134/comparing-two-arrays-using-dictionary-order-in-an-array-of-arrays-java
 *
 */

struct AInt{
  int t[10];
  int length;
};


/*@ requires 0 <= o1.length && o1.length <= 10;
  @ requires 0 <= o2.length && o2.length <= 10;
  @ assigns \result \from o1,o2;
*/
int compare(struct AInt o1, struct AInt o2){
    int index, aentry, bentry;
    index = 0;
    /*@ loop invariant 0 <= index && index <= o2.length && index <= o1.length;
      @ loop invariant \forall integer k; 0 <= k < index ==> o1.t[k] == o2.t[k];
      @ loop assigns index,aentry,bentry;
      @ loop variant o1.length - index;
      */
    while ((index < o1.length) && (index < o2.length)) {
      aentry = o1.t[index];
      bentry = o2.t[index];
      if (aentry < bentry) {
	return -1;
      }
      if (aentry > bentry) {
	return 1;
      }
      index++;
    }
    if (o1.length < o2.length) return -1;
    if (o1.length > o2.length) return 1;
    return 0;
  }
