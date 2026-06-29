/*@
   requires c >= 0;
   assigns \nothing;
   ensures \true;
 */

void f (int c) {
	/*@ loop invariant c >= 0;
	    loop invariant c <= \at(c, Pre);
	    loop assigns c;
            loop variant c;
	 */
	while (c != 0) {
		c--;
	}
	return;
}