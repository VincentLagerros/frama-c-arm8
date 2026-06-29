// TODO : mettre les bonnes annotations...

/*@
    requires n >= 0;
    requires \valid_read(src+(0..n-1));
    requires \valid(dst+(0..n-1));
    assigns dst[0..n-1];
    ensures dst[0..n-1] == \old(src[0..n-1]);
*/
void array_copy(int *src, int *dst, int n) {
    if (src < dst) {
        // recopier de droite à gauche
        /*@
            loop invariant -1 <= i <= n-1;
            loop invariant
                \forall int k; i < k <= n-1 ==> dst[k] == \at(src[k], Pre); 
            loop invariant
                \forall int k; 0 <= k <= i ==> src[k] == \at(src[k], Pre);
            loop assigns i, dst[0..n-1];
            loop variant i+1;
        */
        for (int i = n-1; -1 < i; i--) {
            dst[i] = src[i];
        }
    } else {
        // recopier de gauche à droite
        /*@
            loop invariant 0 <= i <= n;
            loop invariant
                \forall int k; 0 <= k < i ==> dst[k] == \at(src[k], Pre);
            loop invariant
                \forall int k; i <= k < n ==> src[k] == \at(src[k], Pre);
            loop assigns i, dst[0..n-1];
            loop variant n-i;
        */
        for (int i = 0; i < n; i++) {
            dst[i] = src[i];
        }
    }
}
