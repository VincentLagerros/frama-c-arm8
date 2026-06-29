/*@ requires 1000>taille>0;
    requires \valid(t+(0..taille-1));
    ensures \forall integer i; 0<=i<taille ==> t[i] == (i*2) ;
    ensures \forall integer i; 0<=i<taille-1 ==> t[i]<=t[i+1];  
*/
 
void doubleint(int t[],int taille) {  // void double() --> not possible since datatype!
       /*@ loop invariant 0<=i<=taille; 
           loop invariant \forall integer j; 0<=j<i ==> t[j] == (j*2) ;
           loop invariant \forall integer j; 0<=j<i-1 ==> t[j]<=t[j+1];
           loop assigns t[0..taille-1],i;
           loop variant taille-i;
       */
       for(int i=0;i<taille;i++) {
          t[i]=i*2;
       }
}