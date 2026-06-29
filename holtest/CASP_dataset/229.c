/*@ requires size>0;
    requires \valid(t+(0..size-1));
    requires \valid(s+(0..size-1));
    requires \valid(r+(0..size-1));
    requires \separated(t+(0..size-1), s+(0..size-1));
    requires \separated(t+(0..size-1), r+(0..size-1));
    requires \separated(s+(0..size-1), r+(0..size-1));
    requires \forall integer i; 0 <= i < size ==> -10000 <= t[i] <= 10000;
    requires \forall integer i; 0 <= i < size ==> -10000 <= s[i] <= 10000;
    assigns r[0..size-1];
    ensures \forall integer i; 0<=i<size ==> r[i]==t[i]+s[i];

    behavior main_behavior:
      ensures \forall integer i; 0<=i<size ==> r[i]==t[i]+s[i];

    complete behaviors main_behavior;
    disjoint behaviors main_behavior;
*/
void sum(int t[],int s[], int r[], int size) {
/*@ loop invariant 0<=i<=size;
    loop invariant \forall integer j; 0<=j<i ==> r[j]==t[j]+s[j];
    loop assigns i, r[0..size-1];
    loop variant size-i;
*/
      for(int i=0;i<size;i++) {
            r[i]=t[i]+s[i];
      }
 }
