#include <stdbool.h>
/*@
	requires \valid(t1+(0..n-1)) && \valid(t2+(0..n-1)) && n>0;
	ensures (\forall integer i; 0<=i<n ==> t1[i] == t2[i]) ==> \result==1;
	ensures (\exists integer i; 0<=i<n && t1[i] != t2[i]) ==> \result==0;
	assigns \nothing;
*/

int compare(int t1[], int t2[], int n){
	int i=0;
	bool diff_found = 0;
	/*@
		loop invariant 0<=i<=n;
		loop invariant (\forall integer j; 0<=j<i ==> t1[j] == t2[j]) || (i == 0);
		loop invariant !diff_found ==> (\forall integer j; 0<=j<i ==> t1[j] == t2[j]);
		loop invariant diff_found ==> (\exists integer j; 0<=j<i && t1[j] != t2[j]);
		loop assigns i, diff_found;
		loop variant n-i;
	*/
	for(i=0;i<n;i++)
	{
		if(t1[i] != t2[i])
		{
			diff_found = 1;
			return 0;
		}
	}
	return 1;
}