/*@ predicate allequ{L}(integer i, int *x, integer res) =
  @ \forall integer j; (i <= j <= res+i-1) ==> (\at(x[i], L)==\at(x[j], L));
  @*/
//Examines equality between between all elemnts in [i,i+res-1]

/*@ predicate ismax{L}(integer i, int *x, integer res,integer N) =
  @   \forall integer j; (0 < j <= N-1 && j!=i) ==> (\forall integer rp; (1 < rp < N && allequ(j,x,rp)) ==> (rp <= res));
  @*/
//Examines that res is the max res the you can get in length N
//For every r that satisfies allequ this r must be smaller-equal from res

/*@ predicate cond{L}(integer N, int *x, integer res) =
  @   \exists integer i; (0 <= i < N-res) ==> (allequ(i,x,res) && ismax(i,x,res,N));
  @*/
//For something to satisfy the given condition there must exist an integer such that for i to
// i+res-1 positions we will have equality and this will be the max length


/*@ requires N > 0;
  @ requires \valid(x + (0..N-1));
  @ ensures  cond(N, x,\result);
  @*/
int countSameConsecutive(int N, int x[]) {
	int best = 0, i = 0;
	// we try to maintain an essence of current best in order to reach total (best)
	// for that we replace N <- i+1 (to look until i array positions)
	/*@ loop invariant 0 <= i <= N;
      @ loop invariant 0 <= best <= N;
      @ loop invariant 0 < i <==> 0 < best;
      @ loop invariant (0 < best <==> allequ(i,x,best)) || (best == 0 <==> i==0) ;
      @ loop invariant (0 < best <==> ismax(i,x,best,i+1)) || (best == 0 <==> i==0);
      @ loop invariant ((0 < i < N && 0 < best) <==> cond(i+1,x,best)) || (best == 0 <==> i==0);
      @ loop assigns i, best;
      @ loop variant N-i;
     @*/
	while (i < N) {
		int j = i+1;
		// while we are inside the second loop everything allequ for j-i 
		// (starting from i) matrix positions is maintained
		/*@ loop invariant i+1 <= j <= N;
          @ loop invariant (x[j] == x[i]) ==> allequ(i,x,j-i);
          @ loop assigns j;
          @ loop variant N-j;
          @*/
		while (j < N && x[j] == x[i]) ++j;
		if (j-i > best) best = j-i;
		i = j;
	}
	return best;
}
