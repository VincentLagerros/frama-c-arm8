struct MaxAndMin{
                  int max;
                  int min;
       };
       /*@ requires size > 0 && \valid_read(a+(0..size-1));
           ensures \forall integer i ; 0 <= i < size ==> ( a[i] <= \result.max && \result.min <= a[i]  ) ;
            */
       struct MaxAndMin findMaxAndMin(int* a,int size){
                   struct MaxAndMin s;
                   struct MaxAndMin* p = &s;
                   int** q = &a;
                   p->min = (*q)[0];
                   p->max = (*q)[0];
                  int i = 0;
                 /*@ loop assigns i, s.max, s.min;
                     loop invariant *p==s && *q==a && size >0 && 
			(i<=size && (i>=0 && (\forall integer j ;0 <= j < i ==> ( a[j] <=s.max && s.min <=a[j]))));
			
                 loop variant size - i;
                 */
                while (i < size){
                           if (p->max < (*q)[i])
                                      p->max = (*q)[i];
                           if (p->min > (*q)[i])
                                      p->min = (*q) [i];
                           i = i + 1;
                 }
                 return s;
      }