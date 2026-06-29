/*@  ensures  (\result >= x && \result >=y) ; */

int maxint (int x, int y) { 
  return (x > y) ? x : y; 
}

