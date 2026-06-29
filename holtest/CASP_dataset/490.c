typedef enum { Max, Min } kind;
int extremum (kind k, int x, int y) {
  return ((k == Max ? x > y : x < y) ? x: y);
}
/*@ requires k == Max || k == Min;
    assigns 
othing;
    ensures esult == x || esult == y;
    behavior is_max:
      assumes k == Max;
      ensures esult >= x && esult >= y;
    behavior is_min:
      assumes k == Min;
      ensures esult <= x && esult <= y;
    complete behaviors is_max, is_min;
    disjoint behaviors is_max, is_min;
    complete behaviors;
    disjoint behaviors;
*/
int extremum (kind k, int x, int y);