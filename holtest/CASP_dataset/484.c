int remove_copy_array (int* a, int length, int* dest, int value )
{
    int i_a = 0;
    int i_dest = 0;

    /*@
    loop invariant 0 <= i_a <= length;
    loop invariant i_dest <= i_a;
    loop invariant 0 <= i_dest <= length;
    loop invariant \forall integer k; 0 <= k < i_dest ==> dest[k] != value;
    loop invariant i_dest == predicate_remove_copy{Pre,Here}(a, dest, i_a-1, i_dest-1, value);
    */
    for ( ; i_a != length; ++i_a)
        if (a[i_a] != value)
        {
            dest[i_dest] = a[i_a];
            /*@assert
            i_dest+1==predicate_remove_copy{Pre,Here}(a,dest,i_a,i_dest,value);
            */
            ++i_dest;
        }

    return i_dest;
}