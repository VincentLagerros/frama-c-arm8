#include <stdio.h>
#include <limits.h>
#include <stddef.h>

#define MAX_SIZE 1000 // Define a maximum size for the array

/*@ requires validSize: MAX_SIZE > size > 0 ;
    requires validArr: \valid_read(arr + (0 .. size - 1)) ;
    assigns \nothing ;
    ensures largest: \forall integer i; 0 <= i < size ==> \result >= arr[i] ;
    ensures existsInArr: \exists integer i; 0 <= i < size && arr[i] == \result ;
    */
int arrayMax(int* arr, size_t size) {
    int result = arr[0];
    size_t i = 0;

    /*@  loop invariant largest: \forall integer k; 0 <= k < i ==> result >= arr[k];
         loop invariant pos: 0 <= i <= size;
         loop invariant existsInArr: \exists integer k; 0 <= k < size && arr[k] == result ;
         loop assigns i, result;
         loop variant size - i;
         */
    while (i < size) {
        if (arr[i] > result)
            result = arr[i];

        i++;
    }

    return result;
}
