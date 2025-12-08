
//p6.1 Write a program that initializes an array with ten random integers and then prints
//four lines of output, containing
//• Every element at an even index.
//• Every even element.
//• All elements in reverse order.
// • Only the first and last element.

method p6_1_process_array(arr: seq<int>) returns (even_indexed: seq<int>, even_elements: seq<int>, reversed: seq<int>, first_and_last: seq<int>)
  requires |arr| == 10
  ensures even_indexed == [arr[0], arr[2], arr[4], arr[6], arr[8]]
  ensures forall i :: 0 <= i < 5 ==> even_indexed[i] == arr[2 * i]
  ensures forall i :: 0 <= i < |arr| ==> arr[i] % 2 == 0 ==> exists j :: 0 <= j < |even_elements| && even_elements[j] == arr[i] // unique existence? 
  ensures |reversed| == |arr|
  ensures forall i :: 0 <= i < |reversed| ==> reversed[i] == arr[|arr| - 1 - i]
  ensures first_and_last == [arr[0], arr[|arr| - 1]]
{  
}

//p6.2 Write array methods that carry out the following tasks for an array of integers. For
//each method, provide a test program.
//a. Swap the first and last elements in the array.
//b. Shift all elements by one to the right and move the last element into the first
//position. For example, 1 4 9 16 25 would be transformed into 25 1 4 9 16.
//c. Replace all even elements with 0.
//d. Replace each element except the first and last by the larger of its two neighbors.
//e. Remove the middle element if the array length is odd, or the middle two
//elements if the length is even.
//f. Move all even elements to the front, otherwise preserving the order of the
//elements.
//g. Return the second-largest element in the array.
//h. Return true if the array is currently sorted in increasing order.
//i. Return true if the array contains two adjacent duplicate elements.
//j. Return true if the array contains duplicate elements (which need not be
//adjacent).

method p6_2_a_swap_first_last(arr: seq<int>) returns (result: seq<int>)
  requires |arr| >= 2
  ensures |result| == |arr|
  ensures result[0] == arr[|arr| - 1]
  ensures result[|arr| - 1] == arr[0]
  ensures forall i :: 1 <= i < |arr| - 1 ==> result[i] == arr[i]
{  
}

method p6_2_b_shift_right(arr: seq<int>) returns (result: seq<int>)
  requires |arr| >= 1
  ensures |result| == |arr|
  ensures result[0] == arr[|arr| - 1]
  ensures forall i :: 1 <= i < |arr| ==> result[i] == arr[i - 1]
{  
}

method p6_2_c_replace_even_with_zero(arr: seq<int>) returns (result: seq<int>)
  ensures |result| == |arr|
  ensures forall i :: 0 <= i < |arr| ==> (arr[i] % 2 == 0 ==> result[i] == 0) && (arr[i] % 2 != 0 ==> result[i] == arr[i])
{  
}

method p6_2_d_replace_with_larger_neighbor(arr: seq<int>) returns (result: seq<int>)
  requires |arr| >= 3
  ensures |result| == |arr|
  ensures result[0] == arr[0]
  ensures result[|arr| - 1] == arr[|arr| - 1]
  ensures forall i :: 1 <= i < |arr| - 1 ==> result[i] == if arr[i - 1] >= arr[i + 1] then arr[i - 1] else arr[i + 1]
{  
}


method p6_2_e_remove_middle(arr: seq<int>) returns (result: seq<int>)
  requires |arr| >= 1
  ensures |result| == if |arr| % 2 == 1 then |arr| - 1 else |arr| - 2
  ensures |arr| % 2 == 1 ==> forall i :: 0 <= i < |arr| / 2 ==> result[i] == arr[i] && forall j :: |arr| / 2 <= j < |result| ==> result[j] == arr[j + 1]
  ensures |arr| % 2 == 0 ==> forall i :: 0 <= i < |arr| / 2 - 1 ==> result[i] == arr[i] && forall j :: |arr| / 2 - 1 <= j < |result| ==> result[j] == arr[j + 2]
{  
}

method p6_2_f_move_even_to_front(arr: seq<int>) returns (result: seq<int>)
  ensures |result| == |arr|
  ensures forall i, j :: 0 <= i < j < |result| && result[i] % 2 == 0 && result[j] % 2 != 0
  ensures forall i :: 0 <= i < |arr| ==> exists j :: 0 <= j < |result| && arr[i] == result[j]
{  
}


/*
function find_largest(arr: seq<int>) : int
  requires |arr| >= 1
  ensures forall x :: x in arr ==> x <= find_largest(arr) 
{
  if |arr| == 1 then arr[0]
  else 
    assert 2 <= |arr|;
    var rest_largest := find_largest(arr[1..]);
    assert 1 <= |rest_largest|; 
    if arr[0] >= rest_largest then arr[0] else rest_largest
}


method p6_2_g_second_largest(arr: seq<int>) returns (second_largest: int)
  requires |arr| >= 2
  ensures exists x :: x in arr && x < second_largest 
{  
}
*/

method p6_2_h_is_sorted(arr: seq<int>) returns (isSorted: bool)
  ensures isSorted == (forall i :: 0 <= i < |arr| - 1 ==> arr[i] <= arr[i + 1])
{  
}

function count_adajacent_duplicates(arr: seq<int>, i: int) : int
  requires 0 <= i < |arr| - 1
  decreases |arr| - i
{
  if i + 1 == |arr| - 1 then if arr[i] == arr[i + 1] then 1 else 0
  else if arr[i] == arr[i + 1] then 1 + count_adajacent_duplicates(arr, i + 1)
  else count_adajacent_duplicates(arr, i + 1)
}


method p6_2_i_has_adjacent_duplicates(arr: seq<int>) returns (hasDuplicates: bool)
  requires |arr| >= 2
  ensures hasDuplicates == (exists i :: 0 <= i < |arr| - 1 && arr[i] == arr[i + 1])
  ensures 1 <= count_adajacent_duplicates(arr, 0) ==> hasDuplicates == true
{  
}

method p6_2_j_has_duplicates(arr: seq<int>) returns (hasDuplicates: bool)
  requires |arr| >= 2
  ensures hasDuplicates == (exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j])
{  
}


//p6.3 Modify the LargestInArray.java program in Section 6.3 to mark both the smallest and
//the largest elements.
// Todo 


//p6.4 Write a method sumWithoutSmallest that computes the sum of an array of values,
//except for the smallest one, in a single loop. In the loop, update the sum and the
//smallest value. After the loop, return the difference.

function sum_array(arr: seq<int>) : int
  ensures forall i :: 0 <= i < |arr| ==> arr[i] >= 0 ==> sum_array(arr) >= 0
{
  if |arr| == 0 then 0
  else arr[0] + sum_array(arr[1..])
}

function find_smallest(arr: seq<int>) : (ret : int)
  requires |arr| >= 1
  ensures forall x :: x in arr ==> ret <= x 
{
  if |arr| == 1 then arr[0]
  else 
    assert 2 <= |arr|;
    var rest_smallest := find_smallest(arr[1..]);
    var ret : int := if arr[0] <= rest_smallest then arr[0] else rest_smallest; 
    assert ret == if arr[0] <= rest_smallest then arr[0] else rest_smallest;
    ret 
}


method p6_4_sum_without_smallest(arr: seq<int>) returns (sum: int)
  requires |arr| >= 1
  ensures sum == sum_array(arr) - find_smallest(arr)
{  
}


//p6.5 Write a method public static void removeMin that removes the minimum value from a
//partially filled array without calling other methods.
// Todo 

//p6.6 Compute the alternating sum of all elements in an array. For example, if your pro-
//gram reads the input
//1 4 9 16 9 7 4 9 11
//then it computes
//1 – 4 + 9 – 16 + 9 – 7 + 4 – 9 + 11 = –2

function sum_arrray(arr : seq<int>, i : int) : int
{
  if |arr| == 0 then 0
  else arr[0] * i + sum_arrray(arr[1..], i * -1)
}

method p6_6_alternating_sum(arr: seq<int>) returns (alt_sum: int)
 ensures alt_sum == sum_arrray(arr, 1)
{
}


// P6.7 Write a method that reverses the sequence of elements in an array. For example, if
//you call the method with the array
//1 4 9 16 9 7 4 9 11
//then the array is changed to
//11 9 4 7 9 16 9 4 1

method p6_7_reverse_array(arr: seq<int>) returns (reversed: seq<int>)
  ensures |reversed| == |arr|
  ensures forall i :: 0 <= i < |reversed| ==> reversed[i] == arr[|arr| - 1 - i]
{  
}

// p6.8 Write a method that implements the algorithm developed in Section 6.6.
// Todo

//p6.9 Write a method
//public static boolean equals(int[] a, int[] b)
// that checks whether two arrays have the same elements in the same order.

method p6_9_arrays_equal(arr1: seq<int>, arr2: seq<int>) returns (areEqual: bool)
  ensures areEqual == (|arr1| == |arr2| && forall i :: 0 <= i < |arr1| ==> arr1[i] == arr2[i])
{  
}

// p6.10Write a method
//public static boolean sameSet(int[] a, int[] b)
//that checks whether two arrays have the same elements in some order, ignoring
//duplicates. For example, the two arrays
//1 4 9 16 9 7 4 9 11
//and
//11 11 7 9 16 4 1
//would be considered identical. You will probably need one or more helper methods.

function array_to_set(arr: seq<int>) : set<int>
{
  if |arr| == 0 then {}
  else {arr[0]} + array_to_set(arr[1..])
}

// https://dafny.org/latest/OnlineTutorial/Sets
method p6_10_same_set(arr1: seq<int>, arr2: seq<int>) returns (areSameSet: bool)
  ensures areSameSet == (array_to_set(arr1) == array_to_set(arr2))
{  
}


