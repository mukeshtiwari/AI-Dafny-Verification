//P14.1 Modify the selection sort algorithm to sort an array of integers in descending order.

method p14_1_selection_sort_desc(arr: array<int>) returns (sorted: array<int>)
  requires arr.Length >= 0
  ensures sorted.Length == arr.Length
  ensures forall i, j :: 0 <= i < j < arr.Length ==> sorted[i] >= sorted[j]
{
}

//P14.2 Modify the selection sort algorithm to sort an array of coins by their value. 
// Todo 

//P14.3 Write a program that automatically generates the table of sample run times for the
//selection sort algorithm. The program should ask for the smallest and largest value
//of n and the number of measurements and then make all sample runs.

// Todo

//P14.4 Modify the merge sort algorithm to sort an array of strings in lexicographic order.

method p14_4_merge_sort_strings(arr: array<string>) returns (sorted: array<string>)
  requires arr.Length >= 0
  ensures sorted.Length == arr.Length
  ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < sorted.Length && arr[i] == sorted[j]
{
}


//P14.5 Write a telephone lookup program. Read a data set of 1,000 names and telephone
//numbers from a file that contains the numbers in random order. Handle lookups
//by name and also reverse lookups by phone number. Use a binary search for both
//lookups.

//Todo

//P14.6 Implement a program that measures the performance of the insertion sort algorithm
//described in Special Topic 14.2.
//Todo

//P14.7 Implement the bubble sort algorithm described in Exercise R14.19.

//https://github.com/deepakn97/CS292C/blob/716358318956d2280c0271695eb99cf2cba40bc4/solutions/hw1/bubble_sort.dfy#L38
ghost predicate Ordered(a: array<int>, start: int, end: int)
  reads a
  requires a.Length >= 1
{
  forall i: int, j: int :: 0 <= start <= i <= j <= end < a.Length ==> a[i] <= a[j]
}

// If the array is partitioned at i, check that all the elements in right side partition are bigger than elements in left side partition. Bubbling the larger elements towards the end of array is a bubble sort property.
ghost predicate bubble(a: array<int>, i: int)
  reads a
  requires a.Length >= 1
{
  forall j, k: int :: 0 <= j <= i < k < a.Length ==> a[j] <= a[k]
}

// To check if the elements and their counts in the array are preserved.
twostate predicate Preserved(a: array<int>)
  reads a
{
  multiset(a[..]) == multiset(old(a[..]))
}

function permutation(a: array<int>, b : array<int>) : bool
  requires 0 <= a.Length
  requires 0 <= a.Length
  reads a, b
{
  if a.Length != b.Length then false
  else multiset(a[..]) == multiset(b[..])
}

method p14_7_bubble_sort(arr: array<int>) returns (sorted: array<int>)
  ensures Ordered(arr, 0, arr.Length-1)
  ensures Preserved(arr)
  requires arr.Length >= 0
  ensures sorted.Length == arr.Length
  ensures forall i, j :: 0 <= i < j < sorted.Length ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < arr.Length ==> exists j :: 0 <= j < sorted.Length && arr[i] == sorted[j]
{
}

