//P13.1 Given a class Rectangle with instance variables width and height, provide a recursive
//getArea method. Construct a rectangle whose width is one less than the original and
//call its getArea method


function rect_area(width: int, height: int) : int
  requires 0 <= width && 0 <= height
  ensures rect_area(width, height) == width * height
{
  if width == 0 || height == 0 then 0
  else rect_area(width - 1, height) + height
}

method p_13_1_rectangle_area(width: int, height: int) returns (area: int)
  requires 0 <= width && 0 <= height
  ensures area == rect_area(width, height) // this spec is here to force AI to come up with a recursive solution
{
  
}

//P13.2 Given a class Square with instance variable width, provide a recursive getArea method.
//Construct a square whose width is one less than the original and call its getArea
//method.

// width * width = area of square
// (width - 1) * (width - 1) = width * width - 2 * width + 1 
// width * width = (width - 1) * (width - 1) + 2 * width - 1
function square_area(width: int) : int
  requires 0 <= width
  ensures square_area(width) == width * width
{
  if width == 0 then 0
  else square_area(width - 1) + 2 * width - 1
}

method p_13_2_square_area_method(width: int) returns (area: int)
  requires 0 <= width
  ensures area == square_area(width) // this spec is here to force AI to come up with a recursive solution
{
  
}

//P13.3 Write a recursive method String reverse(String text) that reverses a string. For
//example, reverse("Hello!") returns the string "!olleH". Implement a recursive solution
//by removing the first character, reversing the remaining text, and combining the two.

function reverse_string(text: seq<char>) : (ret : seq<char>)
  ensures |ret| == |text| 
  ensures forall i :: 0 <= i < |text| ==> ret[i] == text[|text| - 1 - i]
{
  if |text| == 0 then []
  else [text[|text| - 1]] + reverse_string(text[0..|text| - 1])
}

method p_13_3_reverse_string_method(text: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |text|
  ensures reversed == reverse_string(text)
  ensures forall i :: 0 <= i < |text| ==> reversed[i] == text[|text| - 1 - i] // should I get rid of this?
{
  
}

//P13.4 Redo Exercise P13.3 with a recursive helper method that reverses a substring of the
//message text.
// Todo 


//P13.5 Implement the reverse method of Exercise P13.3 as an iteration.

method p_13_5_reverse_string_iterative(text: seq<char>) returns (reversed: seq<char>)
  ensures |reversed| == |text|
  ensures forall i :: 0 <= i < |text| ==> reversed[i] == text[|text| - 1 - i]
  ensures reversed == reverse_string(text)
{
}

//P13.6 Use recursion to implement a method
//public static boolean find(String text, String str)
//that tests whether a given text contains a string. For example, find("Mississippi",
//"sip") returns true.
//Hint: If the text starts with the string you want to match, then you are done. If not,
//consider the text that you obtain by removing the first character.

function starts_with(text: seq<char>, str: seq<char>) : (b: bool)
  ensures b == (|str| <= |text| && forall i :: 0 <= i < |str| ==> text[i] == str[i])
{
  if |str| == 0 then true
  else if |text| == 0 then false
  else if text[0] == str[0] then starts_with(text[1..], str[1..])
  else false
}

method p_13_6_find_string(text: seq<char>, str: seq<char>) returns (found: bool)
  ensures found == (exists i :: 0 <= i <= |text| - |str| && starts_with(text[i..], str) == true)
{
}


//•• P13.7 Use recursion to implement a method
//public static int indexOf(String text, String str)
//that returns the starting position of the first substring of the text that matches str.
//Return –1 if str is not a substring of the text.
//For example, s.indexOf("Mississippi", "sip") returns 6.
//Hint: This is a bit trickier than Exercise P13.6, because you must keep track of how
//far the match is from the beginning of the text. Make that value a parameter variable
//of a helper method

function find_index(text: seq<char>, str: seq<char>, index: int) : (ret : int)
   ensures starts_with(text, str) ==> ret == index 
{
  if |text| < |str| then -1
  else if starts_with(text, str) then index
  else find_index(text[1..], str, index + 1)
}


method p_13_7_index_of_string(text: seq<char>, str: seq<char>) returns (index: int)
  ensures index == find_index(text, str, 0)
{
}

// P13.8 Using recursion, find the largest element in an array.

function find_largest(arr: seq<int>) : int
  requires |arr| >= 1
  ensures forall x :: x in arr ==> find_largest(arr) >= x
{
  if |arr| == 1 then arr[0]
  else 
      assert arr == [arr[0]] + arr[1..];
      var sub_largest := find_largest(arr[1..]) ;
      if arr[0] >= sub_largest then arr[0] else sub_largest
}

method p_13_8_largest_in_array(arr: seq<int>) returns (largest: int)
  requires |arr| >= 1
  ensures largest == find_largest(arr)
{
}

//P13.9 Using recursion, compute the sum of all values in an array.

function sum_array(arr: seq<int>) : int
  ensures sum_array(arr) == (if |arr| == 0 then 0 else arr[0] + sum_array(arr[1..]))
{
  if |arr| == 0 then 0
  else arr[0] + sum_array(arr[1..])
}

method p_13_9_sum_of_array(arr: seq<int>) returns (sum: int)
  ensures sum == sum_array(arr)
{
}

//P13.10 Using recursion, compute the area of a polygon. Cut off a
//triangle and use the fact that a triangle with corners (x1 , y1),
// (x2, y2 ), (x3, y3) has area
// |x1(y2 – y3) + x2(y3 – y1) + x3(y1 – y2)| / 2

// this assumes that polygon points are given in order either clockwise or counterclockwise
function polygon_area(points: seq<(real, real)>) : real
  requires |points| >= 3
  ensures polygon_area(points) >= 0.0
{
  if |points| == 3 then 
    var (x1, y1) := points[0];
    var (x2, y2) := points[1];
    var (x3, y3) := points[2];
    var sign : real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    if sign < 0.0 then -sign / 2.0 else sign / 2.0 as real 
  else 
    var (x1, y1) := points[0];
    var (x2, y2) := points[1];
    var (x3, y3) := points[2];
    var sign : real := x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2);
    var triangle_area := if sign < 0.0 then -sign / 2.0 else sign / 2.0 as real;
    triangle_area + polygon_area([points[0]] + points[2..])
}


method p_13_10_compute_polygon_area(points: seq<(real, real)>) returns (area: real)
  requires |points| >= 3
  ensures area == polygon_area(points)
{
}