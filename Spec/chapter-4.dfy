
//Write programs with loops that compute
//a. The sum of all even numbers between 2 and 100 (inclusive).
//b. The sum of all squares between 1 and 100 (inclusive).
//c. All powers of 2 from 2^0 up to 2^20 .
//d. The sum of all odd numbers between a and b (inclusive), where a and b are inputs.
//e. The sum of all odd digits of an input. (For example, if the input is 32677, the sum would be 3 + 7 + 7 = 17.)

method p4_1_a_sum_even_numbers() returns (sum: int)
ensures sum == 2550
{
  
}

method p4_1_b_sum_squares() returns (sum: int)
ensures sum == 338350
{
}


function pow(base: int, exp: int): int
  requires  0 <= exp
  decreases exp
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}

//Dafny does not have pow function 
method p4_1_c_powers_of_two() returns (powers: seq<int>)
ensures |powers| == 21
ensures forall i :: 0 <= i < |powers| ==> powers[i] == pow(2, i)
{
  
}


function pow_nat(base: int, exp: nat): int 
decreases exp
{
  match exp
  case 0 => 1
  case _ => base * pow_nat(base, exp - 1)
}

method p4_1_c_powers_of_two_array() returns (powers: array<int>)
ensures powers.Length == 21
ensures forall i :: 0 <= i < powers.Length ==> powers[i] == pow_nat(2, i)
{
  
}



function sum_odd(a: int, b: int): int
decreases b - a
{
  if a > b then 0
  else if a % 2 == 1 then a + sum_odd(a + 1, b)
  else sum_odd(a + 1, b)
}

method p4_1_d_sum_odd_numbers(a: int, b: int) returns (sum: int)
ensures sum == sum_odd(a, b)  // closed formula for addition of odd numbers between a and b?? 
{  
}



function sum_odd_digits(n: int): int
decreases n
{
  if n % 10 < 10 then 
    if n % 10 % 2 == 1 then n % 10 else 0
  else if n % 10 % 2 == 1 then n % 10 + sum_odd_digits(n / 10)
  else sum_odd_digits(n / 10)
}


method p4_1_e_sum_odd_digits(n: int) returns (sum: int)
ensures sum >= 0
ensures sum == sum_odd_digits(n)
{  
}



//p4.2 Write programs that read a sequence of integer inputs and print
//a. The smallest and largest of the inputs.
//b. The number of even and odd inputs.
//c. Cumulative totals. For example, if the input is 1 7 2 9, the program should print
//1 8 10 19.
//d. All adjacent duplicates. For example, if the input is 1 3 3 4 5 5 6 6 6 2, the
// program should print 3 5 6


method p4_2_a_min_max(inputs: seq<int>) returns (min: int, max: int)
requires 0 < |inputs|
ensures forall x :: x in inputs ==> min <= x
ensures forall x :: x in inputs ==> max >= x
ensures exists x :: x in inputs && min == x
ensures exists x :: x in inputs && max == x
{  
}

method p4_2_a_min_max_array(inputs: array<int>) returns (min: int, max: int)
requires 0 < inputs.Length
ensures forall i :: 0 <= i < inputs.Length ==> min <= inputs[i]
ensures forall i :: 0 <= i < inputs.Length ==> max >= inputs[i]
ensures exists i :: 0 <= i < inputs.Length && min == inputs[i]
ensures exists i :: 0 <= i < inputs.Length && max == inputs[i]
{  
}


method p4_2_b_count_even_odd(inputs: seq<int>) returns (even_count: int, odd_count: int)
ensures even_count + odd_count == |inputs|
ensures forall x :: x in inputs && x % 2 == 0 ==> even_count >= 1
ensures forall x :: x in inputs && x % 2 == 1 ==> odd_count >= 1
ensures (forall x :: x in inputs ==> x % 2 == 0) ==> odd_count == 0 // all inputs are even
ensures (forall x :: x in inputs ==> x % 2 == 1) ==> even_count == 0 // all inputs are odd
{  
}

method p4_2_b_count_even_odd_array(inputs: array<int>) returns (even_count: int, odd_count: int)
ensures even_count + odd_count == inputs.Length
ensures forall i :: 0 <= i < inputs.Length && inputs[i] % 2 == 0 ==> even_count >= 1
ensures forall i :: 0 <= i < inputs.Length && inputs[i] % 2 == 1 ==> odd_count >= 1
ensures (forall i :: 0 <= i < inputs.Length ==> inputs[i] % 2 == 0) ==> odd_count == 0 // all inputs are even
ensures (forall i :: 0 <= i < inputs.Length ==> inputs[i] % 2 == 1) ==> even_count == 0 // all inputs are odd
{  
}


method p4_2_c_cumulative_totals(inputs: seq<int>) returns (totals: seq<int>)
requires 0 < |inputs|
ensures |totals| == |inputs|
ensures forall i :: 0 <= i < |inputs| ==> totals[i] == (if i == 0 then inputs[0] else totals[i - 1] + inputs[i])
{  
}


method p4_2_c_cumulative_totals_array(inputs: array<int>) returns (totals: array<int>)
requires 0 < inputs.Length
ensures totals.Length == inputs.Length
ensures forall i :: 0 <= i < inputs.Length ==> totals[i] == (if i == 0 then inputs[0] else totals[i - 1] + inputs[i])
{  
}


function contiguous_duplicates(inputs: seq<int>, i : int, j : int, d : int) : (b : bool) 
  requires 0 <= i < j < |inputs|
  decreases j - i
{
  if i + 1 == j then inputs[i] == inputs[j] == d
  else if inputs[i] == d then contiguous_duplicates(inputs, i + 1, j, d)
  else false
}


method p4_2_d_adjacent_duplicates(inputs: seq<int>) returns (duplicates: seq<int>)
ensures forall d :: d in duplicates ==> d in inputs
ensures forall i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] ==> inputs[i] in duplicates
ensures forall d :: d in duplicates ==> exists i :: 0 <= i < |inputs| - 1 && inputs[i] == inputs[i + 1] && inputs[i] == d
ensures forall d :: d in duplicates ==> exists i, j :: 0 <= i < j < |inputs| && contiguous_duplicates(inputs, i, j, d) == true 
{  
}

function contiguous_duplicates_array(inputs: array<int>, i : int, j : int, d : int) : (b : bool) 
  requires 0 <= i < j < inputs.Length
  decreases j - i
{
  if i + 1 == j then inputs[i] == inputs[j] == d
  else if inputs[i] == d then contiguous_duplicates_array(inputs, i + 1, j, d)
  else false
}


method p4_2_d_adjacent_duplicates_array(inputs: array<int>) returns (duplicates: array<int>)
ensures forall d :: d in duplicates[..] ==> d in inputs[..]
ensures forall i :: 0 <= i < inputs.Length - 1 && inputs[i] == inputs[i + 1] ==> inputs[i] in duplicates[..]
ensures forall d :: d in duplicates[..] ==> exists i :: 0 <= i < inputs.Length - 1 && inputs[i] == inputs[i + 1] && inputs[i] == d
ensures forall d :: d in duplicates[..] ==> exists i, j :: 0 <= i < j < inputs.Length && contiguous_duplicates_array(inputs, i, j, d) == true 
{  
}


//Write programs that read a line of input as a string and print
//a. Only the uppercase letters in the string.
//b. Every second letter of the string.
//c. The string, with all vowels replaced by an underscore.
//d. The number of vowels in the string.
// e. The positions of all vowels in the string.


method p4_3_a_extract_uppercase(s: string) returns (uppercase: string)
ensures forall c :: c in uppercase ==> 'A' <= c <= 'Z'
ensures forall c :: c in s && 'A' <= c <= 'Z' ==> c in uppercase
{  
} 

method p4_3_b_every_second_letter(s: string) returns (result: string)
ensures |result| * 2 == |s| || |result| * 2 + 1 == |s|
ensures forall i :: 0 <= i < |result| ==> result[i] == s[2 * i]
{  
}

method p4_3_c_replace_vowels(s: string) returns (result: string)
ensures |result| == |s|
ensures forall i :: 0 <= i < |s| ==> (if s[i] in ['a','e','i','o','u','A','E','I','O','U'] then result[i] == '_' else result[i] == s[i])
{  
}

method p4_3_d_count_vowels(s: string) returns (count: int)
ensures count >= 0
ensures forall c :: c in s && c in ['a','e','i','o','u','A','E','I','O','U'] ==> count >= 1
ensures (forall c :: c in s ==> c !in ['a','e','i','o','u','A','E','I','O','U']) ==> count == 0
{  
}

method p4_3_e_positions_of_vowels(s: string) returns (positions: seq<int>)
ensures forall p :: p in positions ==> 0 <= p < |s| && s[p] in ['a','e','i','o','u','A','E','I','O','U']
ensures forall i :: 0 <= i < |s| && s[i] in ['a','e','i','o','u','A','E','I','O','U'] ==> i in positions
{  
} 

method p4_3_e_positions_of_vowels_array(s: string) returns (positions: array<int>)
ensures forall p :: p in positions[..] ==> 0 <= p < |s| && s[p] in ['a','e','i','o','u','A','E','I','O','U']
ensures forall i :: 0 <= i < |s| && s[i] in ['a','e','i','o','u','A','E','I','O','U'] ==> i in positions[..]
{  
} 

// p4.4 Complete the program in How To 4.1 on page 169. Your program should read twelve
// temperature values and print the month with the highest temperature.


// p4.5
//Write a program that reads a set of floatingpoint values. Ask the user to enter the
//values, then print
//• the average of the values.
//• the smallest of the values.
//• the largest of the values.
// • the range, that is the difference between the smallest and largest.

function sum(values: seq<real>): real
{
  if |values| == 0 then 0.0
  else values[0] + sum(values[1..])
}

method p4_5_analyze_floats(values: seq<real>) returns (average: real, min: real, max: real, range: real)
requires 0 < |values|
ensures average == (sum(values) / |values| as real)
ensures forall v :: v in values ==> min <= v
ensures forall v :: v in values ==> max >= v
ensures range == max - min
ensures exists v :: v in values && min == v
ensures exists v :: v in values && max == v
{  
}

function sum_array(values: array<real>, i: nat): real
  requires i <= values.Length
  decreases values.Length - i
{
  if i == values.Length then 0.0
  else values[i] + sum_array(values, i + 1)
}



method p4_5_analyze_floats_array(values: array<real>) returns (average: real, min: real, max: real, range: real)
requires 0 < values.Length
ensures average == (sum_array(values, 0) / values.Length as real)
ensures forall v :: v in values[..] ==> min <= v
ensures forall v :: v in values[..] ==> max >= v
ensures range == max - min
ensures exists v :: v in values[..] && min == v
ensures exists v :: v in values[..] && max == v
{  
}



//4.6 Translate the following pseudocode for finding the minimum value from a set of
// inputs into a Java program.
// Set a Boolean variable "first" to true.
//While another value has been read successfully
//If first is true
//Set the minimum to the value.
//Set first to false.
//Else if the value is less than the minimum
//Set the minimum to the value.
//Print the minimum.

method p4_6_find_minimum(inputs: seq<int>) returns (min: int)
requires 0 < |inputs|
ensures forall x :: x in inputs ==> min <= x
ensures exists x :: x in inputs && min == x
{  
}

method p4_6_find_minimum_array(inputs: array<int>) returns (min: int)
requires 0 < inputs.Length
ensures forall x :: x in inputs[..] ==> min <= x
ensures exists x :: x in inputs[..] && min == x
{  
}

//4.7 Translate the following pseudocode for randomly permuting the characters in a
// string into a Java program.
//Read a word.
//Repeat word.length() times
//Pick a random position i in the word, but not the last position.
//Pick a random position j > i in the word.
//Swap the letters at positions j and i.
//Print the word.

method p4_7_permute_string(s: string) returns (permuted: string)
ensures |permuted| == |s|
ensures forall c :: c in s ==> c in permuted
ensures forall c :: c in permuted ==> c in s
{  
}

// 4.8 Write a program that reads a word and prints each character of the word on a sepa
// rate line.


method p4_8_print_characters(s: string) returns (chars: string)
ensures |chars| == 2 * |s|
ensures forall i :: 0 <= i < |s| ==> i % 2 == 1 ==> chars[i] == '\n'
ensures forall i :: 0 <= i < |s| ==> i % 2 == 0 ==> chars[i] == s[i / 2]
{  
}


// 4.9 Write a program that reads a word and prints the word in reverse. 
method p4_9_reverse_string(s: string) returns (reversed: string)
ensures |reversed| == |s|
ensures forall i :: 0 <= i < |s| ==> reversed[i] == s[|s| - 1 - i]
{  
}

// 4. 10 Write a program that reads a word and prints the number of vowels in the word.
method p4_10_count_vowels(s: string) returns (count: int)
ensures 0 <= count
ensures forall c :: c in s ==> c in ['a','e','i','o','u','A','E','I','O','U'] ==> count >= 1
ensures (forall c :: c in s ==> c !in ['a','e','i','o','u','A','E','I','O','U']) ==> count == 0
{  
}
