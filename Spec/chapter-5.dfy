
//p5.1 Write the following methods and provide a program to test them. 
// a. double smallest(double x, double y, double z), returning the smallest of the
// arguments

method p5_1_a_smallest(x: real, y: real, z: real) returns (smallest: real)
ensures smallest <= x && smallest <= y && smallest <= z
ensures smallest == x || smallest == y || smallest == z
{
}


//b. double average(double x, double y, double z), returning the average of the
// arguments
method p5_1_b_average(x: real, y: real, z: real) returns (average: real)
ensures average == (x + y + z) / 3.0
{
}

// p5.2 Write the following methods and provide a program to test them.
// a. boolean allTheSame(double x, double y, double z), returning true if the arguments
// are all the same

method p5_2_a_allTheSame(x: real, y: real, z: real) returns (allSame: bool)
ensures allSame == (x == y && y == z)
{
}

// b. boolean allDifferent(double x, double y, double z), returning true if the argu-
// ments are all different

method p5_2_b_allDifferent(x: real, y: real, z: real) returns (allDiff: bool)
ensures allDiff == (x != y && y != z && x != z)
{
}
// c. boolean sorted(double x, double y, double z), returning true if the arguments are
// sorted, with the smallest one coming first

method p5_2_c_sorted(x: real, y: real, z: real) returns (isSorted: bool)
ensures isSorted == (x <= y && y <= z)
{
}

function intToSeq(n: int) : seq<int>
  requires n >= 0
  ensures forall d :: d in intToSeq(n) ==> 0 <= d < 10
{
  if n < 10 then [n]
  else intToSeq(n / 10) + [n % 10]
}


function pow(base: int, exp: int) : int
  requires exp >= 0
{
  if exp == 0 then 1
  else base * pow(base, exp - 1)
}

// p5.3 Write the following methods.
// int firstDigit(int n), returning the first digit of the argument
method p5_3_firstDigit(n: int) returns (first: int)
requires 0 <= n 
ensures 0 <= first < 10
ensures intToSeq(n)[0] == first // This could be strengthned 
ensures forall d :: d in intToSeq(n) ==> 0 <= d < 10
{
}


// p5.4 Write a method
// public static String middle(String str)
// that returns a string containing the middle character in str if the length of str is odd,
// or the two middle characters if the length is even. For example, middle("middle")
//returns "dd".

method p5_4_middle(str: seq<char>) returns (middleStr: seq<char>)
requires 0 < |str|
ensures if |str| % 2 == 1 then |middleStr| == 1 else |middleStr| == 2
ensures if |str| % 2 == 1 then middleStr[0] == str[|str| / 2] else middleStr == str[|str| / 2 - 1 .. |str| / 2 + 1]
{
} 

method p5_4_middle_array(str: array<char>) returns (middleStr: array<char>)
requires 0 < str.Length
ensures if str.Length % 2 == 1 then middleStr.Length == 1 else middleStr.Length == 2
ensures if str.Length % 2 == 1 then middleStr[0] == str[str.Length / 2] else middleStr[..] == str[str.Length / 2 - 1 .. str.Length / 2 + 1]
{
} 

// p5.5 Write a method
//public static String repeat(String str, int n)
//that returns the string str repeated n times. For example, repeat("ho", 3) returns
//"hohoho"

method p5_5_repeat(str: seq<char>, n: int) returns (repeatedStr: seq<char>)
requires n >= 0
ensures |repeatedStr| == n * |str|
ensures forall i :: 0 <= i < n ==> repeatedStr[i * |str| .. (i + 1) * |str|] == str
{
}

method p5_5_repeat_array(str: array<char>, n: int) returns (repeatedStr: array<char>)
requires n >= 0
ensures repeatedStr.Length == n * str.Length
ensures forall i :: 0 <= i < n ==> repeatedStr[i * str.Length .. (i + 1) * str.Length] == str[..]
{
}

// p5.6 Write a method
//Write a method
//public static int countVowels(String str)
//that returns a count of all vowels in the string str. Vowels are the letters a, e, i, o, and
//u, and their uppercase variants.

method p5_6_countVowels(str: seq<char>) returns (vowelCount: int)
ensures vowelCount >= 0
ensures vowelCount <= |str|
ensures (forall c :: c in str ==> (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')) ==> vowelCount == |str|
ensures (forall c :: c in str ==> !(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')) ==> vowelCount == 0
{
}

method p5_6_countVowels_array(str: array<char>) returns (vowelCount: int)
ensures vowelCount >= 0
ensures vowelCount <= str.Length
ensures (forall c :: c in str[..] ==> (c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')) ==> vowelCount == str.Length
ensures (forall c :: c in str[..] ==> !(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U')) ==> vowelCount == 0
{
}

// p5.7 Write a method
// Write a method
// public static int countWords(String str)
// that returns a count of all words in the string str. Words are separated by spaces. For
// example, countWords("Mary had a little lamb") should return 5.

function count_space(str: seq<char>) : int
{
  if |str| == 0 then 0
  else if str[0] == ' ' then 1 + count_space(str[1..])
  else count_space(str[1..])
}


method p5_7_countWords(str: seq<char>) returns (wordCount: int)
ensures wordCount >= 0
ensures if |str| == 0 then wordCount == 0 else wordCount >= 1
ensures wordCount == count_space(str) + 1
{
}

// this is probably a better spec
// it checks if i is the start of a word or not. 
function is_word_start(str: seq<char>, i: int): bool
{
  0 <= i < |str| &&
  str[i] != ' ' &&
  (i == 0 || str[i - 1] == ' ')
}

// This one builds a set of all the indices that are the start of a word and checks that the word count is the size of that set.
// For example, for "Mary had a little lamb", the set of indices are {0, 5, 9, 11, 18} (hopefully, my counting is correct) and the word count is 5.
function count_word_spec(str: seq<char>): nat
{
  |set i:nat | 0 <= i < |str| && is_word_start(str, i) :: i|
}

method p5_7_countWords_better_spec(str: seq<char>) returns (wordCount: nat)
  ensures wordCount == count_word_spec(str)
  ensures wordCount <= |str|
  ensures |str| == 0 ==> wordCount == 0
  ensures (forall i :: 0 <= i < |str| ==> str[i] != ' ') ==> wordCount == (if |str| == 0 then 0 else 1) 
  ensures (exists i :: 0 <= i < |str| && is_word_start(str, i)) ==> 1 <= wordCount 
  ensures 1 <= wordCount ==> (exists i :: 0 <= i < |str| && is_word_start(str, i)) // if there is at least one word, then there is at least one index that is the start of a word
{
  // implementation
}

// array version of the above spec 
function is_word_start_array(str: array<char>, i: int) : bool
requires 0 <= i < str.Length
reads str 
{
  0 <= i < str.Length &&
  str[i] != ' ' &&
  (i == 0 || str[i - 1] == ' ')
}

function count_word_spec_array(str: array<char>): nat
reads str
{
  |set i:nat | 0 <= i < str.Length && is_word_start_array(str, i) :: i|
}

method p5_7_countWords_better_spec_array(str: array<char>) returns (wordCount: nat)
  ensures wordCount == count_word_spec_array(str)
  ensures wordCount <= str.Length
  ensures str.Length == 0 ==> wordCount == 0
  ensures (forall i :: 0 <= i < str.Length ==> str[i] != ' ') ==> wordCount == (if str.Length == 0 then 0 else 1) 
  ensures (exists i :: 0 <= i < str.Length && is_word_start_array(str, i)) ==> 1 <= wordCount 
  ensures 1 <= wordCount ==> (exists i :: 0 <= i < str.Length && is_word_start_array(str, i)) // if there is at least one word, then there is at least one index that is the start of a word
{
  // implementation
}



// It is a well-known phenomenon that most people are easily able to read a text whose
//words have two characters flipped, provided the first and last letter of each word are
//not changed. For example,
//I dn’ot gvie a dman for a man taht can olny sepll a wrod one way. (Mrak Taiwn)
//Write a method String scramble(String word) that constructs a scrambled version of a
//given word, ran domly flipping two characters other than the first and last one. Then
//write a program that reads words and prints the scrambled words


// write a permutation function becase they are permuting of each other
method p5_8_scramble(word: seq<string>) returns (scrambled: seq<string>)
requires 1 <= |word| && forall w :: w in word ==> 1 <= |w|
ensures |scrambled| == |word|
ensures forall i :: 0 <= i < |word| ==> |scrambled[i]| == |word[i]|
ensures forall i :: 0 <= i < |word| ==> word[i][0] == scrambled[i][0] && word[i][|word[i]| - 1] == scrambled[i][|scrambled[i]| - 1]
{  
}

method p5_8_scramble_array(word: array<string>) returns (scrambled: array<string>)
requires 1 <= word.Length && forall w :: w in word[..] ==> 1 <= |w|
ensures scrambled.Length == word.Length
ensures forall i :: 0 <= i < word.Length ==> |scrambled[i]| == |word[i]|
ensures forall i :: 0 <= i < word.Length ==> word[i][0] == scrambled[i][0] && 
  word[i][|word[i]| - 1] == scrambled[i][|scrambled[i]| - 1]
{  
}

//p5.9 Write methods
//public static double sphereVolume(double r)
//public static double sphereSurface(double r)
//public static double cylinderVolume(double r, double h)
//public static double cylinderSurface(double r, double h)
//public static double coneVolume(double r, double h)
//public static double coneSurface(double r, double h)
//that compute the volume and surface area of a sphere with radius r, a cylinder with a
//circular base with radius r and height h, and a cone with a circular base with radius r
//and height h. Then write a program that prompts the user for the values of r and h,
//calls the six methods, and prints the results

method p5_9_sphereVolume(r: real) returns (volume: real)
ensures volume == (4.0 / 3.0) * 3.14159 * r * r * r
{  
}

method p5_9_sphereSurface(r: real) returns (surface_area: real)
ensures surface_area == 4.0 * 3.14159 * r * r
{  
}

method p5_9_cylinderVolume(r: real, h: real) returns (volume: real)
ensures volume == 3.14159 * r * r * h
{  
}

method p5_9_cylinderSurface(r: real, h: real) returns (surface_area: real)
ensures surface_area == 2.0 * 3.14159 * r * (r + h)
{  
}

method p5_9_coneVolume(r: real, h: real) returns (volume: real)
ensures volume == (1.0 / 3.0) * 3.14159 * r * r * h
{  
}

// can you give surface area without sqrt? 
// taken https://github.com/dafny-lang/teaching-material/blob/066004f07fcd2e7bc13e75b0ecf448cca3c8c674/Exercises/IncreasingSQRT_solution.dfy#L4
// In this exercise, we will prove some properties of the square root function. First, we posit its existence.
ghost function Sqrt(x: real): real

// The square root function is characterized by two properties that we axiomatize. First, the square root function is positive.
lemma SqrtPos()
  ensures forall x: real :: x >= 0.0 ==> Sqrt(x) >= 0.0

// Second, for a given real x, the product of the square root of x with itself is x. That's the essence of the square root function.
lemma SqrtProp()
  ensures forall x: real :: x >= 0.0 ==> Sqrt(x) * Sqrt(x) == x

// Exercise
// Our goal is to prove that the square root function is monotonic. First, we will do so as a sequent. Maybe you do not remember how to prove this property, and that's fine. Think about it on paper first, and when you think you might have an argument, see if Dafny accepts it. Hint: assume that the square root function was not monotonic, and show that it is inconsistent.
lemma MonotonicPre(x: real, y: real)
  requires 0.0 <= x < y
  ensures Sqrt(x) < Sqrt(y)
{
  assert x < y;
  assert Sqrt(x) * Sqrt(x) < Sqrt(y) * Sqrt(y) by {
    SqrtProp();
  }
  assert Sqrt(x) >= 0.0 && Sqrt(y) >= 0.0 by {
    SqrtPos();
  }
  if Sqrt(x) >= Sqrt(y) {
    assert Sqrt(x) * Sqrt(x) >= Sqrt(y) * Sqrt(y);
    assert false;
  }
}

// Exercise
// Using that lemma we just proved, prove the non-sequent version of the theorem.
lemma Monotonic()
  ensures forall x, y: real :: 0.0 <= x < y ==> Sqrt(x) < Sqrt(y)
{
  forall x, y: real ensures 0.0 <= x < y ==> Sqrt(x) < Sqrt(y) {
    if 0.0 <= x < y {
      MonotonicPre(x,y);
    }
  }
}


method p5_9_coneSurface(r: real, h: real) returns (surface_area: real)
ensures surface_area == 3.14159 * r * (r + Sqrt(h * h + r * r))
{  
} 


//p5.10 Write a method
//public static double readDouble(String prompt)
//that displays the prompt string, followed by a space, reads a floating-point number
//in, and returns it. Here is a typical usage:
//salary = readDouble("Please enter your salary:");
//percentageRaise = readDouble("What percentage raise would you like?");

// Not a very spec friendly method
method p5_10_readDouble(prompt: seq<char>) returns (value: real)
{  
}

