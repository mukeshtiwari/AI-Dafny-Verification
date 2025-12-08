
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

// p5.7 Write a method
// Write a method
// public static int countWords(String str)
// that returns a count of all words in the string str. Words are separated by spaces. For
// example, countWords("Mary had a little lamb") should return 5.

// Todo: not a very good spec so improve it. 
method p5_7_countWords(str: seq<char>) returns (wordCount: int)
ensures wordCount >= 0
ensures if |str| == 0 then wordCount == 0 else wordCount >= 1
{
}

