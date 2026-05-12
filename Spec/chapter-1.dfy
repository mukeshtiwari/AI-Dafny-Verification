// Book page 25.

// greeting of your choice
method p_1_1() returns (s : string)
ensures s == "hugo"
{
    return "hugo";
}



method p_1_2() returns (i : nat)
ensures i == (10 * 11) / 2
{
}

// removed if then else statement and replaced with match statement
function factorial(n: nat): nat
{
    match n
    case 0 => 1
    case _ => n * factorial(n - 1)
}


method p_1_3() returns (i : nat)
ensures i == factorial(10)
{

}

method p_1_4() returns (first : real, second : real, third : real)
ensures first == 1000.0 + 1000.0 * 0.05
ensures second == first + first * 0.05 
ensures third == second + second * 0.05 
{
    
}

method p_1_5() returns (s : string)
ensures s == "--------\n| Dave |\n--------\n"
{
  
}


method p_1_6() returns (s : string)
ensures s == "*   *\n*   *\n*****\n*   *\n*   *\n"
{
    
}

method p_1_7() returns (s : string)
ensures s == " ///// \n \"\"\"\"\" \n+     +"
{
    
}

function mystring(s : string, n : nat) : string 
decreases n
{
    match n 
    case 0 => ""
    case _ => s + mystring(s, n - 1)
}

method p_1_8() returns (s : string)
ensures s == mystring("          !!!@@@@@@@@@@@@@@@@@@@@\n", 5)
{
}

method p_1_9() returns (s : string)
ensures s == "   +    \n  + +   \n +   + \n+-----+\n"
{

}


method p_1_10() returns (s : string)
ensures s == " /\\_/\\    -----\n" +
    "( ' ' )  / Hello \\\'\n" +
    "(  -  ) <  Junior |\n" +
    " | | |  \\ Coder!/\n" +
    "(_|_|)    -----\n"
{
}


method Main() {
    var t : string := p_1_9();
	print t;
}
