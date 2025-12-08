// greeting of your choice
method p_1_1() returns (s : string)
ensures s == "hugo"
{
    return "hugo";
}



method p_1_2() returns (i : int)
ensures i == (10 * 11) / 2
{
}

function factorial(n : int) : int  
decreases n 
{
    if n <= 1 then 1 else n * factorial (n-1)
}

method p_1_3() returns (i : int)
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
    return "--------\n| Dave |\n--------\n";
}


method p_1_6() returns (s : string)
ensures s == "*   *\n*   *\n*****\n*   *\n*   *\n"
{
    return "*   *\n*   *\n*****\n*   *\n*   *\n";
}

method p_1_7() returns (s : string)
ensures s == " ///// \n \"\"\"\"\" \n+     +"
{
    return " ///// \n \"\"\"\"\" \n+     +";
}

function mystring(s : string, n : int) : string 
{
    if n == 0 then "" else s + mystring(s, n -1)
}

method p_1_8() returns (s : string)
ensures s == mystring("          !!!@@@@@@@@@@@@@@@@@@@@\n", 5)
{

    return "          !!!@@@@@@@@@@@@@@@@@@@@\n          !!!@@@@@@@@@@@@@@@@@@@@\n          !!!@@@@@@@@@@@@@@@@@@@@\n          !!!@@@@@@@@@@@@@@@@@@@@\n          !!!@@@@@@@@@@@@@@@@@@@@\n";
}

method p_1_9() returns (s : string)
ensures s == "   +    \n  + +   \n +   + \n+-----+\n"
{
    return "   +    \n  + +   \n +   + \n+-----+\n";
}

method p_1_10() returns (s : string)
ensures s =  " /\_/\    -----\n" + "" 


method Main() {
    var t : string := p_1_9();
	print t;
}
