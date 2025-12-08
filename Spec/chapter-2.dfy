// • p2.1  Write a program that displays the dimensions of a letter-size (8.5 × 11 inches) sheet 
// of paper in millimeters. There are 25.4 millimeters per inch. 
// Use constants and comments in your program.
 
method Letter_Dimensions () returns (x: real, y:real) 
  ensures x == 8.5 * 25.4
  ensures y == 11.0 * 25.4
{
  
}

//• p2.2  Write a program that computes and displays the perimeter 
// of a letter-size (8.5 × 11 inches) sheet of paper and the length of its diagonal.

// Ma & Mu: couldn't find the square root function - 
// let the AI be troubled :-) 

method Letter_perimeter () returns (x: real, y:real) 
  ensures x == (8.5 * 25.4) * 2.0 + 11.0 * 25.4 * 2.0
  ensures y * y  == (8.5 * 25.4) * (8.5 * 25.4) + 11.0 * 25.4 * 11.0 * 25.4 
{
}

// • p2.3  Write a program that reads a number and displays the square, cube, and fourth power. 
// Use the Math.pow method only for the fourth power.

method powerFunctions (x: int) returns (sq: int, cube : int, fourth: int)
  ensures sq == x * x
  ensures cube == x * x * x
  ensures fourth == x * x *x * x
{
}

// •• p2.4  Write a program that prompts the user for two integers and then prints
// • The sum

method sum (x: int, y: int ) returns (result:int)
  ensures result == x + y
{
}

// • The difference

method difference (x: int, y: int ) returns (result:int)
  ensures result == x - y
{
}

// • The product

method product (x: int, y: int ) returns (result:int)
  ensures result == x * y
{
}


// • The average

method average (x: int, y: int ) returns (result:real)
  ensures result == (x + y)as real / 2.0
{
}

// • The distance (absolute value of the difference)

method distance (x: int, y: int ) returns (result:int)
  ensures result >= 0
  ensures if x >= y then result == x -y else result == y - x
{
}

// • The maximum (the larger of the two)

method max (x: int, y: int ) returns (result:int)
  ensures result == x || result == y
  ensures if x >= y then result == x  else result == y
{
}

// • The minimum (the smaller of the two)

method min (x: int, y: int ) returns (result:int)
  ensures result == x || result == y
  ensures if x <= y then result == x  else result == y
{
}

// Enhance the output of Exercise P2.4 so that the numbers are properly aligned:
// -- we are thinking about this

// 2.6 Write a program that prompts the user for a measurement in meters and 
// then converts it to miles, feet, and inches.

method convert (x: real) returns (miles: real, feet: real, inches: real)
  ensures x / 0.000621371 == miles
  ensures x / 3.28084 == feet
  ensures x / 39.3701 == inches
{
}


//Write a program that prompts the user for a radius and then prints
//• The area and circumference of a circle with that radius
//• The volume and surface area of a sphere with that radius

method circle_properties(radius: real) returns (circumference: real, area: real, surface_area: real, volume: real)
ensures circumference == 2.0 * 3.14159 * radius
ensures area == 3.14159 * radius * radius
ensures surface_area == 4.0 * 3.14159 * radius * radius
ensures volume == (4.0 / 3.0) * 3.14159 * radius * radius * radius
{
   
}


// Write a program that asks the user for the lengths of the sides of a rectangle. Then
  //print
  // • The area and perimeter of the rectangle
  // • The length of the diagonal (use the Pythagorean theorem)

method rectangle_properties(length: real, width: real) returns (area: real, perimeter: real, diagonal: real)
ensures area == length * width
ensures perimeter == 2.0 * (length + width)
ensures diagonal * diagonal == length * length + width * width
{ 
  
}

//Improve the program discussed in How To 2.1 to allow input of quarters in addition
// to bills. 

// Mukesh Not writing it for the moment 


//Write a program that helps a person decide whether to buy a hybrid car. Your
//program’s inputs should be:
//• The cost of a new car
//• The estimated miles driven per year
//• The estimated gas price
//• The efficiency in miles per gallon
//• The estimated resale value after 5 years
////Compute the total cost of owning the car for
//five years. (For simplic ity, we will not take the
//cost of financing into account.) Obtain
//realistic prices for a new and used hybrid
//and a comparable car from the Web. Run your program twice, using today’s gas
//price and 15,000 miles per year. Include pseudocode and the program runs with your
// assignment.

method hybrid_car_cost(new_car_cost: real, miles_per_year: real, gas_price: real, mpg: real, resale_value: real) returns (total_cost: real)
requires 0.0 < mpg
ensures total_cost == new_car_cost + (miles_per_year / mpg) * gas_price * 5.0 - resale_value
{ 
  
}