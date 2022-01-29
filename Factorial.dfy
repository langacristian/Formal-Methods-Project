function method factorial(x: int): int
{
if x < 2 then 1 else x * factorial(x - 1)
}
method Fact(x: int) returns (y: int)
  ensures y == factorial(x);
  requires x >= 0;   
{
    y := 1;
    var z := 0;
    while(z != x)
     invariant y == factorial(z)
     decreases x - z;
     invariant 0 <= x-z;
    {
        z := z + 1;
        y := y * z;
    }
}
method Main() {
    var a := Fact(87);
    print a;
}