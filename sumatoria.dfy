method Sumatoria(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == (n * (n + 1)) / 2
{

    var i: int := 0;
    sum := 0;

    while i < n
      invariant 0 <= i <= n
      invariant sum == (i * (i + 1)) / 2
      decreases n - i
    {

        i := i + 1;
        sum := sum + i;
    }
} 
