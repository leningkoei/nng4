import NNG4.Definitions.MyNat

example (x y z : ℕ) (h1 : x + y = 37) (_h2 : 3 * x + z = 42)
: x + y = 37
:= by
  exact h1
