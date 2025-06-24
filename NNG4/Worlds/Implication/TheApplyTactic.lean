import NNG4.Definitions.MyNat
import NNG4.Tactics.Apply

example (x y : ℕ) (h1 : x = 37) (h2 : x = 37 → y = 42)
: y = 42
:= by
  apply h2 at h1
  exact h1
