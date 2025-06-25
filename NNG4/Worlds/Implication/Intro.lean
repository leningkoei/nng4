import NNG4.Definitions.MyNat

example (x : ℕ) : x = 37 → x = 37 := by
  intro h
  exact h
