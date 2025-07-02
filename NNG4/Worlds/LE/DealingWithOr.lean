import NNG4.Definitions.MyNat
import NNG4.Tactics.Cases
import NNG4.Tactics.LeftRight

example (x y : ℕ) (h : x = 37 ∨ y = 42) : y = 42 ∨ x = 37 := by
  cases h with hx hy
  right
  exact hx
  left
  exact hy
