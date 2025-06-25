import NNG4.Definitions.MyNat
import NNG4.Tactics.Apply

example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2
  exact h1

example (x y : ℕ) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 at h1
  exact h1
