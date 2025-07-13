import NNG4.Definitions.MyNat
import NNG4.Tactics.Tauto
import NNG4.Tactics.Have
import NNG4.Theorems.MulNeZero

theorem mul_eq_zero (a b : ℕ) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  have h2 := mul_ne_zero a b
  tauto
