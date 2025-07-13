import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.MulZero

theorem mul_left_ne_zero (a b : ℕ) (h : a * b ≠ 0) : b ≠ 0 := by
  intro hf
  apply h
  rw [hf]
  rw [mul_zero]
  rfl
