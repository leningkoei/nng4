import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Exact
import NNG4.Theorems.MulOne
import NNG4.Theorems.MulLeftCancel
import Mathlib.Tactic.NthRewrite

theorem mul_right_eq_self (a b : ℕ) (ha : a ≠ 0) (h : a * b = a) : b = 1 := by
  nth_rewrite 2 [← mul_one a] at h
  exact mul_left_cancel a b 1 ha h
  -- apply mul_left_cancel a b 1 ha at h
  -- exact h
