import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.ZeroAdd
import NNG4.Theorems.AddRightCancel
import Mathlib.Tactic.NthRewrite

theorem add_left_eq_self (x y : ℕ) : x + y = y → x = 0 := by
  nth_rewrite 2 [← zero_add y]
  -- intro h
  -- apply add_right_cancel at h
  -- exact h
  exact add_right_cancel x 0 y
