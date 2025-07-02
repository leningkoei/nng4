import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Cases
import NNG4.Tactics.Symm
import NNG4.Tactics.LeftRight
import NNG4.Theorems.AddZero
import NNG4.Theorems.ZeroAdd
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.AddRightEqZero
import NNG4.Theorems.AddRightCancel
import NNG4.Theorems.LeZero
import NNG4.Theorems.SuccLeSucc
import Mathlib.Tactic.NthRewrite

theorem le_one (x : ℕ) (hx : x ≤ 1) : x = 0 ∨ x = 1 := by
  cases x with y
  left
  rfl
  rw [one_eq_succ_zero] at hx ⊢ -- use this theorem both at hx and goal
  apply succ_le_succ at hx
  apply le_zero at hx
  rw [hx]
  right
  rfl
  -- cases hx with e hx
  -- cases e with a
  -- right
  -- rw [add_zero] at hx
  -- symm
  -- exact hx
  -- rw [add_succ] at hx
  -- rw [succ_eq_add_one] at hx
  -- nth_rewrite 1 [← zero_add 1] at hx
  -- apply add_right_cancel 0 (x + a) 1 at hx
  -- symm at hx
  -- apply add_right_eq_zero x a at hx
  -- left
  -- exact hx
