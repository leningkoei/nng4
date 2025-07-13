import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Tactics.Cases
import NNG4.Tactics.Use
import NNG4.Tactics.Tauto
import NNG4.Theorems.AddComm
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulSucc
import NNG4.Theorems.OneMul
import NNG4.Theorems.MulComm
import NNG4.Theorems.MulLeftNeZero
import NNG4.Theorems.MulLeMulRight
import NNG4.Theorems.OneLeOfNeZero

theorem le_mul_right (a b : ℕ) (h : a * b ≠ 0) : a ≤ a * b := by
  apply mul_left_ne_zero at h
  apply one_le_of_ne_zero at h
  apply mul_le_mul_right 1 b a at h
  rw [one_mul, mul_comm] at h
  exact h
  -- cases b with d hd
  -- rw [mul_zero] at h
  -- tauto
  -- rw [mul_succ]
  -- use a * d
  -- rw [add_comm]
  -- rfl
