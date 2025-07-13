import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Tactics.Apply
import NNG4.Tactics.Symm
import NNG4.Tactics.Tauto
import NNG4.Theorems.AddRightCancel
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulSucc
import NNG4.Theorems.MulEqZero

theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0) (h : a * b = a * c)
: b = c := by
  induction b with d hd generalizing c
  rw [mul_zero] at h
  symm at h
  apply mul_eq_zero at h
  tauto
  cases c with e
  rw [mul_zero] at h
  apply mul_eq_zero at h
  tauto
  rw [mul_succ, mul_succ] at h
  apply add_right_cancel at h
  apply hd at h
  rw [h]
  rfl
