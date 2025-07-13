import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Tactics.Cases
import NNG4.Tactics.Symm
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccMul
import NNG4.Theorems.MulSucc
import NNG4.Theorems.ZeroNeSucc
import NNG4.Theorems.EqSuccOfNeZero

theorem mul_ne_zero (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  apply eq_succ_of_ne_zero at ha
  apply eq_succ_of_ne_zero at hb
  cases ha with n₁ ha
  cases hb with n₂ hb
  rw [ha, hb]
  rw [succ_mul, mul_succ]
  rw [add_succ]
  symm
  apply zero_ne_succ
