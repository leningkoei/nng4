import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Tactics.Cases
import NNG4.Tactics.Exact
import NNG4.Tactics.Symm
import NNG4.Tactics.Tauto
import NNG4.Tactics.Have
import NNG4.Theorems.ZeroNeSucc
import NNG4.Theorems.OneEqSuccZero
import NNG4.Theorems.ZeroMul
import NNG4.Theorems.LeOne
import NNG4.Theorems.LeMulRight

theorem mul_right_eq_one (x y : ℕ) (h : x * y = 1) : x = 1 := by
  have h2 : x * y ≠ 0
  rw [h]
  rw [one_eq_succ_zero]
  symm
  apply zero_ne_succ
  apply le_mul_right at h2
  rw [h] at h2
  apply le_one at h2
  cases h2 with h0 h1
  rw [h0, zero_mul] at h
  tauto
  exact h1
