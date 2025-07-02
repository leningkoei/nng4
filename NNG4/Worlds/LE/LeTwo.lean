import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Tactics.Cases
import NNG4.Tactics.LeftRight
import NNG4.Theorems.SuccLeSucc
import NNG4.Theorems.OneEqSuccZero
import NNG4.Theorems.TwoEqSuccOne
import NNG4.Theorems.LeOne

theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by
  cases x with x
  left
  rfl
  rw [two_eq_succ_one] at hx
  apply succ_le_succ at hx
  apply le_one at hx
  cases hx with hzero hone
  right
  left
  rw [hzero]
  rw [← one_eq_succ_zero]
  rfl
  right
  right
  rw [hone]
  rw [two_eq_succ_one]
  rfl
