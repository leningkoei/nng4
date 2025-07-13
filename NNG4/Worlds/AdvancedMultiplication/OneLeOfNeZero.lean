import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Tactics.Cases
import NNG4.Tactics.Use
import NNG4.Tactics.Tauto
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.AddComm
import NNG4.Theorems.EqSuccOfNeZero

theorem one_le_of_ne_zero (a : ℕ) (ha : a ≠ 0) : 1 ≤ a := by
  apply eq_succ_of_ne_zero at ha
  cases ha with n hn
  rw [hn]
  use n
  rw [succ_eq_add_one]
  rw [add_comm]
  rfl
  -- cases a with d
  -- tauto
  -- use d
  -- rw [succ_eq_add_one]
  -- rw [add_comm]
  -- rfl
