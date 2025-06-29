import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddRightEqZero

theorem add_left_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  rw[add_comm]
  apply add_right_eq_zero
