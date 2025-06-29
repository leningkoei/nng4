import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddLeftEqSelf

theorem add_right_eq_self (x y : ℕ) : x + y = x → y = 0 := by
  rw[add_comm x]
  exact add_left_eq_self y x
