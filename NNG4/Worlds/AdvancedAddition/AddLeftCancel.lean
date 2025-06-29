import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddRightCancel

theorem add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  repeat rw[add_comm n]
  exact (add_right_cancel a b n)
