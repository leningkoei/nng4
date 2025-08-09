import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddLeftComm

example (a b c d : ℕ) : a + b + (c + d) = a + c + d + b := by
  repeat rw [add_assoc]
  rw [add_left_comm b c]
  rw [add_comm b d]
  rfl
