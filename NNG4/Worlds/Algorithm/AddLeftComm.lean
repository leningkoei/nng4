import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddAssoc

theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by
  rw [add_comm]
  rw [add_assoc]
  rw [add_comm c a]
  rfl
