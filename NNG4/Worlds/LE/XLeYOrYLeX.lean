import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Tactics.Cases
import NNG4.Tactics.LeftRight
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccAdd
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.ZeroLe
import NNG4.Theorems.LeSuccSelf

theorem le_total (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction y with d hd
  right
  apply zero_le x
  cases hd with hxd hdx
  left
  cases hxd with e hxd
  rw [hxd]
  use e + 1
  rw [succ_eq_add_one, add_assoc]
  rfl
  cases hdx with e he
  cases e with a
  left
  rw [he]
  rw [add_zero]
  apply le_succ_self
  right
  rw [he]
  use a
  rw [add_succ, succ_add]
  rfl
