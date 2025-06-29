import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Use
import NNG4.Theorems.SuccEqAddOne

theorem le_succ_self (x : ℕ) : x ≤ .succ x := by
  use 1
  rw[succ_eq_add_one]
  rfl
