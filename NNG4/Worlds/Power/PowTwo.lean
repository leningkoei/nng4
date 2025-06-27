import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.PowSucc
import NNG4.Theorems.PowOne
import NNG4.Theorems.TwoEqSuccOne

theorem pow_two (a : ℕ) : a ^ (2 : ℕ) = a * a := by
  rw[two_eq_succ_one]
  rw[pow_succ a 1]
  rw[pow_one a]
  rfl
