import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.OneMul
import NNG4.Theorems.PowZero
import NNG4.Theorems.PowSucc
import NNG4.Theorems.OneEqSuccZero

theorem pow_one (a : ℕ) : a ^ (1 : ℕ) = a := by
  rw[one_eq_succ_zero]
  rw[pow_succ a 0]
  rw[pow_zero a]
  rw[one_mul a]
  rfl
