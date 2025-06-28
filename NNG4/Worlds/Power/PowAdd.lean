import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc
import NNG4.Theorems.MulOne
import NNG4.Theorems.MulAssoc
import NNG4.Theorems.PowSucc
import NNG4.Theorems.PowOne

theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with d hd
  rw[add_zero m]
  rw[pow_zero a]
  rw[mul_one (a ^ m)]
  rfl
  rw[add_succ m d]
  rw[pow_succ a (m + d)]
  rw[hd]
  rw[pow_succ a d]
  rw[← mul_assoc (a ^ m) (a ^ d) a]
  rfl
