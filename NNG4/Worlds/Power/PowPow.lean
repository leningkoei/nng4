import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.MulZero
import NNG4.Theorems.MulOne
import NNG4.Theorems.MulComm
import NNG4.Theorems.MulAssoc
import NNG4.Theorems.PowSucc
import NNG4.Theorems.PowZero
import NNG4.Theorems.PowAdd

theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with d hd
  rw[mul_zero]
  repeat rw[pow_zero]
  rfl
  rw[pow_succ]
  rw[mul_succ]
  rw[pow_add]
  rw[hd]
  rfl
