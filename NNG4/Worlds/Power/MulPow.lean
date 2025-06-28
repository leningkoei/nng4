import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.MulOne
import NNG4.Theorems.MulComm
import NNG4.Theorems.MulAssoc
import NNG4.Theorems.PowSucc
import NNG4.Theorems.PowZero

theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with d hd
  repeat rw[pow_zero]
  rw[mul_one]
  rfl
  rw[pow_succ]
  rw[← mul_assoc]
  rw[hd]
  repeat rw[pow_succ]
  rw[← mul_assoc]
  rw[mul_assoc (a ^ d) a]
  rw[mul_comm a (b ^ d)]
  rw[← mul_assoc]
  rfl
