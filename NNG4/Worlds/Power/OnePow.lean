import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Theorems.MulOne
import NNG4.Theorems.PowZero
import NNG4.Theorems.PowSucc

theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with d hd
  rw[pow_zero 1]
  rfl
  rw[pow_succ 1 d]
  rw[mul_one (1 ^ d)]
  exact hd
