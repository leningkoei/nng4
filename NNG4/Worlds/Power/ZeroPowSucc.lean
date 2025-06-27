import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.MulZero
import NNG4.Theorems.PowSucc

theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (MyNat.succ m) = 0 := by
  rw[pow_succ 0 m]
  rw[mul_zero]
  rfl
