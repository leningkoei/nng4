import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.PowZero

theorem zero_pow_zero : (0 : ℕ) ^ (0 : ℕ) = 1 := by
  rw[pow_zero 0]
  rfl
