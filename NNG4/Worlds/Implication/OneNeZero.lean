import NNG4.Definitions.MyNat
import NNG4.Tactics.Apply
import NNG4.Tactics.Symm
import NNG4.Theorems.ZeroNeOne

theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  symm
  exact zero_ne_one
  -- intro h
  -- apply zero_ne_one
  -- exact (Eq.symm h)
