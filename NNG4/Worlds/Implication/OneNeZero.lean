import NNG4.Definitions.MyNat
import NNG4.Tactics.Apply
import NNG4.Theorems.ZeroNeOne

theorem one_ne_zero : (1 : ℕ) ≠ 0 := by
  intro h
  apply zero_ne_one
  exact (Eq.symm h)
