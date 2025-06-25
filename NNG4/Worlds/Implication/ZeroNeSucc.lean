import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.ZeroNeSucc
import NNG4.Theorems.OneEqSuccZero

theorem zero_ne_one : (0 : ℕ) ≠ 1 := by
  -- intro h
  rw[one_eq_succ_zero]
  exact (zero_ne_succ 0)
