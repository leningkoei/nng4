import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Trivial
import NNG4.Theorems.IsZeroZero
import NNG4.Theorems.IsZeroSucc

#print is_zero_succ

theorem succ_ne_zero (a : ℕ) : MyNat.succ a ≠ 0 := by
  intro h
  rw [← is_zero_succ a]
  trivial
