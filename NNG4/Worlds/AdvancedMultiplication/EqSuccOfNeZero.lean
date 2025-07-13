import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Cases
import NNG4.Tactics.Use
import NNG4.Tactics.Tauto
import NNG4.Theorems.MulZero

theorem eq_succ_of_ne_zero (a : ℕ) (ha : a ≠ 0) : ∃ n, a = .succ n := by
  cases a with d
  tauto
  use d
  rfl
