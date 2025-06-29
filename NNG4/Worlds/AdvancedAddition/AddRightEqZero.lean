import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Symm
import NNG4.Tactics.Cases
import NNG4.Tactics.Apply
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc
import NNG4.Theorems.ZeroNeSucc

theorem add_right_eq_zero (a b : ℕ) : a + b = 0 → a = 0 := by
  cases b with d
  rw[add_zero]
  intro h
  exact h
  rw [add_succ]
  intro h
  symm at h
  apply zero_ne_succ at h
  cases h
