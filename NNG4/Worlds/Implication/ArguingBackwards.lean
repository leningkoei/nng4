import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.SuccInj
import NNG4.Theorems.FourEqSuccThree

example (x : ℕ) (h : x + 1 = 4) : x = 3 := by
  apply succ_inj
  rw[succ_eq_add_one x]
  rw[← four_eq_succ_three]
  exact h
