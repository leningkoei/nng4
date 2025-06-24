import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.SuccInj
import NNG4.Theorems.FourEqSuccThree

example (x : ℕ) (h : x + 1 = 4)
: x = 3
:= by
  rw[four_eq_succ_three] at h
  rw[← succ_eq_add_one] at h
  apply succ_inj at h
  exact h
