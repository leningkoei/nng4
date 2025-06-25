import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Theorems.SuccEqAddOne
import NNG4.Theorems.SuccInj

example (x : ℕ) : x + 1 = y + 1 → x = y := by
  rw[← succ_eq_add_one x]
  rw[← succ_eq_add_one y]
  exact (succ_inj x y)
  -- intro h
