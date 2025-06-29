import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Induction
import NNG4.Tactics.Apply
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccInj

theorem add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  induction n with d hd
  repeat rw[add_zero]
  intro h
  exact h
  intro h
  apply hd
  apply succ_inj
  repeat rw[add_succ] at h
  exact h
