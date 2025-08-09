import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.PredSucc

example (a b : ℕ) (h : MyNat.succ a = .succ b) : a = b := by
  rw [← pred_succ a]
  rw [h]
  rw [pred_succ]
  rfl
