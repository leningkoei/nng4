import NNG4.Definitions.MyNat
import NNG4.Tactics.Exact
import NNG4.Tactics.Contrapose
import NNG4.Theorems.SuccInj

theorem succ_ne_succ (m n : ℕ) (h : m ≠ n) : MyNat.succ m ≠ .succ n := by
  contrapose! h
  exact succ_inj m n h
