import NNG4.Definitions.MyNat
import NNG4.Tactics.Cases
import NNG4.Tactics.Use
import NNG4.Theorems.SuccAdd
import NNG4.Theorems.SuccInj

theorem succ_le_succ (x y : ℕ) (hx : MyNat.succ x ≤ .succ y) : x ≤ y := by
  cases hx with e hx
  use e
  rw [succ_add] at hx
  apply succ_inj
  exact hx
