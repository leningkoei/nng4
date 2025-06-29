import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Use
import NNG4.Theorems.AddZero

theorem le_refl (x : ℕ) : x ≤ x := by
  use 0
  rw[add_zero]
  rfl
