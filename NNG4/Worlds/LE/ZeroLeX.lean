import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Use
import NNG4.Theorems.ZeroAdd

theorem zero_le (x : ℕ) : 0 ≤ x := by
  use x
  rw[zero_add]
  rfl
