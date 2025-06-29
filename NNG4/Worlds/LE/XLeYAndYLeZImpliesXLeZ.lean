import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Cases
import NNG4.Tactics.Use
import NNG4.Theorems.AddAssoc

theorem le_trans (x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) : x ≤ z := by
  cases hxy with a ha
  cases hyz with b hb
  use (a + b)
  rw[hb]
  rw[ha]
  rw[add_assoc]
  rfl
