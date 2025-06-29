import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Symm
import NNG4.Tactics.Cases
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.AddRightEqZero
import NNG4.Theorems.AddRightEqSelf

theorem le_antisymm (x y : ℕ) (hxy : x ≤ y) (hyx : y ≤ x) : x = y := by
  cases hxy with a ha
  cases hyx with b hb
  rw [ha]
  rw [ha, add_assoc] at hb
  symm at hb
  apply add_right_eq_self at hb
  apply add_right_eq_zero at hb
  rw [hb, add_zero]
  rfl
  -- cases hxy with a ha
  -- cases hyx with b hb
  -- rw[ha] at hb
  -- symm at hb
  -- rw[add_assoc] at hb
  -- apply add_right_eq_self at hb
  -- apply add_right_eq_zero at hb
  -- rw[hb] at ha
  -- rw[add_zero] at ha
  -- symm at ha
  -- exact ha
