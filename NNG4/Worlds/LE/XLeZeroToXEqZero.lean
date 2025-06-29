import NNG4.Definitions.MyNat
import NNG4.Tactics.Symm
import NNG4.Tactics.Cases
import NNG4.Theorems.AddRightEqZero

theorem le_zero (x : ℕ) (hx : x ≤ 0) : x = 0 := by
  cases hx with a ha
  symm at ha
  apply add_right_eq_zero at ha
  exact ha
