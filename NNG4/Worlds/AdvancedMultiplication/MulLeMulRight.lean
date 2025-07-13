import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Cases
import NNG4.Tactics.Use
import NNG4.Theorems.AddMul

theorem mul_le_mul_right (a b t : ℕ) (h : a ≤ b) : a * t ≤ b * t := by
  cases h with c hc
  rw [hc]
  rw [add_mul]
  use c * t
  rfl
