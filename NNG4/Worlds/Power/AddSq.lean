import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.MulAdd
import NNG4.Theorems.AddMul
import NNG4.Theorems.MulComm
import NNG4.Theorems.MulAssoc
import NNG4.Theorems.TwoMul
import NNG4.Theorems.PowTwo

theorem add_sq (a b : ℕ)
: (a + b) ^ (2 : ℕ) = a ^ (2 : ℕ) + b ^ (2 : ℕ) + 2 * a * b := by
  rw[pow_two]
  rw[mul_add]
  repeat rw[add_mul]
  repeat rw[← pow_two]
  rw[mul_comm]
  rw[← add_assoc]
  rw[add_assoc (a ^ 2) (a * b) (a * b)]
  rw[← two_mul (a * b)]
  rw[← mul_assoc]
  rw[add_assoc, add_comm (2 * a * b), ← add_assoc]
  rfl
