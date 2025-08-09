import NNG4.Definitions.MyNat
import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Tactics.Simp
import NNG4.Theorems.AddAssoc
import NNG4.Theorems.AddComm
import NNG4.Theorems.AddLeftComm

example (a b c d e f g h : ℕ)
: (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_left_comm, add_comm]
