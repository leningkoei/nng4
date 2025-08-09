import NNG4.Definitions.MyNat
import NNG4.Tactics.SimpAdd

example (a b c d e f g h : ℕ)
: (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add
