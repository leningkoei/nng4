import NNG4.Definitions.MyNat
import NNG4.Definitions.DecidableEq
import NNG4.Tactics.Decide
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc

example : (2 : ℕ) + 2 ≠ 5 := by
  decide
