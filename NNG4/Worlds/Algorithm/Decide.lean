import NNG4.Definitions.MyNat
import NNG4.Tactics.Decide
import NNG4.Theorems.AddZero
import NNG4.Theorems.AddSucc

example : (20 : ℕ) + 20 = 40 := by
  decide
