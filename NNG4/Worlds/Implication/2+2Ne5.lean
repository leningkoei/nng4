import NNG4.Definitions.MyNat
import NNG4.Tactics.RW
import NNG4.Tactics.Apply
import NNG4.Theorems.ZeroAdd
import NNG4.Theorems.OneEqSuccZero
import NNG4.Theorems.AddSucc
import NNG4.Theorems.SuccInj
import NNG4.Theorems.ZeroNeSucc

example : MyNat.succ (.succ 0) + .succ (.succ 0) ≠
.succ (.succ (.succ (.succ (.succ 0)))) := by
  repeat rw[add_succ]
  rw[add_zero]
  intro h
  repeat apply succ_inj at h
  apply zero_ne_succ at h
  exact h
