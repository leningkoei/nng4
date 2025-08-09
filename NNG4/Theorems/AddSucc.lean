import NNG4.Definitions.MyNat
import NNG4.Tactics.LabelAttr

@[simp, MyNat_decide]
axiom add_succ (a d : ℕ) : a + (.succ d) = .succ (a + d)
