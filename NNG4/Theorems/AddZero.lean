import NNG4.Definitions.MyNat
import NNG4.Tactics.LabelAttr

@[simp, MyNat_decide]
axiom add_zero (a : ℕ) : a + 0 = a
