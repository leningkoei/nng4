import NNG4.Definitions.MyNat

axiom succ_inj (a b : ℕ) (h : MyNat.succ a = .succ b)
: a = b
