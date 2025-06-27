import NNG4.Definitions.MyNat

axiom pow_succ (m n : ℕ) : m ^ MyNat.succ n = m ^ n * m
