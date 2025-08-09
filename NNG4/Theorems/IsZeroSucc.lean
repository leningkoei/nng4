import NNG4.Definitions.MyNat
import NNG4.Definitions.IsZero

axiom is_zero_succ (n : ℕ) : ℕ.is_zero (.succ n) = False
