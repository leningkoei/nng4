import NNG4.Definitions.MyNat

def ℕ.is_zero : ℕ → Bool
| 0 => .true
| (.succ _n) => .false
