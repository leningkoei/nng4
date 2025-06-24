import NNG4.Definitions.MyNat
-- import NNG4.Tactics.RFL
import NNG4.Tactics.RW
import NNG4.Theorems.ZeroAdd

example (x : ℕ) (h : 0 + x = 0 + y + 2)
: x = y + 2
:= by
  rw[zero_add x] at h
  rw[zero_add y] at h
  -- rw[h]
  -- rfl
  exact h
