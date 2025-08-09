import NNG4.Definitions.MyNat
import NNG4.Theorems.SuccNeZero
import NNG4.Theorems.ZeroNeSucc
import NNG4.Theorems.SuccNeSucc

instance MyNat.instDecidableEq : DecidableEq ℕ
| 0, 0 => isTrue <| by
  show 0 = 0
  rfl
| .succ m, 0 => isFalse <| by
  show .succ m ≠ (0 : MyNat)
  exact succ_ne_zero m
| 0, .succ n => isFalse <| by
  show (0 : MyNat) ≠ .succ n
  exact zero_ne_succ n
| .succ m, .succ n =>
  match MyNat.instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show MyNat.succ m = .succ n
    rw [h]
    rfl
  | isFalse (h : m ≠ n) => isFalse <| by
    show MyNat.succ m ≠ .succ n
    exact succ_ne_succ m n h
