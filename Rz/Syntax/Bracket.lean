universe u v w

inductive Bracket (α : Type u) : Nat → Type u where
| var : {n : Nat} → Fin n → Bracket α n
| const : {n : Nat} → α → Bracket α n
| ap : {n : Nat} → Bracket α n → Bracket α n → Bracket α n
| abs : {n : Nat} → Bracket α (n + 1) → Bracket α n
