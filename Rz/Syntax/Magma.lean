/-
# Free Magmas
-/

universe u v w

-- Not /really/ the free magma anymore...
inductive FreeMagma (α : Type u) (n : Nat) : Type u where
| var : Fin n → FreeMagma α n
| const : α → FreeMagma α n
| op : FreeMagma α n → FreeMagma α n → FreeMagma α n

namespace FreeMagma

def foldM [Monad m] (v : Fin n → m β) (c : α → m β) (o : β → β → m β) : FreeMagma α n → m β
| .var i => v i
| .const a => c a
| .op l r => do
  let a ← foldM v c o l
  let b ← foldM v c o r
  o a b

def k : FreeMagma α 2 := .var 0

def s : FreeMagma α 3 := .op (.op (.var 0) (.var 2)) (.op (.var 1) (.var 2))

end FreeMagma
