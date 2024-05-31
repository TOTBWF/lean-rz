/-!
# Inductive Fin

We are Agda now 🐔
-/

variable {α β γ : Type _}

inductive Idx : Nat → Type where
| zero : {n : Nat} → Idx (n + 1)
| succ : {n : Nat} → Idx n → Idx (n + 1)

namespace Idx

def ofNat {n : Nat} : (k : Nat) → Idx (n + k + 1)
| 0 => .zero
| k+1 => .succ (ofNat k)

instance {n : Nat} : OfNat (Idx (n + 1)) 0 where
  ofNat := .zero

instance {n k : Nat} [N : OfNat (Idx n) k] : OfNat (Idx (n + 1)) (k + 1) where
  ofNat := .succ N.ofNat


def ofFin : {n : Nat} → Fin n → Idx n
| n+1, ⟨ 0 , _ ⟩ => zero
| n+1, ⟨ k+1 , h ⟩ => succ (@ofFin n ⟨ k , by omega ⟩)


end Idx

namespace List

@[simp] def getIdx : (as : List α) → (i : Idx as.length) → α
| (a :: _), .zero => a
| (_ :: as), .succ i => getIdx as i

end List
