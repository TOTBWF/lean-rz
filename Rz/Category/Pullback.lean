import Mathlib.Tactic.TypeStar
import Mathlib.Logic.Equiv.Defs

open Function

/-!
# Pullbacks of types.
-/

/-- Canonical pullbacks in Set. -/
structure Pullback {X Y Z : Type*} (f : X → Z) (g : Y → Z) : Type _ where
  fst : X
  snd : Y
  commutes : f fst = g snd

namespace Pullback

def univ
  {P X Y Z : Type*} {f : X → Z} {g : Y → Z}
  (p1 : P → X) (p2 : P → Y)
  (square : ∀ p, f (p1 p) = g (p2 p))
  : P → Pullback f g := fun p => ⟨ p1 p, p2 p, square p ⟩

end Pullback

-- FIXME: This should use some variant of IsEquiv/IsIso
/-- A square of maps is a pullback square if it commutes and the map into the canonical pullback is an iso. -/
structure IsPullbackSquare {P X Y Z : Type*} (p1 : P → X) (p2 : P → Y) (f : X → Z) (g : Y → Z) : Type _ where
  square : ∀ p, f (p1 p) = g (p2 p)
  invFun : Pullback f g → P
  left_inv : LeftInverse invFun (Pullback.univ p1 p2 square)
  right_inv : RightInverse invFun (Pullback.univ p1 p2 square)

namespace IsPullbackSquare

variable {P X Y Z : Type*} {p1 : P → X} {p2 : P → Y} {f : X → Z} {g : Y → Z}

@[simp] lemma fst_commute
    (pb : IsPullbackSquare p1 p2 f g)
    (p : Pullback f g)
    : p1 (pb.invFun p) = p.fst :=
  congrArg Pullback.fst (pb.right_inv p)

@[simp] lemma snd_commute
    (pb : IsPullbackSquare p1 p2 f g)
    (p : Pullback f g)
    : p1 (pb.invFun p) = p.fst :=
  congrArg Pullback.fst (pb.right_inv p)

end IsPullbackSquare
