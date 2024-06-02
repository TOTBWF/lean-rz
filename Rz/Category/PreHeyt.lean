import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom


import Rz.Order.PreHeyting


/-!
# The category of pre-Heyting algebras
-/

universe u

open CategoryTheory

/-- The category of pre-Heyting algebras. -/
def PreHeyt :=
  Bundled PreHeyting

namespace PreHeyt

instance : CoeSort PreHeyt (Type*) :=
  Bundled.coeSort

instance (X : PreHeyt) : PreHeyting X :=
  X.str

def of (α : Type*) [PreHeyting α] : PreHeyt :=
  Bundled.of α

@[simp]
theorem coe_of (α : Type*) [PreHeyting α] : ↥(of α) = α :=
  rfl

instance bundledHom : BundledHom PreHeytingHom where
  toFun α β [PreHeyting α] [PreHeyting β] := (DFunLike.coe : PreHeytingHom α β → α → β)
  id := @PreHeytingHom.id
  comp := @PreHeytingHom.comp
  hom_ext α β [PreHeyting α] [PreHeyting β] := DFunLike.coe_injective

deriving instance LargeCategory for PreHeyt

instance : ConcreteCategory PreHeyt := by
  dsimp [PreHeyt]
  infer_instance

instance {X Y : PreHeyt.{u}} : FunLike (X ⟶ Y) ↑X ↑Y :=
  PreHeytingHom.instFunLike

instance {X Y : PreHeyt.{u}} : PreHeytingHomClass (X ⟶ Y) ↑X ↑Y :=
  PreHeytingHom.instPreHeytingHomClass

end PreHeyt
