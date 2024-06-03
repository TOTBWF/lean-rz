import Mathlib.Init.Order.Defs
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Order.Notation
import Mathlib.Tactic.Use

import Rz.Algebra.PCA
import Rz.Category.Pullback
import Rz.Category.Tripos
import Rz.Order.PreHeyting
import Rz.Category.PreHeyt

universe u v w

/-!
# P(A) valued predicates.
-/

namespace PCA

open PAS
open CategoryTheory Opposite CategoricalLogic

def Predicate (α : Type u) [PCA α] (X : Type v) := X → Val α → Prop

variable {α W X Y Z : Type u} [A : PCA α]

@[ext]
lemma Predicate.ext {P Q : Predicate α X} (h : ∀ x a, P x a ↔ Q x a) : P = Q := by
  unfold Predicate
  ext
  apply h

instance {α : Type u} {X : Type v} [A : PCA α] : Preorder (Predicate α X) where
  le P Q := ∃ (f : Val α), ∀ (x : X), ∀ (a : Val α), P x a → ∃ (h : (A.ap f a) ↓), Q x ⟨ A.ap f a , h ⟩
  le_refl P := ⟨ A.id ⇓, by aesop ⟩
  le_trans P Q R := by
    intro ⟨ f , f_rz ⟩ ⟨ g , g_rz ⟩
    use ap (ap (A.comp) f) g ⇓
    intro x a px
    have ⟨ fa_def, qx ⟩ := f_rz x a px
    have ⟨ gfa_def, qx ⟩ := g_rz x (A.ap f a ⇓) qx
    aesop

instance {α : Type u} {X : Type v} [PCA α] : Top (Predicate α X) where
  top _ _ := True

instance {α : Type u} {X : Type v} [PCA α] : Bot (Predicate α X) where
  bot _ _ := False

instance {α : Type u} {X : Type v} [A : PCA α] : Inf (Predicate α X) where
  inf P Q x a := ∃ (l : Val α), ∃ (r : Val α), (a = ap (ap A.pair l) r) ∧ P x l ∧ Q x r

instance {α : Type u} {X : Type v} [A : PCA α] : Sup (Predicate α X) where
  sup P Q x a := (∃ (l : Val α), (a = ap A.inl l) ∧ P x l) ∨ (∃ (r : Val α), (a = ap A.inr r) ∧ Q x r)

instance {α : Type u} {X : Type v} [A : PCA α] : HImp (Predicate α X) where
  himp P Q x f := ∀ (a : Val α), P x a → ∃ (h : A.ap f a ↓), Q x ⟨ A.ap f a , h ⟩

instance {α : Type u} {X : Type v} [A : PCA α] : PreHeyting (Predicate α X) where
  le_top P := by
    use A.id ⇓
    intro x a _
    refine ⟨ ?_, True.intro ⟩
    aesop
  bot_le P := by
    use A.id ⇓
    intro x a ff
    nomatch ff
  inf_le_left P Q := by
    use A.fst ⇓
    rintro x ⟨ a , a_def ⟩ ⟨ l , r , rfl , px, _ ⟩
    aesop
  inf_le_right P Q := by
    use A.snd ⇓
    rintro x ⟨ a , a_def ⟩ ⟨ l , r , rfl , _, qx ⟩
    aesop
  le_inf P Q R := by
    intro ⟨ l , l_rz ⟩ ⟨ r , r_rz ⟩
    use («pca» fun x => ⟨ l x , r x ⟩) ⇓
    intro x a px
    have ⟨ la_def, qx ⟩ := l_rz x a px
    have ⟨ ra_def, rx ⟩ := r_rz x a px
    refine ⟨ ?_, ⟨ A.ap l a ⇓, A.ap r a ⇓, ?_, ?_, ?_ ⟩ ⟩ <;> aesop
  le_sup_left P Q := by
    use A.inl ⇓
    intro x a px
    refine ⟨ by simp, Or.inl ⟨ a, rfl, px ⟩ ⟩
  le_sup_right P Q := by
    use A.inr ⇓
    intro x a qx
    refine ⟨ by simp, Or.inr ⟨ a, rfl, qx ⟩ ⟩
  sup_le P Q R := by
    intro ⟨ l , l_rz ⟩ ⟨ r , r_rz ⟩
    use («pca» A.elim l r) ⇓
    intro x a pqx
    match pqx with
    | Or.inl ⟨ la, eq, px ⟩ =>
      have ⟨ la_def , rx ⟩ := l_rz x la px
      aesop
    | Or.inr ⟨ ra, eq, qx ⟩ =>
      have ⟨ ra_def , rx ⟩ := r_rz x ra qx
      aesop
  le_himp_iff P Q R := by
    constructor
    · intro ⟨ f , f_rz ⟩
      use (ap A.uncurry f) ⇓
      intro x ax ⟨ l , r , eq , px , qx ⟩
      have ⟨ d , qrx ⟩ := f_rz x l px
      have ⟨ d' , rx ⟩ := qrx r qx
      aesop
    · intro ⟨ f , f_rz ⟩
      use (ap A.curry f) ⇓
      intro x a px
      use (by aesop)
      intro b qx
      have ⟨ d , rx ⟩ := f_rz x (_ ⇓) ⟨ a, b , rfl, px, qx ⟩
      refine ⟨ ?_, ?_ ⟩
      · simpa using d
      · simpa using rx


/-!
# Base Change
-/

def baseChange {X Y : Type*} (f : X → Y) : PreHeytingHom (Predicate α Y) (Predicate α X) where
  toFun P := fun x a => P (f x) a
  monotone' := by
    intro P Q ⟨ a , a_rz ⟩
    use a
    intro x b px
    have ⟨ d , qx ⟩ := a_rz (f x) b px
    use d, qx
  map_le_bot' := by
    use A.id ⇓
    intro a x ff
    nomatch ff
  top_le_map' := by
    use A.id ⇓
    intro a x _
    constructor
    · trivial
    · simp
  map_le_sup' := by
    intro P Q
    use A.id ⇓
    intro x a pqx
    match pqx with
    | Or.inl ⟨ la, eq, px ⟩ =>
      refine ⟨ ?_, Or.inl ⟨ la, ?_, px ⟩ ⟩ <;> aesop
    | Or.inr ⟨ ra, eq, qx ⟩ =>
      refine ⟨ ?_, Or.inr ⟨ ra, ?_, qx ⟩ ⟩ <;> aesop
  inf_le_map' := by
    intro P Q
    use A.id ⇓
    intro x a ⟨ l , r , eq , px , qx ⟩
    refine ⟨ ?_, ⟨ l, r, ?_, px, qx ⟩ ⟩ <;> aesop
  himp_le_map' := by
    intro P Q
    use A.id ⇓
    intro x a pqx
    refine ⟨ ?_, ?_ ⟩
    · aesop
    · intro b px
      have ⟨ _ , qx ⟩ := pqx b px
      aesop

variable (α) in
def EffPred : Type u ᵒᵖ ⥤ PreHeyt.{u} where
  obj X := PreHeyt.of (Predicate α (unop X))
  map f := baseChange (unop f)

@[simp]
def EffPred.map_apply
    {X Y : Type u} {f : op X ⟶ op Y} {P : Predicate α X} {y : Y} {a : Val α}
    : (EffPred α).map f P y a = P ((unop f) y) a := rfl

/-!
## Existential quantification
-/

instance : ExistentialDoctrine (EffPred α) where
  Exists X Y f P := fun y a => ∃ (x : X), f x = y ∧ P x a
  exists_monotone := by
    intro X Y f P Q ⟨ a , a_rz ⟩
    use a
    rintro y b ⟨ x , rfl , pxb ⟩
    have ⟨ d , qxb ⟩ := a_rz x b pxb
    exact ⟨ d, ⟨ x , rfl , qxb ⟩ ⟩
  exists_left_adj := by
    intro X Y f P Q
    constructor
    · intro ⟨a, a_rz⟩
      use a
      intro x b pxb
      exact a_rz (f x) b ⟨ x , rfl, pxb ⟩
    · intro ⟨ a , a_rz ⟩
      use a
      rintro y b ⟨ x , rfl , pxb ⟩
      exact a_rz x b pxb
  exists_beck_chevalley := by
    intro W X Y Z v r s u P pb
    use A.id ⇓
    intro x a ⟨ y , eq , py ⟩
    let w := pb.invFun ⟨ x, y, symm eq ⟩
    refine ⟨ ?_, ⟨ w , ?_, ?_ ⟩ ⟩ <;> aesop

/-!
## Universal quantification
-/

instance : UniversalDoctrine (EffPred α) where
  Forall X Y f P := fun y a => ∀ (x : X) (b : Val α), (f x = y) → ∃ (h : A.ap a b ↓), P x ⟨ A.ap a b , h ⟩
  forall_monotone := by
    intro X Y f P Q ⟨a, a_rz⟩
    use ⟨ («pca» fun x y => a (x y)), by simp ⟩
    intro y b pyb
    simp
    rintro x c rfl
    have ⟨ _ , pxbc ⟩ := pyb x c rfl
    have ⟨ _ , qxbc ⟩ := a_rz _ _ pxbc
    constructor <;> simpa
  forall_right_adj := by
    intro X Y f P Q
    constructor
    · rintro ⟨ a , a_rz ⟩
      use ⟨ («pca» fun x y => a x), by simp ⟩
      intro y b pxb
      exists (by simp)
      rintro x c rfl
      obtain ⟨ d , qxab ⟩ := a_rz x b pxb
      constructor <;> simpa
    · intro ⟨ a , a_rz ⟩
      use ⟨ («pca» fun x => a x A.const), by simp ⟩
      intro x b pxb
      have ⟨ _ , pres_rz ⟩ := a_rz (f x) b pxb
      have ⟨ d , qx ⟩ := pres_rz x (A.const ⇓) rfl
      constructor <;> simpa
  forall_beck_chevalley := by
    introv pb
    use A.id ⇓
    intro x a px
    refine ⟨ ?_, ?_ ⟩
    · aesop
    · intro y b eq
      let w := pb.invFun ⟨ x , y, symm eq ⟩
      have ⟨ d , prw ⟩ := px w b (pb.fst_commute _)
      aesop

/-!
# Generic Objects
-/

instance : Tripos (EffPred α) where
  Generic := Val α → Prop
  Proof := fun P a => P a
  classify P := fun x a => P x a
  le_proof P := by use A.id ⇓; aesop
  proof_le P := by use A.id ⇓; aesop
