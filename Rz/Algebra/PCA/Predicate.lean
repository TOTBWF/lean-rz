import Mathlib.Init.Order.Defs
import Mathlib.Order.Notation
import Mathlib.Tactic.Use

import Rz.Algebra.PCA
import Rz.Category.Pullback
import Rz.Order.PreHeyting

universe u v w

/-!
# P(A) valued predicates.
-/

namespace PCA

open PAS

def Predicate (α : Type u) [PCA α] (X : Type v) := X → Val α → Prop

@[ext]
lemma Predicate.ext [PCA α] {P Q : Predicate α X} (h : ∀ x a, P x a ↔ Q x a) : P = Q := by
  unfold Predicate
  ext
  apply h

variable {α W X Y Z : Type u} [A : PCA α]

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

@[aesop norm]
def baseChange
    {α : Type u} {X : Type v} {Y : Type w} [PCA α]
    (f : X → Y) (P : Predicate α Y) : Predicate α X :=
  fun x a => P (f x) a

postfix:max "^*" => baseChange

@[simp]
lemma base_change_id
  {P : Predicate α X}
  : id ^* P = P := by aesop

@[simp]
lemma base_change_comp
  {P : Predicate α Z}
  {f : Y → Z} {g : X → Y}
  : (f ∘ g) ^* P = g^* (f^* P) := by aesop

/-- Base change preserves chosen meets. -/
lemma inf_base_change_le_base_change_inf
  {f : X → Y} {P Q : Predicate α Y}
  : (f^* P ⊓ f^* Q) ≤ f^* (P ⊓ Q) := by
  use A.id ⇓
  intro x a ⟨ l , r , eq , px , qx ⟩
  refine ⟨ ?_, ⟨ l, r, ?_, px, qx ⟩ ⟩ <;> aesop

/-- Base change preserves chosen joins. -/
lemma base_change_sup_le_sup_base_change
    {f : X → Y} {P Q : Predicate α Y}
    : f^* (P ⊔ Q) ≤ (f^* P ⊔ f^* Q) := by
  use A.id ⇓
  intro x a pqx
  match pqx with
  | Or.inl ⟨ la, eq, px ⟩ =>
    refine ⟨ ?_, Or.inl ⟨ la, ?_, px ⟩ ⟩ <;> aesop
  | Or.inr ⟨ ra, eq, qx ⟩ =>
    refine ⟨ ?_, Or.inr ⟨ ra, ?_, qx ⟩ ⟩ <;> aesop

/-- Base change preserves heyting implication. -/
lemma himp_base_change_le_base_change_himp
    {f : X → Y} {P Q : Predicate α Y}
    : (f^* P ⇨ f^* Q) ≤ f^* (P ⇨ Q) := by
  use A.id ⇓
  intro x a pqx
  refine ⟨ ?_, ?_ ⟩
  · aesop
  · intro b px
    have ⟨ _ , qx ⟩ := pqx b px
    aesop


/-!
Existentials
-/

def Existential (f : X → Y) (P : Predicate α X) : Predicate α Y :=
  fun y a => ∃ (x : X), f x = y ∧ P x a

scoped notation "⨿ " f:min ", " P:max => Existential f P

lemma exists_intro
    {f : X → Y} {P : Predicate α X} {Q : Predicate α Y}
    : P ≤ f^* Q → ⨿ f, P ≤ Q := by
  intro ⟨ a , a_rz ⟩
  use a
  rintro y b ⟨ x , rfl , pxb ⟩
  exact a_rz x b pxb

lemma exists_elim
    {f : X → Y} {P : Predicate α X} {Q : Predicate α Y}
    : ⨿ f, P ≤ Q → P ≤ f^* Q := by
  intro ⟨ a , a_rz ⟩
  use a
  intro x b pxb
  exact a_rz (f x) b ⟨ x , rfl, pxb ⟩

lemma exists_map
    {f : X → Y} {P Q : Predicate α X}
    : P ≤ Q → ⨿ f, P ≤ ⨿ f, Q := by
  intro ⟨ a , a_rz ⟩
  use a
  rintro y b ⟨ x , rfl , pxb ⟩
  have ⟨ d , qxb ⟩ := a_rz x b pxb
  refine ⟨ d, ⟨ x , rfl , qxb ⟩ ⟩

lemma exists_beck_chevalley
    {v : W → X} {r : W → Y} {s : X → Z} {u : Y → Z}
    {P : Predicate α Y}
    (pb : IsPullbackSquare v r s u)
    : s^* (⨿ u, P) ≤ ⨿ v, (r^* P) := by
  use A.id ⇓
  intro x a ⟨ y , eq , py ⟩
  let w := pb.invFun ⟨ x, y, symm eq ⟩
  refine ⟨ ?_, ⟨ w , ?_, ?_ ⟩ ⟩ <;> aesop

def Universal (f : X → Y) (P : Predicate α X) : Predicate α Y :=
  fun y a => ∀ (x : X) (b : Val α), (f x = y) → ∃ (h : A.ap a b ↓), P x ⟨ A.ap a b , h ⟩

scoped notation "∏ " f:min ", " P:max => Universal f P

lemma forall_intro
    {f : X → Y} {P : Predicate α Y} {Q : Predicate α X}
    : f^* P ≤ Q → P ≤ ∏ f, Q := by
  intro ⟨ a , a_rz ⟩
  use («pca» fun x y => a x) ⇓
  intro y b pxb
  refine ⟨ ?_, ?_ ⟩
  · aesop
  · rintro x c rfl
    have ⟨ _ , qxab ⟩ := a_rz x b pxb
    aesop

lemma forall_elim
    {f : X → Y} {P : Predicate α Y} {Q : Predicate α X}
    : P ≤ ∏ f, Q → f^* P ≤ Q := by
  intro ⟨ a , a_rz ⟩
  use («pca» fun x => a x A.const) ⇓
  intro x b pxb
  have ⟨ _ , pres_rz ⟩ := a_rz (f x) b pxb
  have ⟨ _ , qx ⟩ := pres_rz x (A.const ⇓) rfl
  aesop

lemma forall_map
    {f : X → Y} {P Q : Predicate α X}
    : P ≤ Q → ∏ f, P ≤ ∏ f, Q := by
  intro ⟨ a , a_rz ⟩
  use («pca» fun x y => a (x y)) ⇓
  intro y b pyb
  simp
  rintro x c rfl
  simp
  have ⟨ _ , pxbc ⟩ := pyb x c rfl
  have ⟨ _ , qxbc ⟩ := a_rz _ _ pxbc
  aesop

lemma forall_beck_chevalley
    {v : W → X} {r : W → Y} {s : X → Z} {u : Y → Z}
    {P : Predicate α Y}
    (pb : IsPullbackSquare v r s u)
    : ∏ v, (r^* P) ≤ s^* (∏ u, P) := by
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

def Generic (α : Type u) [PCA α] : Type u := Val α → Prop

notation "Ω" => Generic

def Proof : Predicate α (Ω α) := fun P a => P a

def classify (P : Predicate α X) : X → Ω α := fun x a => P x a

def le_classify
    {P : Predicate α X}
    : P ≤ (classify P)^* Proof := by
  use A.id ⇓
  aesop

def classify_le
    {P : Predicate α X}
    : (classify P)^* Proof ≤ P := by
  use A.id ⇓
  aesop
