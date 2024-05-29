import Rz.Syntax.Subst
import Rz.Data.Bwd

inductive Tp : Type where
| prod : Tp → Tp → Tp
| fn : Tp → Tp → Tp
| prop : Tp

inductive Tm : Type where
| var : Nat → Tm
| pair : Tm → Tm → Tm
| fst : Tm → Tm
| snd : Tm → Tm
| lam : Tm → Tm
| app : Tm → Tm → Tm
| and : Tm → Tm → Tm
| or : Tm → Tm → Tm
| implies : Tm → Tm → Tm
| true : Tm
| false : Tm
| all : Tp → Tm → Tm
| some : Tp → Tm → Tm
| eq : Tp → Tm → Tm → Tm

namespace Tm

def subst (e : Tm) (σ : Sb Tm) : Tm :=
  sorry
-- match tm with
-- | var => _
-- | pair e₁ e₂ => _
-- | fst e => _
-- | snd : Tm → Tm
-- | lam : Tm → Tm
-- | app : Tm → Tm → Tm
-- | and : Tm → Tm → Tm
-- | or : Tm → Tm → Tm
-- | implies : Tm → Tm → Tm
-- | true : Tm
-- | false : Tm
-- | all : Tp → Tm → Tm
-- | some : Tp → Tm → Tm
-- | eq : Tp → Tm → Tm → Tm

end Tm

instance : Var Tm where
  var := Tm.var

-- TODO: Ford this :(
inductive Entails : Bwd Tp → Bwd Tm → Tm → Type where
| and.intro     : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q : Tm} → Entails Γ φ p → Entails Γ φ q → Entails Γ φ (Tm.and p q)
| and.eliml     : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q : Tm} → Entails Γ φ (Tm.and p q) → Entails Γ φ p
| and.elimr     : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q : Tm} → Entails Γ φ (Tm.and p q) → Entails Γ φ q
| or.introl     : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q : Tm} → Entails Γ φ p → Entails Γ φ (Tm.or p q)
| or.intror     : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q : Tm} → Entails Γ φ q → Entails Γ φ (Tm.or p q)
| or.elim       : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q r : Tm} → Entails Γ φ (Tm.or p q) → Entails Γ (φ :# p) r → Entails Γ (φ :# q) r → Entails Γ φ r
| implies.intro : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q : Tm} → Entails Γ (φ :# p) q → Entails Γ φ (Tm.implies p q)
| implies.elim  : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p q : Tm} → Entails Γ φ (Tm.implies p q) → Entails Γ φ p → Entails Γ φ q
| true.intro    : {Γ : Bwd Tp} → {φ : Bwd Tm} → Entails Γ φ Tm.true
| false.elim    : {Γ : Bwd Tp} → {φ : Bwd Tm} → {p : Tm} → Entails Γ φ Tm.false → Entails Γ φ p
| all.intro     : {Γ : Bwd Tp} → {φ : Bwd Tm} → {A : Tp} → {p : Tm} → Entails (Γ :# A) φ p → Entails Γ φ (Tm.all A p)
| all.elim      : {Γ : Bwd Tp} → {φ : Bwd Tm} → {A : Tp} → {p : Tm} → Entails Γ φ (Tm.all A p) → (a : Tm) → Entails Γ φ (p.subst (Sb.id ;; a))
| some.intro    : {Γ : Bwd Tp} → {φ : Bwd Tm} → {A : Tp} → {p : Tm} → (a : Tm) → Entails Γ φ (p.subst (Sb.id ;; a)) → Entails Γ φ (Tm.some A p)
| some.elim     : {Γ : Bwd Tp} → {φ : Bwd Tm} → {A : Tp} → {p : Tm} → Entails Γ φ (Tm.some A p) → Entails (Γ :# A) φ p
| eq.intro      : {Γ : Bwd Tp} → {φ : Bwd Tm} → (A : Tp) → (a : Tm) → Entails Γ φ (Tm.eq A a a)
| eq.elim       : {Γ : Bwd Tp} → {φ : Bwd Tm} → {A : Tp} → {a b : Tm} → {p : Tm} → Entails Γ φ (Tm.eq A a b) → Entails Γ φ (p.subst (Sb.id ;; a)) → Entails Γ φ (p.subst (Sb.id ;; b))
