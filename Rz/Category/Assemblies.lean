import Rz.Syntax.Magma
import Rz.Algebra.PCA

universe u v w

variable {α β γ : Type u}

structure Assembly (α : Type u) (β : Type v) where
  Realize : β → α → Prop

