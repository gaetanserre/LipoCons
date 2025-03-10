/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Fintype
import Mathlib.Data.Fintype.Basic

variable {α : Type*}

namespace Tuple

variable {β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β)

def image : Fin n → β := g ∘ f

end Tuple

namespace Tuple

variable [LinearOrder α] {n : ℕ} [Nonempty α] (f : Fin n → α)

noncomputable def max := Fintype.max_image f

lemma le_max (h : n > 0) : ∀ j, f j ≤ max f := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  exact Fintype.le_max_image f

end Tuple

namespace Tuple

def toTuple (n : ℕ) (u : ℕ → α) : Fin n → α := fun i => u i.val

def toTupleFun {β : Type*} (f : (n : ℕ) → (Fin n → α) → β) := fun n u => f n (toTuple n u)

end Tuple
