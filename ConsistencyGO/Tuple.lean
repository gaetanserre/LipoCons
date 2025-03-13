/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Fintype
import Mathlib.Data.Fintype.Basic

variable {α : Type*}

namespace Tuple

variable [LinearOrder α] {n : ℕ} [Nonempty α] (f : Fin n → α)

noncomputable def max := Fintype.max_image f

lemma le_max (h : 0 < n) : ∀ j, f j ≤ max f := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  exact Fintype.le_max_image f

noncomputable def min := Fintype.min_image f

lemma le_min (h : 0 < n) : ∀ j, min f ≤ f j := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  exact Fintype.le_min_image f

end Tuple

namespace Tuple

def toTuple (n : ℕ) (u : ℕ → α) : Fin n → α := fun i => u i.val

def toTupleFun {β : Type*} (f : (n : ℕ) → (Fin n → α) → β) := fun n u => f n (toTuple n u)

end Tuple
