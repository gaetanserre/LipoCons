import ConsistencyGO.Fintype
import Mathlib.Data.Fintype.Basic

variable {α : Type*}

namespace Tuple

variable {β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β)

def image : Fin n → β := g ∘ f

end Tuple

namespace Tuple

variable [LinearOrder α] {n : ℕ} [Nonempty (Fin n)] (f : Fin n → α)

def max := Fintype.max_image f

lemma le_max : ∀ j, f j ≤ max f := Fintype.le_max_image f

end Tuple

namespace Tuple

def toTuple (u : ℕ → α) (n : ℕ) : Fin n → α := fun i => u i.val

def toTupleFun {β : Type*} (f : (n : ℕ) → (Fin n → α) → β) := fun n u => f n (toTuple u n)

end Tuple
