import Mathlib.Data.Fintype.Basic
import ConsistencyGO.Fintype

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

variable (u : ℕ → α)

def toTuple (n : ℕ) : Fin n → α := fun i => u i.val

end Tuple
