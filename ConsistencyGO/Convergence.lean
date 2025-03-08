import Mathlib

open MeasureTheory Filter Topology

namespace Measure

variable {α β : Type*} [MeasurableSpace α] [Dist β] (μ : Measure α)

def tendsto (fn : ℕ → α → β) (f : α → β) : Prop :=
    ∀ ε > 0, Tendsto (fun n => μ {x | dist (fn n x) (f x) > ε}) atTop (𝓝 0)


end Measure
