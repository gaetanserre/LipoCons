/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open Filter Topology

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [Dist β] (μ : Measure α)

def tendsto (fn gn : ℕ → α → β) : Prop :=
    ∀ ε > 0, Tendsto (fun n => μ {x | dist (fn n x) (gn n x) > ε}) atTop (𝓝 0)


end Measure
