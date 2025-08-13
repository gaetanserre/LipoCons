/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Probability.Kernel.Defs

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (κ : Kernel α β) (μ : Measure α)

noncomputable def avg : Measure β := by
  refine Measure.ofMeasurable (fun s hs => ∫⁻ a, κ a s ∂μ) ?_ ?_
  · simp only [measure_empty, lintegral_const, zero_mul]
  · intro f f_m f_d
    simp_rw [fun x => measure_iUnion f_d f_m]
    exact lintegral_tsum (fun i => (κ.measurable_coe <| f_m i).aemeasurable)

@[simp]
lemma avg_apply {s : Set β} (hs : MeasurableSet s) : (avg κ μ) s = ∫⁻ a, κ a s ∂μ := by
  rw [avg, Measure.ofMeasurable_apply _ hs]

instance [IsMarkovKernel κ] [IsProbabilityMeasure μ] : IsProbabilityMeasure (avg κ μ) := by
  sorry

end ProbabilityTheory.Kernel
