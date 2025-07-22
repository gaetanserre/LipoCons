/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib

open MeasureTheory

structure QuasiKernel (α β : Type*) [MeasurableSpace β] where
  toFun : α → Measure β

namespace QuasiKernel

instance {α β : Type*} [MeasurableSpace β] : FunLike (QuasiKernel α β) α (Measure β) where
  coe := QuasiKernel.toFun
  coe_injective' f g h := by cases f; cases g; congr

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace ι] (κ : QuasiKernel (α × β) ι)

example (μ : Measure α) (f : α → α × β) : Measure ι := by
  refine Measure.ofMeasurable (fun s _ => ∫⁻ x, κ (f x) s ∂ μ) ?_ ?_
  · simp only [measure_empty, lintegral_const, zero_mul]
  · intro g g_m g_d
    simp_rw [fun x => measure_iUnion g_d g_m]
    refine lintegral_tsum ?_
    sorry



end QuasiKernel
