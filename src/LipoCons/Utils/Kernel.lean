/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.Tuple
import Mathlib

set_option maxHeartbeats 0

open MeasureTheory

namespace ProbabilityTheory.Kernel

section avg

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (κ : Kernel α β) (μ : Measure α)

noncomputable def avg : Measure β := by
  refine Measure.ofMeasurable (fun s hs => ∫⁻ a, κ a s ∂μ) ?_ ?_
  · simp only [measure_empty, MeasureTheory.lintegral_const, zero_mul]
  · intro f f_m f_d
    simp_rw [fun x => measure_iUnion f_d f_m]
    exact lintegral_tsum (fun i => (κ.measurable_coe <| f_m i).aemeasurable)

@[simp]
lemma avg_apply {s : Set β} (hs : MeasurableSet s) : (avg κ μ) s = ∫⁻ a, κ a s ∂μ := by
  rw [avg, Measure.ofMeasurable_apply _ hs]

instance [IsMarkovKernel κ] [IsProbabilityMeasure μ] : IsProbabilityMeasure (avg κ μ) := by
  sorry

end avg

section traj

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))) {a b : ℕ}
  (hab : a ≤ b) [∀ n, IsMarkovKernel (κ n)] (μ : Measure (Π i : Finset.Iic a, X i))

open Set Function Tuple

lemma partialTraj_avg_rect_eq {C : (i : Finset.Iic b) → Set (X i)} (hC : ∀ i, MeasurableSet (C i)) :
    (partialTraj κ a b).avg μ (univ.pi C) =
    ∫⁻ u in univ.pi (fun (i : Finset.Iic a) => C ⟨i.1, mem_iic_le hab i.2⟩),
      (partialTraj κ a b) u (univ.pi C) ∂μ := by
  have : MeasurableSet (univ.pi C) := MeasurableSet.univ_pi hC
  rw [Kernel.avg_apply _ _ this]
  rw [← lintegral_indicator (MeasurableSet.univ_pi fun i ↦ hC ⟨i.1, mem_iic_le hab i.2⟩) _]
  congr with u
  by_cases hu : u ∈ univ.pi (fun (i : Finset.Iic a) => C ⟨i.1, mem_iic_le hab i.2⟩)
  · simp [hu]
  · simp only [hu, not_false_eq_true, indicator_of_notMem]
    rw [← lintegral_indicator_one this]
    rw [partialTraj_eq_prod, lintegral_map, lintegral_id_prod, lintegral_map]
    · simp [IicProdIoc_def]
      suffices ∀ (x : Π i : Finset.Iic b, X i),
          (fun (i : Finset.Iic b) ↦
          if h : i.1 ≤ a then u ⟨i.1, Finset.mem_Iic.mpr h⟩
          else x i) ∉ univ.pi C by
        simp [this]
      intro x x_mem
      simp_all only [Subtype.forall, Finset.mem_Iic, mem_pi, not_forall]
      obtain ⟨i, hi, -, hui⟩ := hu
      specialize x_mem i (Nat.le_trans hi hab) trivial
      simp_all only [↓reduceDIte]
    · exact Finset.measurable_restrict₂ Finset.Ioc_subset_Iic_self
    · refine Measurable.indicator measurable_const ?_
      have t : Measurable (fun x => IicProdIoc a b (u, x)) := by fun_prop
      exact t this
    · refine Measurable.indicator measurable_const ?_
      have tt : Measurable (fun (x : (Π i : Finset.Iic a, X i) × (Π i : Finset.Ioc a b, X i)) =>
        IicProdIoc a b x) := by fun_prop
      exact tt this
    · fun_prop
    · exact Measurable.indicator measurable_const this

end traj



end ProbabilityTheory.Kernel
