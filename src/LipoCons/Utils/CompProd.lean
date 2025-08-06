/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Defs.Iter
import LipoCons.Utils.Tuple
import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory Set ENNReal Tuple

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

lemma lintegral_section_eq_indicator_prod (μ : Measure (iter α n))
    (ν : iter α n → Measure α) {s : Set (iter α n × α)} (hs : MeasurableSet s) :
    ∫⁻ a, ν a (Prod.mk a ⁻¹' s) ∂μ = ∫⁻ a, ∫⁻ b, s.indicator 1 (a, b) ∂ν a ∂μ := by
  suffices ∀ a, ν a (Prod.mk a ⁻¹' s) = ∫⁻ b, s.indicator 1 (a, b) ∂ν a by
    simp_rw [this]
  intro a
  rw [←lintegral_indicator_one <| hs.preimage measurable_prodMk_left]
  suffices ∀ b, ((Prod.mk a ⁻¹' s).indicator 1 b : ℝ≥0∞) = s.indicator 1 (a, b) by
    simp_rw [this]
  intro b
  rfl

lemma lintegral_pi_section_eq_indicator_pi (μ : Measure (iter α n))
    (ν : iter α n → Measure α) {s : Set (iter α (n + 1))} (hs : MeasurableSet s) :
    ∫⁻ a, ν a (Prod.mk a ⁻¹' ((iter_mequiv α n) '' s)) ∂μ =
    ∫⁻ a, ∫⁻ b, s.indicator 1 (append a b) ∂ν a ∂μ := by
  set s' := (iter_mequiv α n) '' s
  have : MeasurableSet s' :=
    (iter_mequiv α n).measurableSet_image.mpr hs
  rw [lintegral_section_eq_indicator_prod μ ν ((iter_mequiv α n).measurableSet_image.mpr hs)]
  suffices ∀ a b, (s'.indicator 1 (a, b) : ℝ≥0∞) = s.indicator 1 (append a b) by
    simp_all only [MeasurableEquiv.measurableSet_image, s']
  intro a b
  refine indicator_eq_indicator ?_ rfl
  simp only [s']
  constructor
  · rintro ⟨y, y_mem, hy⟩
    have : y = (iter_mequiv α n).symm (a, b) := EquivLike.inv_apply_eq.mp hy
    rw [this] at y_mem
    suffices append a b = (iter_mequiv α n).symm (a, b) by
      rwa [this]
    show append a b = Fin.insertNth (Fin.last (n + 1)) (b, a).1 (b, a).2
    simp only [append]
    ext i
    simp only [Fin.insertNth_last']
  · intro h_pi
    simp only [mem_image]
    refine ⟨append a b, h_pi, ?_⟩
    set u := append a b
    let e : α × iter α n ≃ᵐ iter α n × α := MeasurableEquiv.prodComm
    show e ((u (Fin.last (n + 1)), Fin.removeNth (Fin.last (n + 1)) u)) = (a, b)
    simp only [Fin.snoc_last, Fin.removeNth_last, Fin.init_snoc, u]
    rfl

open ProbabilityTheory in
lemma MeasureTheory.Measure.compProd_apply' (μ : Measure (iter α n)) [SFinite μ]
    (κ : Kernel (iter α n) α) [IsSFiniteKernel κ]
    {s : Set (iter α (n + 1))} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).comap (iter_mequiv α n) s = ∫⁻ a, ∫⁻ b, s.indicator 1 (append a b) ∂κ a ∂μ := by
  rw [Measure.comap_apply (iter_mequiv α n) (iter_mequiv α n).injective ?_ _ hs]
  swap
  · exact fun _ hs => (iter_mequiv α n).measurableSet_image.mpr hs
  rw [Measure.compProd_apply ((iter_mequiv α n).measurableSet_image.mpr hs)]
  exact lintegral_pi_section_eq_indicator_pi μ κ hs
