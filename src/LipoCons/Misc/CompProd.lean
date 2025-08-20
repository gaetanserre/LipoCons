import LipoCons.Utils.Kernel
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open MeasureTheory Finset ENNReal Function

namespace ProbabilityTheory.Kernel

section compProd

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] {n : ℕ}

lemma lintegral_section_eq_indicator_prod (μ : Measure (Π i : Iic n, X i))
    (ν : (Π i : Iic n, X i) → Measure ((n : ℕ) → X n))
    {s : Set ((Π i : Iic n, X i) × ((n : ℕ) → X n))} (hs : MeasurableSet s) :
    ∫⁻ a, ν a (Prod.mk a ⁻¹' s) ∂μ = ∫⁻ a, ∫⁻ b, s.indicator 1 (a, b) ∂ν a ∂μ := by
  suffices ∀ a, ν a (Prod.mk a ⁻¹' s) = ∫⁻ b, s.indicator 1 (a, b) ∂ν a by
    simp_rw [this]
  intro a
  rw [←lintegral_indicator_one <| hs.preimage measurable_prodMk_left]
  suffices ∀ b, ((Prod.mk a ⁻¹' s).indicator 1 b : ℝ≥0∞) = s.indicator 1 (a, b) by
    simp_rw [this]
  intro b
  rfl

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)] {a b : ℕ}
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))}
  [∀ n, IsMarkovKernel (κ n)] (a : ℕ) (μ : Measure (Π i : Iic a, X i))
  [SFinite μ]

theorem lintegral_traj {a : ℕ} (x₀ : Π i : Iic a, X i) {f : (Π n, X n) → ℝ≥0∞}
    (mf : Measurable f) :
    ∫⁻ x, f x ∂traj κ a x₀ = ∫⁻ x, f (updateFinset x (Iic a) x₀) ∂traj κ a x₀ := by
  nth_rw 1 [← traj_map_updateFinset, MeasureTheory.lintegral_map]
  · exact mf
  · fun_prop

def e : ((n : ℕ) → X n) → (Π i : Iic a, X i) × ((n : ℕ) → X n) :=
  fun x => (fun i => x i, x)

lemma e_m : Measurable (e (X := X) a) := Measurable.prod (by fun_prop) (by fun_prop)

lemma compProd_eq_map_avg : μ.compProd (Kernel.traj κ a) = ((Kernel.traj κ a).avg μ).map (e a) := by
  set e := e a
  ext t ht
  rw [((Kernel.traj κ a).avg μ).map_apply (e_m a) ht]
  have e_pre_m : MeasurableSet (e ⁻¹' t) := e_m a ht
  rw [μ.compProd_apply, (Kernel.traj κ a).avg_apply μ e_pre_m,
    lintegral_section_eq_indicator_prod μ (Kernel.traj κ a)]
  simp_rw [← lintegral_indicator_one e_pre_m]
  congr with x
  rw [lintegral_traj]
  nth_rw 2 [lintegral_traj]
  congr with b
  have : (x, updateFinset b (Iic a) x) = e (updateFinset b (Iic a) x) := by
    ext i
    · simp only [updateFinset_def, mem_Iic, Kernel.e, left_eq_dite_iff, not_le, e]
      intro hi
      have : i.1 ≤ a := mem_Iic.mp i.2
      linarith
    · rfl
  by_cases h : updateFinset b (Iic a) x ∈ e ⁻¹' t
  · simp only [h, Set.indicator_of_mem, Pi.one_apply]
    suffices (x, updateFinset b (Iic a) x) ∈ t by
      simp [this]
    rw [Set.mem_preimage] at h
    rwa [this]
  · simp only [h, not_false_eq_true, Set.indicator_of_notMem, Set.indicator_apply_eq_zero,
      Pi.one_apply, one_ne_zero, imp_false]
    rw [Set.mem_preimage] at h
    rwa [this]
  · exact Measurable.indicator measurable_const e_pre_m
  · suffices Measurable (uncurry (fun x b => t.indicator 1 (x, b))) by
      exact Measurable.of_uncurry_left (this)
    exact Measurable.indicator measurable_const ht
  all_goals exact ht

end compProd

/- section compProd2

variable {α : Type*} [MeasurableSpace α] {a b : ℕ}
  {κ : (n : ℕ) → Kernel (Iic n → α) α}
  [∀ n, IsMarkovKernel (κ n)] (a : ℕ) (μ : Measure (Iic a → α))
  [SFinite μ]

def mequiv : (Iic a → α) × (ℕ → α) ≃ᵐ (ℕ → α) where
  toFun := fun x i => if h : i ∈ Iic a then x.1 ⟨i, h⟩ else x.2 (i - 1 - a)
  invFun := fun x => (fun i => x i, fun i => x (i + 1 + a))
  measurable_toFun := by
    refine measurable_pi_lambda _ ?_
    intro i
    simp only [mem_Iic, Equiv.coe_fn_mk]
    split_ifs with h
    · fun_prop
    · fun_prop
  measurable_invFun := by
    refine Measurable.prod ?_ ?_
    · fun_prop
    · fun_prop
  left_inv x := by
    ext i
    · simp
    · simp
  right_inv x := by
    ext i
    simp only [mem_Iic, dite_eq_ite, ite_eq_left_iff, not_le]
    intro h
    congr
    omega

lemma compProd_eq_map_avg' : (μ.compProd (Kernel.traj (X := fun _ => α) κ a)).map (mequiv a) =
    (Kernel.traj κ a).avg μ := by
  set e := mequiv (α := α) a
  ext t ht
  rw [Measure.map_apply]
  have e_pre_m : MeasurableSet (e ⁻¹' t) := e.measurableSet_preimage.mpr ht
  rw [μ.compProd_apply, Kernel.avg_apply,
    lintegral_section_eq_indicator_prod (X := fun _ => α)]
  simp_rw [← lintegral_indicator_one ht]
  congr with x
  rw [lintegral_traj]
  nth_rw 2 [lintegral_traj]
  congr with b
  by_cases h : (x, updateFinset b (Iic a) x) ∈ e ⁻¹' t
  · simp [h]
    suffices updateFinset b (Iic a) x ∈ t by
      simp [this]
    rw [Set.mem_preimage] at h
    sorry
  · simp only [h, not_false_eq_true, Set.indicator_of_notMem]
    suffices updateFinset b (Iic a) x ∉ t by
      simp [this]
    rw [Set.mem_preimage] at h

    sorry
  /- have : e (x, updateFinset b (Iic a) x) = (updateFinset b (Iic a) x) := by
    ext i
    · simp [mem_Iic, e, mequiv]
      split_ifs with h₁ h₂
      · rfl
      · push_neg at h₁
        have : a ≤ a + a + 1 := by omega

        sorry

      sorry

    · rfl -/

  all_goals sorry

end compProd2 -/

end ProbabilityTheory.Kernel
