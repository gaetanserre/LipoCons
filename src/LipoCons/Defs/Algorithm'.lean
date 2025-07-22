/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.Tuple
import LipoCons.Defs.NPos
import Mathlib

open MeasureTheory ProbabilityTheory

namespace Tuple

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def prod_eval (f : α → β) (n : ℕ) (u : Fin n → α) := (u, f ∘ u)

lemma measurable_prod_eval {f : α → β} (hf : Measurable f) (n : ℕ) :
    Measurable (prod_eval f n) := by
  refine Measurable.prodMk measurable_id ?_
  unfold Function.comp
  apply measurable_pi_lambda
  intro a
  apply Measurable.comp'
  · exact hf
  · exact measurable_pi_apply _

end Tuple

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (κ : Kernel α β) (μ : Measure α)

noncomputable def avg : Measure β := by
  refine Measure.ofMeasurable (fun s hs => ∫⁻ a, κ a s ∂μ) ?_ ?_
  · simp only [measure_empty, MeasureTheory.lintegral_const, zero_mul]
  intro f f_m f_d
  simp_rw [fun x => measure_iUnion f_d f_m]
  refine lintegral_tsum ?_
  intro i
  specialize f_m i
  exact (κ.measurable_coe f_m).aemeasurable

@[simp]
lemma avg_apply {s : Set β} (hs : MeasurableSet s) :
  κ.avg μ s = ∫⁻ a, κ a s ∂μ := Measure.ofMeasurable_apply s hs

end ProbabilityTheory.Kernel

structure Algo (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  measure_iter (n : ℕ₀) : Kernel ((Fin n → α) × (Fin n → β)) α

namespace Algo

open Tuple

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (A : Algo α β)

noncomputable def tt {n : ℕ} (i : Fin (n + 1)) {f : α → β} (hf : Measurable f) :=
  if h : i.1 = 0 then A.ν
  else by
    let μ : Measure (Fin i → α) := by
      refine Measure.pi ?_
      intro i'
      exact tt ⟨i', Nat.lt_trans i'.2 i.2⟩ hf
    push_neg at h
    let κ := (A.measure_iter ⟨i, Nat.zero_lt_of_ne_zero h⟩).comap (prod_eval f i) (measurable_prod_eval hf i)
    exact κ.avg μ

noncomputable def test (n : ℕ₀) {f : α → β} (hf : Measurable f) : Measure (Fin (n + 1) → α) := by
  refine Measure.pi (fun i => A.tt i hf)

example {f g : α → β} (hf : Measurable f) (hg : Measurable g) {s : Set α}
    (hs : MeasurableSet s) (h : s.restrict f = s.restrict g) (n : ℕ₀) :
    A.test n hf {u | ∀ i, u i ∉ sᶜ} = A.test n hg {u | ∀ i, u i ∉ sᶜ} := by
  set us := {u : Fin (n + 1) → α | ∀ i, u i ∉ sᶜ}
  have : us = Set.univ.pi (fun _ => s) := by sorry
  rw [this, test.eq_def, test.eq_def]
  have : ∀ (i : Fin (n + 1)), SigmaFinite (A.tt i hf) := by sorry
  have : ∀ (i : Fin (n + 1)), SigmaFinite (A.tt i hg) := by sorry
  rw [Measure.pi_pi, Measure.pi_pi]
  congr
  ext i
  induction i using Fin.induction with
  | zero =>
    simp only [tt, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceDIte]
  | succ i hi =>
    have : i.succ.1 ≠ 0 := (Nat.zero_ne_add_one i).symm
    rw [tt, tt]
    split
    · contradiction
    set μf := Measure.pi fun (i' : Fin i.succ) ↦ A.tt (⟨i', Nat.lt_trans i'.2 i.succ.2⟩ : Fin (n + 1)) hf
    let κ := (A.measure_iter ⟨i.succ, Nat.zero_lt_of_ne_zero this⟩)
    set κf_comap := κ.comap (prod_eval f i.succ) (measurable_prod_eval hf i.succ)

    set μg := Measure.pi fun (i' : Fin i.succ) ↦ A.tt (⟨i', Nat.lt_trans i'.2 i.succ.2⟩ : Fin (n + 1)) hg
    set κg_comap := κ.comap (prod_eval g i.succ) (measurable_prod_eval hg i.succ)
    simp only

    rw [κf_comap.avg_apply _ hs, κg_comap.avg_apply _ hs]

    simp only [Fin.val_succ, Kernel.coe_comap, Function.comp_apply, κf_comap, κg_comap]






    sorry

end Algo
