/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Order.Lattice

open NNReal

variable {α β : Type*}

/-! A wrapper around `LipschitzWith` of Mathlib. A function is `Lipschitz` if it exists
a `K : ℝ≥0` such that `LipschitzWith K f. -/
@[fun_prop]
structure Lipschitz [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : Prop where
  isLipschitz : ∃ K, LipschitzWith K f

namespace Lipschitz

@[fun_prop]
lemma dist_right [PseudoMetricSpace α] (x : α) : Lipschitz (dist x ·) :=
  ⟨1, LipschitzWith.dist_right x⟩

@[fun_prop]
lemma dist_left [PseudoMetricSpace α] (y : α) : Lipschitz (dist · y) :=
  ⟨1, LipschitzWith.dist_left y⟩

variable [PseudoEMetricSpace α]

lemma lipschitz_neg_iff [SeminormedAddCommGroup β] {f : α → β} : Lipschitz f ↔ Lipschitz (-f) := by
  constructor
  · intro hf
    exact ⟨hf.isLipschitz.choose, lipschitzWith_neg_iff.mpr hf.isLipschitz.choose_spec⟩
  intro hf
  exact ⟨hf.isLipschitz.choose, lipschitzWith_neg_iff.mp hf.isLipschitz.choose_spec⟩

variable {f g : α → β}

@[to_additive, fun_prop]
lemma mul [SeminormedCommGroup β] (hf : Lipschitz f) (hg : Lipschitz g) : Lipschitz (f * g) :=
  ⟨hf.isLipschitz.choose + hg.isLipschitz.choose,
    hf.isLipschitz.choose_spec.mul hg.isLipschitz.choose_spec⟩

@[fun_prop]
lemma sub [SeminormedAddCommGroup β] (hf : Lipschitz f) (hg : Lipschitz g) : Lipschitz (f - g) := by
  rw [sub_eq_add_neg f g]
  exact add hf (lipschitz_neg_iff.mp hg)

variable [PseudoEMetricSpace β]

lemma continuous (hf : Lipschitz f) : Continuous f :=
  hf.isLipschitz.choose_spec.continuous

@[fun_prop]
lemma mul_const {f : α → ℝ} (hf : Lipschitz f) {b : ℝ} : Lipschitz (fun a => f a * b) := by
  have f_lipschitz := hf.isLipschitz.choose_spec
  set K := hf.isLipschitz.choose
  let nnb : ℝ≥0 := ⟨|b|, abs_nonneg b⟩
  use K * nnb
  intro x y
  specialize f_lipschitz x y
  simp only [ENNReal.coe_mul]
  rw [show edist (f x * b) (f y * b) = ‖f x * b - f y * b‖₊ by rfl]
  have factorize : f x * b - f y * b = b * (f x - f y) := by ring
  rw [factorize, nnnorm_mul b (f x - f y)]
  have comm : ENNReal.ofNNReal K * .ofNNReal nnb * edist x y =
    .ofNNReal nnb * (.ofNNReal K * edist x y) := by ring
  rw [comm]
  exact mul_le_mul_left' f_lipschitz nnb

@[fun_prop]
lemma const_mul {f : α → ℝ} (hf : Lipschitz f) {b : ℝ} : Lipschitz (fun a => b * f a) := by
  have f_lipschitz := hf.isLipschitz.choose_spec
  set K := hf.isLipschitz.choose
  let nnb : ℝ≥0 := ⟨|b|, abs_nonneg b⟩
  use K * nnb
  intro x y
  specialize f_lipschitz x y
  simp only [ENNReal.coe_mul]
  rw [show edist (b * f x) (b * f y) = ‖b * f x - b * f y‖₊ by rfl]
  have factorize : b * f x - b * f y = b * (f x - f y) := by ring
  rw [factorize, nnnorm_mul b (f x - f y)]
  have comm : ENNReal.ofNNReal K * .ofNNReal nnb * edist x y =
    .ofNNReal nnb * (.ofNNReal K * edist x y) := by ring
  rw [comm]
  exact mul_le_mul_left' f_lipschitz nnb

@[fun_prop]
lemma div_const {f : α → ℝ} (hf : Lipschitz f) {b : ℝ} :
    Lipschitz (fun a => f a / b) := mul_const hf

end Lipschitz

variable [PseudoEMetricSpace β]

@[fun_prop]
lemma lipschitz_const [PseudoEMetricSpace α] {b : β} :
    Lipschitz (fun _ : α => b) := ⟨0, LipschitzWith.const b⟩

variable [NormedAddCommGroup α] [NormedSpace ℝ α]
open Metric Set unitInterval

lemma LipschitzWith.if {f g : α → ℝ} {c : α} {ε : ℝ} {Kf Kg : ℝ≥0}
    [∀ a, Decidable (a ∈ ball c ε)] (hp : ∀ a ∈ sphere c ε, g a = 0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) (fun a => if a ∈ ball c ε then f a + g a else f a) := by

  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let p := fun a => a ∈ ball c ε

  by_cases hxy : ¬ p x ∧ ¬ p y
  · rw [if_neg hxy.1, if_neg hxy.2]
    rw [lipschitzWith_iff_dist_le_mul] at hf
    specialize hf x y
    suffices Kf * dist x y ≤ (Kf + Kg) * dist x y from le_trans hf this
    have Kf_le_add : (Kf : ℝ) ≤ Kf + Kg := by
      show Kf ≤ Kf + Kg
      exact le_self_add
    exact mul_le_mul_of_nonneg Kf_le_add (le_refl _) zero_le_coe dist_nonneg

  · by_cases hxy' : p x ∧ p y
    · rw [if_pos hxy'.1, if_pos hxy'.2]
      exact lipschitzWith_iff_dist_le_mul.mp (hf.add hg) x y
    · push_neg at hxy; push_neg at hxy'

      let φ := fun a => if a ∈ ball c ε then f a + g a else f a
      suffices ∀ a b, ¬ p a ∧ p b → dist (φ a) (φ b) ≤ (Kf + Kg) * dist a b by
        by_cases hx : ¬ p x
        · exact this x y ⟨hx, hxy hx⟩
        · push_neg at hx
          specialize this y x ⟨hxy' hx, hx⟩
          rwa [dist_comm, dist_comm x y]
      intro a b hab
      simp only [φ]
      rw [if_neg hab.1, if_pos hab.2]
      show |f a - (f b + g b)| ≤ (Kf + Kg) * dist a b
      rw [abs_sub_comm]
      suffices h : ∃ e, e ∈ Metric.sphere c ε ∧ dist e b ≤ dist a b by
        let e := h.choose
        have : f b + g b - f a = f b - f a + g b := by ring
        rw [this]
        clear this
        calc _ ≤ |f b - f a| + |g b| := abs_add_le _ _
        _ ≤ Kf * dist b a + |g b| := by
          rw [lipschitzWith_iff_dist_le_mul] at hf
          exact add_le_add_right (hf b a) _
        _ = Kf * dist a b + |g b| := by rw [dist_comm]
        _ = Kf * dist a b + |g b - g e| := by
          rw [hp h.choose h.choose_spec.1]
          simp only [sub_zero]
        _ ≤ Kf * dist a b + Kg * dist b e := by
          rw [lipschitzWith_iff_dist_le_mul] at hg
          exact add_le_add_left (hg b e) (Kf * dist a b)
        _ ≤ Kf * dist a b + Kg * dist a b := by
          have : Kg * dist b e ≤ Kg * dist a b := by
            rw [dist_comm]
            exact mul_le_mul_of_nonneg
              (le_refl _) h.choose_spec.2 (NNReal.zero_le_coe) (dist_nonneg)
          exact (add_le_add_iff_left _).mpr this
        _ = (Kf + Kg) * dist a b := by ring

      suffices ∃ e ∈ segment ℝ b a, e ∈ Metric.sphere c ε by
        obtain ⟨e, e_mem⟩ := this
        refine ⟨e, e_mem.2, ?_⟩
        rw [NormedAddGroup.dist_eq e b, NormedAddGroup.dist_eq a b]
        exact norm_sub_le_of_mem_segment e_mem.1

      let combo := fun t : I => (1 - t.1) • b + t.1 • a
      have int := intermediate_value_univ (f := (dist · c) ∘ combo) 0 1 (by fun_prop)
      simp only [Function.comp_apply, Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero,
        Icc.coe_one, sub_self, zero_add, combo] at int
      have ε_mem_icc : ε ∈ Icc (dist b c) (dist a c) := by
        suffices h : Icc ε ε ⊆ Icc (dist b c) (dist a c) from h ⟨le_refl _, le_refl _⟩
        refine Icc_subset_Icc (le_of_lt hab.2) ?_
        simp only [mem_ball, gt_iff_lt, not_lt, p] at hab
        exact hab.1
      obtain ⟨t, ht⟩ := int ε_mem_icc
      refine ⟨combo t, ?_, ht⟩
      exact ⟨1 - t, t, sub_nonneg_of_le t.2.2, t.2.1, (by ring), rfl⟩

lemma Lipschitz.if {f g : α → ℝ} {c : α} {ε : ℝ} [∀ a, Decidable (a ∈ ball c ε)]
    (hp : ∀ a ∈ sphere c ε, g a = 0) (hf : Lipschitz f) (hg : Lipschitz g) :
    Lipschitz (fun a => if a ∈ ball c ε then f a + g a else f a) :=
  ⟨hf.isLipschitz.choose + hg.isLipschitz.choose,
   hf.isLipschitz.choose_spec.if hp hg.isLipschitz.choose_spec⟩
