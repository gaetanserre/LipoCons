/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Utils.Compact
import Mathlib

open NNReal

variable {α β : Type*}

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

open Set

variable [PseudoMetricSpace α] [ProperSpace α]

lemma Lipschitz.if {f g : α → ℝ} {p : α → Prop} [∀ a, Decidable (p a)]
    (hp : ∀ a ∈ frontier { x | p x }, f a = g a) (hf : Lipschitz f) (hg : Lipschitz g) :
    Lipschitz fun a => if p a then f a else g a := by
  let Kf := hf.isLipschitz.choose
  let Kg := hg.isLipschitz.choose
  have h_cont := hf.continuous.if hp hg.continuous

  use (max Kf Kg)

  have t : (max Kf Kg) = Real.toNNReal (max Kf Kg) := by sorry
  rw [t]

  apply LipschitzWith.of_dist_le'
  intro x y
  by_cases h : p x ∧ p y
  · rw [if_pos h.1, if_pos h.2]
    sorry
    --exact le_mul_of_le_mul_right (hf.isLipschitz.choose_spec x y) (le_max_left _ _)
  · by_cases h' : ¬ p x ∧ ¬ p y
    · rw [if_neg h'.1, if_neg h'.2]
      sorry
      --exact le_mul_of_le_mul_right (hg.isLipschitz.choose_spec x y) (le_max_right _ _)
    push_neg at h; push_neg at h'
    by_cases hx : ¬ p x
    · specialize h' hx
      rw [if_neg hx, if_pos h']
      set h := fun a ↦ if p a then f a else g a
      by_contra h_contra
      push_neg at h_contra

      let r := dist x y
      have compact_ball : IsCompact (Metric.closedBall x r) :=
        isCompact_closedBall x r

      replace h_cont : ContinuousOn h (Metric.closedBall x r) :=
        fun _ _ => Continuous.continuousWithinAt h_cont
      replace h_cont : UniformContinuousOn h (Metric.closedBall x r) :=
        compact_ball.uniformContinuousOn_of_continuous h_cont
      rw [Metric.uniformContinuousOn_iff] at h_cont



      /- let r := dist x y
      have compact_ball : IsCompact (Metric.closedBall x r) :=
        isCompact_closedBall x r

      have nonempty_ball : (Metric.closedBall x r).Nonempty :=
        Metric.nonempty_closedBall.mpr dist_nonneg



      have compact_image : IsCompact (h '' (Metric.closedBall x r)) := compact_ball.image h_cont

      obtain ⟨hz, ⟨z, z_mem, h_z⟩, h_hz⟩ := compact_image.exists_isGreatest (nonempty_ball.image h)

      by_cases pz : p z
      · have : ∀ x ∈ (Metric.closedBall x r), dist (f x) (f y) ≤ dist (f z) (f )
        sorry
      · sorry -/


      /- replace : ContinuousOn (fun a ↦ if p a then f a else g a) (Metric.closedBall x r) :=
        fun _ _ => Continuous.continuousWithinAt h_cont
      replace : UniformContinuousOn (fun a ↦ if p a then f a else g a) (Metric.closedBall x r) := by
        exact compact_ball.uniformContinuousOn_of_continuous this
      rw [Metric.uniformContinuousOn_iff] at this -/



      sorry
    · sorry

example (f : ℝ → ℝ) (s : Set ℝ) (hs : IsCompact s) (hf : ContinuousOn f s) :
    UniformContinuousOn f s := by
  exact IsCompact.uniformContinuousOn_of_continuous hs hf

example (a : ℝ) (ε : ℝ) : (Metric.ball a ε).Nonempty := by
  have : 0 < ε := by sorry
  exact Metric.nonempty_ball.mpr this
