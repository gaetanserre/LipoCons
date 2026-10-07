/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

open NNReal MeasureTheory

variable {α β : Type*}

/-- A wrapper around `LipschitzWith` of Mathlib. A function is `Lipschitz` if it exists
a `K : ℝ≥0` such that `LipschitzWith K f`. -/
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

lemma measurable (hf : Lipschitz f) [MeasurableSpace α] [MeasurableSpace β]
    [OpensMeasurableSpace α] [BorelSpace β] : Measurable f :=
  hf.continuous.measurable

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
  exact mul_le_mul_right f_lipschitz nnb

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
  exact mul_le_mul_right f_lipschitz nnb

@[fun_prop]
lemma div_const {f : α → ℝ} (hf : Lipschitz f) {b : ℝ} :
    Lipschitz (fun a => f a / b) := mul_const hf

end Lipschitz

variable [PseudoEMetricSpace β]

@[fun_prop]
lemma lipschitz_const [PseudoEMetricSpace α] {b : β} :
    Lipschitz (fun _ : α => b) := ⟨0, LipschitzWith.const b⟩

/-- Adding `g` to `f` only where `p` holds preserves the Lipschitz property, provided `g` is
nonnegative where `p` holds and nonpositive elsewhere: the resulting function is then
`f + max g 0`. This holds in any (pseudo-e)metric space. -/
lemma LipschitzWith.if [PseudoEMetricSpace α] {f g : α → ℝ} {p : α → Prop} [DecidablePred p]
    {Kf Kg : ℝ≥0} (hpos : ∀ a, p a → 0 ≤ g a) (hneg : ∀ a, ¬ p a → g a ≤ 0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) (fun a => if p a then f a + g a else f a) := by
  have : (fun a => if p a then f a + g a else f a) = fun a => f a + max (g a) 0 := by
    ext a
    by_cases ha : p a
    · rw [ite_eq_left ha, max_eq_left (hpos a ha)]
    · rw [ite_eq_right ha, max_eq_right (hneg a ha), add_zero]
  rw [this]
  exact hf.add (hg.max_const 0)

lemma Lipschitz.if [PseudoEMetricSpace α] {f g : α → ℝ} {p : α → Prop} [DecidablePred p]
    (hpos : ∀ a, p a → 0 ≤ g a) (hneg : ∀ a, ¬ p a → g a ≤ 0)
    (hf : Lipschitz f) (hg : Lipschitz g) :
    Lipschitz (fun a => if p a then f a + g a else f a) :=
  ⟨hf.isLipschitz.choose + hg.isLipschitz.choose,
   hf.isLipschitz.choose_spec.if hpos hneg hg.isLipschitz.choose_spec⟩
