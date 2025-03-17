/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Compact
import ConsistencyGO.Convergence
import ConsistencyGO.Tuple
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.CompletePartialOrder

open MeasureTheory Tuple Filter Topology

namespace AlgorithmMeasure

variable {α : Type*} [MeasurableSpace α] (ν : Measure (ℕ → α))

noncomputable def μ (n : ℕ) : Measure (Fin n → α) := by
  refine Measure.ofMeasurable ?_ ?_ ?_
  · intro s _
    exact ν {u : ℕ → α | toTuple n u ∈ s}
  · exact OuterMeasureClass.measure_empty ν
  intro f h_m h_d
  let g := fun i => {u : ℕ → α | toTuple n u ∈ f i}

  have measurable : ∀ (i : ℕ), MeasurableSet (g i) := by
    intro i
    have h_measurable : Measurable (toTuple n : (ℕ → α) → Fin n → α) :=
      measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)
    exact h_measurable (h_m i)

  have disjoint : Pairwise (Function.onFun Disjoint g) := by
    intro i j h
    suffices h : g i ∩ g j = ∅ from Set.disjoint_iff_inter_eq_empty.mpr h
    have h_d : f i ∩ f j = ∅ := Set.disjoint_iff_inter_eq_empty.mp (h_d h)
    ext u
    constructor
    · intro (h : toTuple n u ∈ f i ∩ f j)
      rw [h_d] at h
      contradiction
    intro h
    contradiction

  have iUnion : ν (⋃ i, g i) = ∑' (i : ℕ), ν (g i) := measure_iUnion disjoint measurable
  have unfold_union : ⋃ i, g i = {u : ℕ → α | toTuple n u ∈ ⋃ i, f i} := by
    ext u
    constructor
    · intro h
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion_of_mem j hj
    intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  rw [unfold_union] at iUnion
  exact iUnion

lemma equiv_convergence {β : Type*} [Dist β] (fn gn : (n : ℕ) → (Fin n → α) → β)
    (h_measurable : ∀ ε n, MeasurableSet {u | dist (fn n u) (gn n u) > ε }) :
    ν.tendsto (toTupleFun fn) (toTupleFun gn)
    ↔ ∀ ε > 0, Tendsto (fun n => μ ν n {u | dist (fn n u) (gn n u) > ε}) atTop (𝓝 0) := by
  unfold Measure.tendsto
  suffices h : ∀ ε > 0,
      (fun n ↦
      ν {x | dist (toTupleFun fn n x) (toTupleFun gn n x) > ε})
      = (fun n ↦ (μ ν n) {u | dist (fn n u) (gn n u) > ε}) by
    constructor
    · intro h' ε hε
      rw [←h ε hε]
      exact h' ε hε
    intro h' ε hε
    rw [h ε hε]
    exact h' ε hε

  intro ε hε
  ext n
  have m_apply : (μ ν n) {u | dist (fn n u) (gn n u) > ε} =
      ν {u : ℕ → α | toTuple n u ∈ {u | dist (fn n u) (gn n u) > ε}} :=
    Measure.ofMeasurable_apply {u | dist (fn n u) (gn n u) > ε} (h_measurable ε n)
  rw [m_apply]
  rfl

lemma μ_mono : ∀ n m A B,
    MeasurableSet A → MeasurableSet B → {u | toTuple n u ∈ A} ⊆ {u | toTuple m u ∈ B} →
    μ ν n A ≤ μ ν m B := by
  intro n m A B hA hB hu
  have : μ ν n A = ν {u : ℕ → α | toTuple n u ∈ A} := Measure.ofMeasurable_apply A hA
  rw [this]
  have : μ ν m B = ν {u : ℕ → α | toTuple m u ∈ B} := Measure.ofMeasurable_apply B hB
  rw [this]
  exact OuterMeasureClass.measure_mono ν hu

lemma μ_mono_iff_eq_subtuple [inst : Nonempty α]
    (μ : (n : ℕ) → Measure (Fin n → α)) (hμ : ∀ n, IsFiniteMeasure (μ n)) :
    (∀ ⦃n m A B⦄, {u | toTuple n u ∈ A} ⊆ {u | toTuple m u ∈ B} → μ n A ≤ μ m B)
    ↔
    ∀ ⦃n m A⦄, (h : n ≤ m) → μ n A = μ m {u | subTuple h u ∈ A} := by
  constructor
  · intro h n m A h_ineq
    let A' := {u | toTuple m u ∈ {(u : Fin m → α) | subTuple h_ineq u ∈ A}}
    have A_ss_A' : {u | toTuple n u ∈ A} ⊆ A' := by
      intro u hu
      simp_all only [Set.setOf_subset_setOf, Set.mem_setOf_eq]
      exact hu
    have ineq1 := h A_ss_A'
    have A'_ss_A: A' ⊆ {u | toTuple n u ∈ A} := by
      intro u hu
      simp_all only [Set.setOf_subset_setOf, Set.mem_setOf_eq, implies_true, A']
      exact hu
    have ineq2 := h A'_ss_A
    have μ_n_finite : (μ n) A ≠ ⊤ := measure_ne_top (μ n) A
    have μ_m_finite : (μ m) {u | subTuple h_ineq u ∈ A} ≠ ⊤ :=
      measure_ne_top (μ m) {u | subTuple h_ineq u ∈ A}
    have ineq1 := (ENNReal.toReal_le_toReal μ_n_finite μ_m_finite).mpr ineq1
    have ineq2 := (ENNReal.toReal_le_toReal μ_m_finite μ_n_finite).mpr ineq2
    suffices ((μ n) A).toReal = ((μ m) {u | subTuple h_ineq u ∈ A}).toReal from
      (ENNReal.toReal_eq_toReal_iff' μ_n_finite μ_m_finite).mp this
    linarith
  intro h n m A B A_ss_B
  by_cases h_ineq : n ≤ m
  · rw [h h_ineq]
    suffices {u | subTuple h_ineq u ∈ A} ⊆ B from OuterMeasureClass.measure_mono (μ m) this
    intro u hu
    let u' := fun (i : ℕ) => if h : i < m then u ⟨i, h⟩ else inst.some
    have toTuple_in_B : toTuple m u' ∈ B := by
      suffices h : toTuple n u' = subTuple h_ineq u by
        have toTuple_in_A : toTuple n u' ∈ A := Set.mem_of_eq_of_mem h hu
        exact A_ss_B toTuple_in_A
      ext i
      unfold toTuple subTuple u'
      split
      · rfl
      next h_if =>
        push_neg at h_if
        have : n ≤ i.val := Nat.le_trans h_ineq h_if
        have := i.2
        linarith
    suffices h : toTuple m u' = u by rwa [h] at toTuple_in_B
    ext i
    unfold toTuple u'
    split
    · rfl
    next h_if =>
        push_neg at h_if
        have : n ≤ i.val := Nat.le_trans h_ineq h_if
        have := i.2
        linarith

  push_neg at h_ineq
  have h_ineq : m ≤ n := Nat.le_of_succ_le h_ineq
  rw [h h_ineq]
  suffices A ⊆ {u | subTuple h_ineq u ∈ B} from OuterMeasureClass.measure_mono (μ n) this
  intro u hu
  let u' := fun (i : ℕ) => if h : i < n then u ⟨i, h⟩ else inst.some
  have toTuple_in_B : toTuple m u' ∈ B := by
    suffices h : toTuple n u' = u by
      have toTuple_in_A : toTuple n u' ∈ A := by exact Set.mem_of_eq_of_mem h hu
      exact A_ss_B toTuple_in_A
    ext i
    unfold toTuple u'
    split
    · rfl
    next h_if =>
        push_neg at h_if
        have : m ≤ i.val := Nat.le_trans h_ineq h_if
        have := i.2
        linarith
  suffices h : toTuple m u' = subTuple h_ineq u by rwa [h] at toTuple_in_B
  ext i
  unfold toTuple subTuple u'
  split
  · rfl
  next h_if =>
    push_neg at h_if
    have : m ≤ i.val := Nat.le_trans h_ineq h_if
    have := i.2
    linarith

end AlgorithmMeasure

namespace Tendsto

variable {α β : Type*} [Preorder α] [TopologicalSpace β] [Preorder β] [OrderTopology β]
[AddZeroClass β] [CanonicallyOrderedAdd β]

lemma tendsto_zero_le {f g : α → β} (h : f ≤ g) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  let c := fun (_ : α) => (0 : β)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg (fun x => zero_le (f x)) h

lemma tendsto_zero_le_nat {f g : ℕ → β} (h : ∀ n > 0, f n ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  let c := fun (_ : ℕ) => (0 : β)
  have ev_le_const : ∀ᶠ n in atTop, c n ≤ f n := Eventually.of_forall (fun x => zero_le (f x))
  have ev_le_fg : ∀ᶠ n in atTop, f n ≤ g n := by
    rw [eventually_iff]
    suffices h : {n | n > 0 ∧ f n ≤ g n} ∈ atTop by
      filter_upwards [h] with _ hn using hn.2
    rw [mem_atTop_sets]
    use 1
    intro b hb
    exact ⟨hb, h b hb⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg ev_le_const ev_le_fg

end Tendsto

namespace Abs

lemma abs_lt {a b : ℝ} (h : a ≤ b) : |a - b| = b - a := by
  have le : a - b ≤ 0 := tsub_nonpos.mpr h
  by_cases h' : a - b = 0
  · rw [h']
    rw [neg_inj.mp (neg_eq_of_add_eq_zero_right h')]
    simp only [abs_zero, sub_self]
  rw [abs_of_neg (lt_of_le_of_ne le h')]
  exact neg_sub a b

end Abs

namespace Compact

variable {α : Type*} [TopologicalSpace α] {Ω : Set α} [CompactSpace Ω] [Nonempty Ω]
{f : Ω → ℝ} (hcont : Continuous f)

lemma dist_max_compact (a : Ω) :
    dist (f a) (f (compact_argmax hcont)) = f (compact_argmax hcont) - (f a) := by
  set f' := f (compact_argmax hcont)
  rw [show dist (f a) f' = |f a - f'| by rfl]
  exact Abs.abs_lt (compact_argmax_apply hcont a)

end Compact

namespace Metric

lemma continuous_iff_le {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, dist a b ≤ δ → dist (f a) (f b) ≤ ε := by
  rw [Metric.continuous_iff]
  constructor
  · intro h b ε hε
    obtain ⟨δ, hδ, h⟩ := h b ε hε
    refine ⟨δ/2, half_pos hδ, ?_⟩
    intro a ha
    exact le_of_lt (h a (lt_of_le_of_lt ha (div_two_lt_of_pos hδ)))
  intro h b ε hε
  obtain ⟨δ, hδ, h⟩ := h b (ε/2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  exact lt_of_le_of_lt (h a (le_of_lt ha)) (div_two_lt_of_pos hε)

end Metric
