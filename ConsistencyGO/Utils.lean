/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Convergence
import ConsistencyGO.Tuple
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Order.CompletePartialOrder

open MeasureTheory Tuple

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

open Filter Topology

lemma equiv_convergence {β : Type*} [Dist β] (fn gn : (n : ℕ) → (Fin n → α) → β)
    (h_measurable : ∀ ε n, MeasurableSet {u | dist (fn n u) (gn n u) > ε }) :
    ν.tendsto (toTupleFun fn) (toTupleFun gn)
    ↔ ∀ ε > 0, Tendsto (fun n => μ ν n {u | dist (fn n u) (gn n u) > ε}) atTop (𝓝 0) := by
  unfold MeasureTheory.Measure.tendsto
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
