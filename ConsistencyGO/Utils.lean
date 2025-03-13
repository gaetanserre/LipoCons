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

variable {α β : Type*} [LinearOrder β] [Nonempty β] (f : α → β)

lemma arg_tuple_max {n : ℕ} (hn : 0 < n) (u : Fin n → α) : ∃ i, f (u i) = Tuple.max (f ∘ u) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold Tuple.max Fintype.max_image
  split
  swap
  · contradiction
  unfold Fintype.max_image'
  have univ_ne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr this

  let A := {x | ∃ i, u i = x}

  suffices h : (Finset.univ).sup' univ_ne (f ∘ u) ∈ (f '' A) by
    obtain ⟨x, ⟨i, hi⟩, h⟩ := h
    rw [←h, ←hi]
    use i

  have : ∀ x ∈ (f '' A), ∀ y ∈ (f '' A), x ⊔ y ∈ (f '' A) := by
    intro x hx y hy
    cases max_choice x y with
    | inl inl => rwa [inl]
    | inr inr => rwa [inr]

  apply Finset.sup'_mem (f '' A) this Finset.univ univ_ne (f ∘ u)

  intro i _
  exact ⟨u i, ⟨i, rfl⟩, rfl⟩
