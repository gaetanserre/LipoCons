/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib

namespace Set

lemma mem_iUnion_disjoint {α : Type*} {f : ℕ → Set α}
    (h : Pairwise (Function.onFun Disjoint f)) (x : α) :
    (∃! i, x ∈ f i) ↔ (x ∈ ⋃ i, f i) := by
  constructor
  · rintro ⟨i, fi, _⟩
    rw [mem_iUnion]
    exact ⟨i, fi⟩
  intro hx
  rw [mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, hi, ?_⟩
  intro y hy
  by_contra y_neq_i
  have : x ∈ (f y) ∩ (f i) := ⟨hy, hi⟩
  rw [Disjoint.inter_eq (h y_neq_i)] at this
  contradiction

lemma sum_indicator_iUnion {α β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    {f : ℕ → Set α} (h : Pairwise (Function.onFun Disjoint f))
    {g : α → β} : ∀ x, ((⋃ i, f i).indicator g x) = ∑' i, (f i).indicator g x := by
  intro x
  by_cases hx : x ∉ ⋃ i, f i
  · rw [indicator_of_notMem hx]
    have : ∀ i, x ∉ f i := by
      rw [mem_iUnion] at hx
      push_neg at hx
      exact hx
    have : ∀ i, (f i).indicator g x = 0 := by
      intro i
      rw [indicator_of_notMem <| this i]
    simp_rw [this]
    simp only [tsum_zero]
  · push_neg at hx
    rw [indicator_of_mem hx]
    rw [←mem_iUnion_disjoint h] at hx
    obtain ⟨i, fi, hi⟩ := hx
    suffices ∑' y, (f y).indicator g x = (f i).indicator g x by
      rw [this, indicator_of_mem fi]
    refine tsum_eq_single i ?_
    intro y hy
    by_contra h_contra
    push_neg at h_contra
    have : x ∈ f y := mem_of_indicator_ne_zero h_contra
    exact hy (hi y this)

end Set
