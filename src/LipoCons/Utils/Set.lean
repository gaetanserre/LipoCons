/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Set

/-- For a pairwise disjoint family of sets, an element belongs to their union if and only if
it belongs to exactly one of the sets in the family. -/
lemma mem_iUnion_disjoint {α : Type*} {f : ℕ → Set α}
    (h : Pairwise (Function.onFun Disjoint f)) (x : α) : (∃! i, x ∈ f i) ↔ (x ∈ ⋃ i, f i) := by
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

/-- For a pairwise disjoint family of sets, the indicator function of their union equals the
infinite sum of the individual indicator functions. -/
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
    rw [← mem_iUnion_disjoint h] at hx
    obtain ⟨i, fi, hi⟩ := hx
    suffices ∑' y, (f y).indicator g x = (f i).indicator g x by
      rw [this, indicator_of_mem fi]
    refine tsum_eq_single i ?_
    intro y hy
    by_contra h_contra
    push_neg at h_contra
    have : x ∈ f y := mem_of_indicator_ne_zero h_contra
    exact hy (hi y this)

/-- The set of pairs where the indicator function of `s₁` applied to `f e.2 e.1` belongs to `s₂`
can only take one of four forms: empty, universal, equal to `{e | f e.2 e.1 ∈ s₁}`,
or its complement. -/
lemma indicator_one_mem {α β ι γ : Type*} [Zero ι] [One ι] (f : α → γ → β) (s₁ : Set β)
    (s₂ : Set ι) :
    ({e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = ∅) ∨
    ({e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = univ) ∨
    ({e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = {e | (f e.2 e.1) ∈ s₁}) ∨
    ({e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = {e | (f e.2 e.1) ∈ s₁}ᶜ) := by
  by_cases hs₂ : 0 ∉ s₂ ∧ 1 ∉ s₂
  · suffices {e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = ∅ by
      rw [this]
      exact Or.inl rfl
    ext e
    constructor
    swap
    · intro _
      contradiction
    · intro (he : s₁.indicator 1 (f e.2 e.1) ∈ s₂)
      by_cases e_mem : f e.2 e.1 ∈ s₁
      · rw [indicator_of_mem e_mem] at he
        exact hs₂.2 he
      · rw [indicator_of_notMem e_mem] at he
        exact hs₂.1 he
  by_cases hs₂' : 0 ∈ s₂ ∧ 1 ∈ s₂
  · suffices {e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = univ by
      rw [this]
      exact Or.inr <| Or.inl rfl
    ext e
    constructor
    · intro _
      trivial
    · intro _
      show s₁.indicator 1 (f e.2 e.1) ∈ s₂
      by_cases e_mem : f e.2 e.1 ∈ s₁
      · rw [indicator_of_mem e_mem]
        exact hs₂'.2
      · rw [indicator_of_notMem e_mem]
        exact hs₂'.1
  push_neg at hs₂
  push_neg at hs₂'
  by_cases hs₂'' : 1 ∈ s₂
  · suffices {e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = {e | f e.2 e.1 ∈ s₁} by
      rw [this]
      exact Or.inr <| Or.inr <| Or.inl rfl
    ext e
    constructor
    · simp only [mem_setOf_eq]
      intro he
      by_contra h
      rw [indicator_of_notMem h] at he
      exact hs₂' he hs₂''
    · intro (he : f e.2 e.1 ∈ s₁)
      show s₁.indicator 1 (f e.2 e.1) ∈ s₂
      rw [indicator_of_mem he]
      exact hs₂''

  · have hs₂''' : 0 ∈ s₂ := by
      by_contra h
      exact hs₂'' (hs₂ h)
    suffices {e : γ × α | s₁.indicator 1 (f e.2 e.1) ∈ s₂} = {e | f e.2 e.1 ∈ s₁}ᶜ by
      rw [this]
      exact Or.inr <| Or.inr <| Or.inr rfl
    ext e
    constructor
    · simp only [mem_compl_iff, mem_setOf_eq]
      intro he
      by_contra h
      rw [indicator_of_mem h] at he
      exact hs₂'' he
    · simp only [mem_compl_iff, mem_setOf_eq]
      intro he
      rw [indicator_of_notMem he]
      exact hs₂'''

end Set
