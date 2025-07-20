/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Analysis.Normed.Order.Lattice

open Set

variable {α β : Type*} [TopologicalSpace α] [Nonempty α] [CompactSpace α] [TopologicalSpace β]
  [LinearOrder β] {f : α → β}

lemma compact_exists_argmin [ClosedIicTopology β] (hf : Continuous f) : ∃ x, ∀ y, f x ≤ f y := by
  have compact_image : IsCompact (f '' univ) :=
    suffices h : CompactSpace (f '' univ) from isCompact_iff_compactSpace.mpr h
    isCompact_iff_compactSpace.mp (CompactSpace.isCompact_univ.image hf)
  have ne_image : (f '' univ).Nonempty :=
    ⟨f (Classical.arbitrary α), mem_image_of_mem f trivial⟩
  obtain ⟨x, ⟨y, _, hy⟩, hx⟩ := compact_image.exists_isLeast ne_image
  use y
  intro y'
  rw [hy]
  exact hx (mem_image_of_mem f (trivial))

noncomputable def compact_argmin [ClosedIicTopology β] (hf : Continuous f) :=
  (compact_exists_argmin hf).choose

lemma compact_argmin_apply [ClosedIicTopology β] (hf : Continuous f) :
    ∀ y, f (compact_argmin hf) ≤ f y := (compact_exists_argmin hf).choose_spec

lemma compact_exists_argmax [ClosedIciTopology β] (hf : Continuous f) : ∃ x, ∀ y, f y ≤ f x := by
  have compact_image : IsCompact (f '' univ) :=
    suffices h : CompactSpace (f '' univ) from isCompact_iff_compactSpace.mpr h
    isCompact_iff_compactSpace.mp (CompactSpace.isCompact_univ.image hf)
  have ne_image : (f '' univ).Nonempty :=
    ⟨f (Classical.arbitrary α), mem_image_of_mem f trivial⟩
  obtain ⟨x, ⟨y, _, hy⟩, hx⟩ := compact_image.exists_isGreatest ne_image
  use y
  intro y'
  rw [hy]
  exact hx (mem_image_of_mem f (trivial))

noncomputable def compact_argmax [ClosedIciTopology β] (hf : Continuous f) :=
  (compact_exists_argmax hf).choose

lemma compact_argmax_apply [ClosedIciTopology β] (hf : Continuous f) :
    ∀ y, f y ≤ f (compact_argmax hf) := (compact_exists_argmax hf).choose_spec

lemma compact_argmin_le_argmax [ClosedIciTopology β] [ClosedIicTopology β] (hf : Continuous f) :
    f (compact_argmin hf) ≤ f (compact_argmax hf) :=
  compact_argmin_apply hf (compact_argmax hf)

lemma compact_argmax_sub_argmin_pos [ClosedIciTopology β] [ClosedIicTopology β] [AddGroup β]
    [AddRightMono β] (hf : Continuous f) : 0 ≤ f (compact_argmax hf) - f (compact_argmin hf) :=
  sub_nonneg_of_le (compact_argmin_le_argmax hf)

lemma dist_max_compact {f : α → ℝ} (hf : Continuous f) (a : α) :
    dist (f a) (f (compact_argmax hf)) = f (compact_argmax hf) - (f a) := by
  set f' := f (compact_argmax hf)
  rw [show dist (f a) f' = |f a - f'| by rfl, abs_sub_comm]
  exact abs_of_nonneg (sub_nonneg_of_le <| compact_argmax_apply hf a)
