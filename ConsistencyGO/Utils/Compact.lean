/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Utils.Abs
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set

variable {α : Type*} [TopologicalSpace α] [i1 : Nonempty α] [i2 : CompactSpace α]

omit [Nonempty α] in
lemma space_to_set : IsCompact (univ : Set α) := CompactSpace.isCompact_univ

lemma compact_exists_max [LinearOrder α] [ClosedIciTopology α] :
    ∃ (ω : α), ∀ x, x ≤ ω := by
  obtain ⟨ω, l, hω⟩ := space_to_set.exists_isGreatest (nonempty_iff_univ_nonempty.mp i1)
  use ω
  intro x
  have x_in_univ : x ∈ univ := trivial
  exact hω x_in_univ

lemma compact_exists_min [LinearOrder α] [ClosedIicTopology α] :
    ∃ (ω : α), ∀ x, ω ≤ x := by
  obtain ⟨ω, l, hω⟩ := space_to_set.exists_isLeast (nonempty_iff_univ_nonempty.mp i1)
  use ω
  intro x
  have x_in_univ : x ∈ univ := trivial
  exact hω x_in_univ

noncomputable def compact_max [LinearOrder α] [ClosedIciTopology α] : α :=
  compact_exists_max.choose

lemma compact_max_apply [LinearOrder α] [ClosedIciTopology α] :
    ∀ (x : α), x ≤ compact_max := (compact_exists_max (α := α)).choose_spec

lemma compact_exists_argmax {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {f : α → β} (hf : Continuous f) : ∃ x, ∀ y, f y ≤ f x := by
  have compact_image : IsCompact (f '' univ) :=
    suffices h : CompactSpace (f '' univ) from isCompact_iff_compactSpace.mpr h
    isCompact_iff_compactSpace.mp (CompactSpace.isCompact_univ.image hf)
  have ne_image : (f '' univ).Nonempty := by
    use f i1.some
    exact mem_image_of_mem f trivial
  obtain ⟨x, ⟨y, _, hy⟩, hx⟩ := compact_image.exists_isGreatest ne_image
  use y
  intro y'
  rw [hy]
  exact hx (mem_image_of_mem f (trivial))

noncomputable def compact_argmax {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {f : α → β} (hf : Continuous f) := (compact_exists_argmax hf).choose

lemma compact_argmax_apply {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {f : α → β} (hf : Continuous f) : ∀ y, f y ≤ f (compact_argmax hf) :=
  (compact_exists_argmax hf).choose_spec

lemma compact_exists_argmin {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIicTopology β] {f : α → β} (hf : Continuous f) : ∃ x, ∀ y, f x ≤ f y := by
  have compact_image : IsCompact (f '' univ) :=
    suffices h : CompactSpace (f '' univ) from isCompact_iff_compactSpace.mpr h
    isCompact_iff_compactSpace.mp (CompactSpace.isCompact_univ.image hf)
  have ne_image : (f '' univ).Nonempty := by
    use f i1.some
    exact mem_image_of_mem f trivial
  obtain ⟨x, ⟨y, _, hy⟩, hx⟩ := compact_image.exists_isLeast ne_image
  use y
  intro y'
  rw [hy]
  exact hx (mem_image_of_mem f (trivial))

noncomputable def compact_argmin {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIicTopology β] {f : α → β} (hf : Continuous f) :=
  (compact_exists_argmin hf).choose

lemma compact_argmin_apply {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIicTopology β] {f : α → β} (hf : Continuous f) : ∀ y, f (compact_argmin hf) ≤ f y :=
  (compact_exists_argmin hf).choose_spec

namespace Compact

variable {f : α → ℝ} (hcont : Continuous f)

lemma dist_max_compact (a : α) :
    dist (f a) (f (compact_argmax hcont)) = f (compact_argmax hcont) - (f a) := by
  set f' := f (compact_argmax hcont)
  rw [show dist (f a) f' = |f a - f'| by rfl]
  exact Abs.abs_lt (compact_argmax_apply hcont a)

end Compact
