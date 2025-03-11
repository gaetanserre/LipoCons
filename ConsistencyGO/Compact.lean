/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set

variable {α : Type*} [TopologicalSpace α] {Ω : Set α} [Nonempty Ω] [i : CompactSpace Ω]

omit [Nonempty Ω] in
lemma space_to_set : IsCompact Ω := isCompact_iff_compactSpace.mpr i

lemma compact_exists_max [LinearOrder α] [ClosedIciTopology α] :
    ∃ ω ∈ Ω, ∀ x ∈ Ω, x ≤ ω := space_to_set.exists_isGreatest (Set.Nonempty.of_subtype)

lemma compact_exists_min [LinearOrder α] [ClosedIicTopology α] :
    ∃ ω ∈ Ω, ∀ x ∈ Ω, ω ≤ x := space_to_set.exists_isLeast (Set.Nonempty.of_subtype)

noncomputable def compact_max [LinearOrder α] [ClosedIciTopology α] : Ω :=
  ⟨(compact_exists_max (Ω := Ω)).choose, (compact_exists_max (Ω := Ω)).choose_spec.1⟩

lemma compact_max_apply [LinearOrder α] [ClosedIciTopology α] :
    ∀ x ∈ Ω, x ≤ compact_max (Ω := Ω) := (compact_exists_max (Ω := Ω)).choose_spec.2

lemma compact_exists_argmax {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {f : Ω → β} (hf : Continuous f) : ∃ x, ∀ y, f y ≤ f x := by
  have : CompactSpace (f '' univ) :=
    isCompact_iff_compactSpace.mp (CompactSpace.isCompact_univ.image hf)
  obtain ⟨fx, ⟨x, _, hx⟩, hfx⟩ := compact_exists_max (Ω := (f '' univ))
  use x
  intro y
  rw [←hx] at hfx
  exact hfx (f y) (mem_image_of_mem f (trivial))

noncomputable def compact_argmax {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {f : Ω → β} (hf : Continuous f) := (compact_exists_argmax hf).choose

lemma compact_argmax_apply {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIciTopology β] {f : Ω → β} (hf : Continuous f) : ∀ y, f y ≤ f (compact_argmax hf) :=
  (compact_exists_argmax hf).choose_spec

lemma compact_exists_argmin {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIicTopology β] {f : Ω → β} (hf : Continuous f) : ∃ x, ∀ y, f x ≤ f y := by
  have : CompactSpace (f '' univ) :=
    isCompact_iff_compactSpace.mp (CompactSpace.isCompact_univ.image hf)
  obtain ⟨fx, ⟨x, _, hx⟩, hfx⟩ := compact_exists_min (Ω := (f '' univ))
  use x
  intro y
  rw [←hx] at hfx
  exact hfx (f y) (mem_image_of_mem f (trivial))

noncomputable def compact_argmin {β : Type*} [TopologicalSpace β] [LinearOrder β]
    [ClosedIicTopology β] {f : Ω → β} (hf : Continuous f) :=
  (compact_exists_argmin hf).choose
