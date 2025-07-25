/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.Fintype
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

variable {α : Type*}

namespace Tuple

def toTuple (n : ℕ) (u : ℕ → α) : Fin n → α := fun i => u i.val

noncomputable def min [LinearOrder α] [Nonempty α] {n : ℕ} (f : Fin n → α) := Fintype.min_image f

lemma le_min [LinearOrder α] [Nonempty α] {n : ℕ} (f : Fin (n + 1) → α) : ∀ j, min f ≤ f j := by
  haveI : Nonempty (Fin (n + 1)) := instNonemptyOfInhabited
  exact Fintype.le_min_image f

noncomputable def max [LinearOrder α] [Nonempty α] {n : ℕ} (f : Fin n → α) := Fintype.max_image f

lemma le_max [LinearOrder α] [Nonempty α] {n : ℕ} (f : Fin (n + 1) → α) : ∀ j, f j ≤ max f := by
  haveI : Nonempty (Fin (n + 1)) := instNonemptyOfInhabited
  exact Fintype.le_max_image f

variable {β : Type*}

/-- Given `n ≤ m`, this is the restriction of a function `u : Fin (m + 1) → α`
to a function `Fin (n + 1) → α`. -/
abbrev subTuple {n m : ℕ} (hmn : n ≤ m) (u : Fin (m + 1) → α) : Fin (n + 1) → α :=
  u ∘ Fin.castLE (Nat.add_le_add_right hmn 1)

/-- Given `n`, a function `f : α → β` and a function `u : Fin (n + 1) → α`,
this is the pair `(u, f ∘ u)`, where `f ∘ u` is the function
from `Fin (n + 1)` to `β` that applies `f` to the values of `u`. -/
abbrev prod_eval (n : ℕ) (f : α → β) (u : Fin (n + 1) → α) := (u, f ∘ u)

/-- Given a set `s` and two functions `f g : α → β`, such that `f` and `g` are equal on `s`,
the pair `(u, f ∘ u)` is equal to the pair `(u, g ∘ u)` for any `u : Fin (n + 1) → α`
such that `u i ∈ s` for all `i`.-/
lemma prod_eval_eq_restrict (n : ℕ) {f g : α → β} {s : Set α} (hfg : s.restrict f = s.restrict g)
    {u : Fin (n + 1) → α} (hu : ∀ i, u i ∈ s) : prod_eval n f u = prod_eval n g u := by
  ext i
  · rfl
  · specialize hu i
    simp_all only [Set.restrict_eq_restrict_iff]
    have fwd : f (u i) = g (u i) := Set.EqOn.eq_of_mem hfg hu
    exact fwd

/-- For any measurable function `f : α → β`, the function `prod_eval n f` is measurable. -/
lemma measurable_prod_eval [MeasurableSpace α] [MeasurableSpace β] (n : ℕ)
    {f : α → β} (hf : Measurable f) : Measurable (prod_eval n f) := by
  refine Measurable.prodMk measurable_id ?_
  unfold Function.comp
  apply measurable_pi_lambda
  intro a
  apply Measurable.comp'
  · exact hf
  · exact measurable_pi_apply _

/-- Given a function `u : Fin n → α` and an element `a : α`, `append u a` extends
`u` by one element, i.e., it maps `Fin (n + 1)` to `α` by taking the values of `u`
and mapping the last index `n` to `a`. -/
abbrev append {n : ℕ} (u : Fin n → α) (a : α) : Fin (n + 1) → α := Fin.snoc u a

variable [LinearOrder β] [Nonempty β] (f : α → β)

lemma argmin {n : ℕ} (u : Fin (n + 1) → α) : ∃ i, f (u i) = min (f ∘ u) := by
  haveI : Nonempty (Fin (n + 1)) := instNonemptyOfInhabited
  unfold min Fintype.min_image
  split
  swap
  · contradiction
  unfold Fintype.min_image'
  have univ_ne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty_iff.mpr this
  let A := {x | ∃ i, u i = x}
  suffices h : Finset.univ.inf' univ_ne (f ∘ u) ∈ (f '' A) by
    obtain ⟨x, ⟨i, hi⟩, h⟩ := h
    rw [←h, ←hi]
    use i
  have min_mem : ∀ x ∈ (f '' A), ∀ y ∈ (f '' A), x ⊓ y ∈ (f '' A) := by
    intro x hx y hy
    cases min_choice x y with
    | inl inl => rwa [inl]
    | inr inr => rwa [inr]
  apply Finset.inf'_mem (f '' A) min_mem Finset.univ univ_ne (f ∘ u)
  intro i _
  exact ⟨u i, ⟨i, rfl⟩, rfl⟩

lemma argmax {n : ℕ} (u : Fin (n + 1) → α) : ∃ i, f (u i) = max (f ∘ u) := by
  haveI : Nonempty (Fin (n + 1)) := instNonemptyOfInhabited
  unfold max Fintype.max_image
  split
  swap
  · contradiction
  unfold Fintype.max_image'
  have univ_ne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty_iff.mpr this
  let A := {x | ∃ i, u i = x}
  suffices h : Finset.univ.sup' univ_ne (f ∘ u) ∈ (f '' A) by
    obtain ⟨x, ⟨i, hi⟩, h⟩ := h
    rw [←h, ←hi]
    use i
  have max_mem : ∀ x ∈ (f '' A), ∀ y ∈ (f '' A), x ⊔ y ∈ (f '' A) := by
    intro x hx y hy
    cases max_choice x y with
    | inl inl => rwa [inl]
    | inr inr => rwa [inr]
  apply Finset.sup'_mem (f '' A) max_mem Finset.univ univ_ne (f ∘ u)
  intro i _
  exact ⟨u i, ⟨i, rfl⟩, rfl⟩

end Tuple
