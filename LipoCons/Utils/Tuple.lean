/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.Fintype
import Mathlib.Data.Fintype.Basic

variable {α : Type*}

namespace Tuple

def toTuple (n : ℕ) (u : ℕ → α) : Fin n → α := fun i => u i.val

variable {n : ℕ}

noncomputable def min [LinearOrder α] [Nonempty α] (f : Fin n → α) := Fintype.min_image f

lemma le_min [LinearOrder α] [Nonempty α] (f : Fin n → α) (h : 0 < n) : ∀ j, min f ≤ f j := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  exact Fintype.le_min_image f

noncomputable def max [LinearOrder α] [Nonempty α] (f : Fin n → α) := Fintype.max_image f

lemma le_max [LinearOrder α] [Nonempty α] (f : Fin n → α) (h : 0 < n) : ∀ j, f j ≤ max f := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  exact Fintype.le_max_image f

variable {β : Type*} [LinearOrder β] [Nonempty β] (f : α → β)

lemma tuple_argmin {n : ℕ} (hn : 0 < n) (u : Fin n → α) : ∃ i, f (u i) = min (f ∘ u) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold min Fintype.min_image
  split
  swap
  · contradiction
  unfold Fintype.min_image'
  have univ_ne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr this
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

lemma tuple_argmax {n : ℕ} (hn : 0 < n) (u : Fin n → α) : ∃ i, f (u i) = max (f ∘ u) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold max Fintype.max_image
  split
  swap
  · contradiction
  unfold Fintype.max_image'
  have univ_ne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr this
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
