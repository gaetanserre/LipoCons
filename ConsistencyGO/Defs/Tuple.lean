/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Defs.Fintype
import Mathlib.Data.Fintype.Basic

variable {α : Type*}

namespace Tuple

variable [LinearOrder α] {n : ℕ} [Nonempty α] (f : Fin n → α)

noncomputable def max := Fintype.max_image f

lemma le_max (h : 0 < n) : ∀ j, f j ≤ max f := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  exact Fintype.le_max_image f

noncomputable def min := Fintype.min_image f

lemma le_min (h : 0 < n) : ∀ j, min f ≤ f j := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h
  exact Fintype.le_min_image f

end Tuple

namespace Tuple

def toTuple (n : ℕ) (u : ℕ → α) : Fin n → α := fun i => u i.val

def toTupleFun {β : Type*} (f : (n : ℕ) → (Fin n → α) → β) := fun n u => f n (toTuple n u)

def subTuple {n m : ℕ} (h : n ≤ m) (u : Fin m → α) : Fin n → α :=
  fun (i : Fin n) => u ⟨i.val, Fin.val_lt_of_le i h⟩

end Tuple

namespace Tuple

variable {α β : Type*} [LinearOrder β] [Nonempty β] (f : α → β)

lemma tuple_argmax {n : ℕ} (hn : 0 < n) (u : Fin n → α) : ∃ i, f (u i) = Tuple.max (f ∘ u) := by
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

lemma tuple_argmin {n : ℕ} (hn : 0 < n) (u : Fin n → α) : ∃ i, f (u i) = Tuple.min (f ∘ u) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold Tuple.min Fintype.min_image
  split
  swap
  · contradiction
  unfold Fintype.min_image'
  have univ_ne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr this

  let A := {x | ∃ i, u i = x}

  suffices h : (Finset.univ).inf' univ_ne (f ∘ u) ∈ (f '' A) by
    obtain ⟨x, ⟨i, hi⟩, h⟩ := h
    rw [←h, ←hi]
    use i

  have : ∀ x ∈ (f '' A), ∀ y ∈ (f '' A), x ⊓ y ∈ (f '' A) := by
    intro x hx y hy
    cases min_choice x y with
    | inl inl => rwa [inl]
    | inr inr => rwa [inr]

  apply Finset.inf'_mem (f '' A) this Finset.univ univ_ne (f ∘ u)

  intro i _
  exact ⟨u i, ⟨i, rfl⟩, rfl⟩

end Tuple
