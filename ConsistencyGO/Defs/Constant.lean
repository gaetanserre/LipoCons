/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Utils.Compact

def Constant {α β : Type*} (f : α → β) := ∃ c, ∀ x, f x = c

def ConstantOn {α β : Type*} (A : Set α) (f : α → β) := ∃ c, ∀ x ∈ A, f x = c

namespace Constant

open Set

lemma constant_iff {α β : Type*} [i : Nonempty α] (f : α → β) : Constant f ↔ ∀ x y, f x = f y := by
  constructor
  · rintro ⟨c, hc⟩ x y
    rw [hc x, hc y]
  intro h
  use f i.some
  intro x
  exact h x i.some

lemma constantOn_iff {α β : Type*} {A : Set α} (hA : A.Nonempty) (f : α → β) :
    ConstantOn A f ↔ ∀ ⦃x y⦄, x ∈ A → y ∈ A → f x = f y := by
  constructor
  · rintro ⟨c, hc⟩ x y x_in_A y_in_A
    rw [hc x x_in_A, hc y y_in_A]
  intro h
  use f hA.some
  intro x x_in_A
  exact h x_in_A hA.some_mem

lemma constantOn_univ_iff_constant {α β : Type*} {f : α → β} :
    Constant f ↔ ConstantOn univ f := by
  constructor
  · rintro ⟨c, hc⟩
    use c
    intro a _
    exact hc a
  rintro ⟨c, hc⟩
  use c
  intro a
  exact hc a trivial

lemma not_constant_on_imp_not_constant {α β : Type*} (A : Set α) (f : α → β) :
    ¬ ConstantOn A f → ¬ Constant f := by
  intro hf
  unfold ConstantOn Constant at *
  push_neg at hf ⊢
  intro c
  obtain ⟨x, _, hx⟩ := hf c
  use x

/- lemma not_constant_set_or_compl_imp_not_constant {α β : Type*} (A : Set α) (f : α → β) :
    ¬ ConstantOn A f ∨ ¬ ConstantOn Aᶜ f → ¬ Constant f := by
  intro hf
  cases hf with
  | inl hf =>
    exact (not_constant_on_imp_not_constant A f) hf
  | inr hf =>
    exact (not_constant_on_imp_not_constant Aᶜ f) hf -/

variable {α β : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
[TopologicalSpace β] [LinearOrderedCommRing β] [ClosedIciTopology β] [ClosedIicTopology β]

lemma not_constant_continuous_iff_ne_min_max {f : α → β} (hf : Continuous f) :
    ¬ Constant f ↔ f (compact_argmax hf) ≠ f (compact_argmin hf) := by
  constructor
  · intro h
    unfold Constant at h
    push_neg at h
    by_contra h_contra
    obtain ⟨y, hy⟩ := h (f (compact_argmax hf))
    have hy' : f y = f (compact_argmax hf) := by
      suffices f (compact_argmax hf) ≤ f y ∧ f y ≤ f (compact_argmax hf) by linarith
      refine ⟨?_, compact_argmax_apply hf y⟩
      rw [h_contra]
      exact compact_argmin_apply hf y
    contradiction
  intro h
  by_contra h_contra
  obtain ⟨y, hy⟩ := h_contra
  rw [hy <| compact_argmax hf] at h
  rw [hy <| compact_argmin hf] at h
  contradiction

end Constant
