/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib


namespace Finset

variable {α β : Type*} [LinearOrder β] [DecidableEq β] [Nonempty β]

lemma extract_mono {s : Finset α} (hs : s.Nonempty) (p : α → β → Prop) (h : ∀ x ∈ s, ∃ a, p x a)
    (h_mono : ∀ x ∈ s, ∀ a b, a ≤ b → p x a → p x b) : ∃ a, ∀ x ∈ s, p x a := by
  choose! f h_f using h
  let mx := (s.image f).max' (image_nonempty.mpr hs)
  use mx
  intro x x_mem
  suffices f x ≤ mx from h_mono x x_mem (f x) mx this (h_f x x_mem)
  exact (s.image f).le_max' (f x) (mem_image_of_mem f x_mem)

end Finset
