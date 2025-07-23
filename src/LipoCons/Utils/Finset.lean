/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Data.Finset.Max


namespace Finset

variable {α β : Type*} [LinearOrder β] [DecidableEq β] [Nonempty β]

lemma extract_mono {s : Finset α} (hs : s.Nonempty) {p : α → β → Prop} (h : ∀ x ∈ s, ∃ a, p x a)
    (h_mono : ∀ x ∈ s, ∀ a b, a ≤ b → p x a → p x b) {p2 : β → Prop}
    (h2 : ∀ x ∈ s, ∀ a, ∃ b ≥ a, p2 b) : ∃ a, (∀ x ∈ s, p x a) ∧ p2 a := by
  choose! f h_f using h
  let mx := (s.image f).max' (image_nonempty.mpr hs)
  obtain ⟨x, x_mem, hx⟩ : ∃ x ∈ s, f x = mx :=
    suffices mx ∈ (s.image f) by
      rwa [Finset.mem_image] at this
    max'_mem (image f s) (image_nonempty.mpr hs)
  specialize h2 x x_mem mx
  obtain ⟨b, b_le, hb2⟩ := h2
  use b
  refine ⟨?_, hb2⟩
  intro y y_mem
  suffices f y ≤ mx from h_mono y y_mem (f y) b (le_trans this b_le) (h_f y y_mem)
  exact (s.image f).le_max' (f y) (mem_image_of_mem f y_mem)

end Finset
