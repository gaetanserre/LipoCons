/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Data.Finset.Max

namespace Finset

variable {α β : Type*} [LinearOrder β] [DecidableEq β] [Nonempty β]

/-- Given a finite set `s` and monotonic predicates, there exists a uniform bound that satisfies
all predicates simultaneously. If for each element `x ∈ s` there exists some `a` satisfying
`p₁ x a`, and `p₁ x` is monotonic, and there's always a larger element satisfying `p₂`,
then there exists a single `a` satisfying both `p₁ x a` for all `x ∈ s` and `p₂ a`. -/
lemma extract_mono {s : Finset α} (hs : s.Nonempty) {p₁ : α → β → Prop} (h₁ : ∀ x ∈ s, ∃ a, p₁ x a)
    (h_mono : ∀ x ∈ s, ∀ a b, a ≤ b → p₁ x a → p₁ x b) {p₂ : β → Prop}
    (h₂ :∀ a, ∃ b ≥ a, p₂ b) : ∃ a, (∀ x ∈ s, p₁ x a) ∧ p₂ a := by
  choose! f h_f using h₁
  let mx := (s.image f).max' (image_nonempty.mpr hs)
  obtain ⟨x, x_mem, hx⟩ : ∃ x ∈ s, f x = mx :=
    suffices mx ∈ (s.image f) by
      rwa [Finset.mem_image] at this
    max'_mem (image f s) (image_nonempty.mpr hs)
  obtain ⟨b, b_le, hb₂⟩ := h₂ mx
  use b
  refine ⟨?_, hb₂⟩
  intro y y_mem
  suffices f y ≤ mx from h_mono y y_mem (f y) b (le_trans this b_le) (h_f y y_mem)
  exact (s.image f).le_max' (f y) (mem_image_of_mem f y_mem)

end Finset
