/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Max

open Classical

namespace Fintype

variable {α β : Type*} [Fintype α] [LinearOrder β] (f : α → β)

def max_image' [Nonempty α] : β := by
  let im := (Finset.univ : Finset α).image f
  have im_ne : im.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  exact im.max' im_ne

lemma le_max_image' [Nonempty α] : ∀ y, f y ≤ max_image' f := by
  let im := (Finset.univ : Finset α).image f
  have im_ne : im.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  obtain ⟨b, hb, hb2⟩ := Finset.mem_image.mp (im.max'_mem im_ne)
  intro y
  exact im.le_max' (f y) (Finset.mem_image.mpr ⟨y, Finset.mem_univ y ,rfl⟩)

variable [i : Nonempty β]

noncomputable def max_image : β :=
  if _ : Nonempty α then max_image' f
  else i.some

lemma max_image_apply [Nonempty α] : max_image f = max_image' f := by
  unfold max_image
  split
  · rfl
  contradiction

lemma le_max_image [Nonempty α] : ∀ y, f y ≤ max_image f := by
  rw [max_image_apply]
  exact le_max_image' f

end Fintype
