import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Max

namespace Fintype

variable {α β : Type*} [Fintype α] [Nonempty α] [LinearOrder β] (f : α → β)

def max_image : β := by
  let im := (Finset.univ : Finset α).image f
  have im_ne : im.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  exact im.max' im_ne

lemma le_max_image : ∀ y, f y ≤ max_image f := by
  let im := (Finset.univ : Finset α).image f
  have im_ne : im.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  --have : max_image f = im.max' im_ne := rfl
  obtain ⟨b, hb, hb2⟩ := Finset.mem_image.mp (im.max'_mem im_ne)
  intro y
  exact im.le_max' (f y) (Finset.mem_image.mpr ⟨y, Finset.mem_univ y ,rfl⟩)

end Fintype
