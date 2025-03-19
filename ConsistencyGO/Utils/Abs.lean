/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Analysis.Normed.Field.Basic

namespace Abs

lemma abs_lt {a b : ℝ} (h : a ≤ b) : |a - b| = b - a := by
  have le : a - b ≤ 0 := tsub_nonpos.mpr h
  by_cases h' : a - b = 0
  · rw [h']
    rw [neg_inj.mp (neg_eq_of_add_eq_zero_right h')]
    simp only [abs_zero, sub_self]
  rw [abs_of_neg (lt_of_le_of_ne le h')]
  exact neg_sub a b

end Abs
