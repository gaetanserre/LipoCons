/-
- Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.CompletePartialOrder

open ENNReal MeasureTheory

namespace ENNReal

lemma contra_ineq {a b : ℝ≥0∞} (i1 : a < b) (i2 : b ≤ a) : False := by
  have ha : a ≠ ⊤ := LT.lt.ne_top i1
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top ha i2
  have : a.toReal < b.toReal := toReal_strict_mono hb i1
  have : b.toReal ≤ a.toReal := (toReal_le_toReal hb ha).mpr i2
  linarith

end ENNReal
