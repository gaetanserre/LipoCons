/-
- Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.CompletePartialOrder

open ENNReal MeasureTheory

namespace ENNReal

lemma contra_ineq {a b : ℝ≥0∞} (hb : b ≠ ⊤) (i1 : a < b) (i2 : b ≤ a) : False := by
  have ha : a ≠ ⊤ := LT.lt.ne_top i1
  have : a.toReal < b.toReal := toReal_strict_mono hb i1
  have : b.toReal ≤ a.toReal := (toReal_le_toReal hb ha).mpr i2
  linarith

end ENNReal

lemma prop_measure_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (i : IsProbabilityMeasure μ) {A : Set α} : μ A ≠ ⊤ := by
  have : IsFiniteMeasure μ := IsZeroOrProbabilityMeasure.toIsFiniteMeasure μ
  exact measure_ne_top μ A
