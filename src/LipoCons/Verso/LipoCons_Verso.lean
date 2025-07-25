/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.ECover
import LipoCons.Utils.ENNReal
import LipoCons.Utils.Finset
import LipoCons.Utils.Indistinguishable
import LipoCons.Utils.Metric
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! **WARNING!!** This file is only to be used in the Verso manual. The proof of this theorem is
located in `LipoCons.lean`. -/

open Metric Tuple MeasureTheory Set ENNReal

variable {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α] [NormedSpace ℝ α]
  [CompactSpace α] [Nonempty α] [OpensMeasurableSpace α]

-- ANCHOR: sample_iff_consistent
theorem sample_iff_consistent' (A : Algorithm α ℝ) :
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → sample_whole_space A hf.continuous)
    ↔
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → is_consistent_over_Lipschitz A hf) := by
-- ANCHOR_END: sample_iff_consistent
  sorry
