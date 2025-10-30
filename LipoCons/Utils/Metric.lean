/-
- Created in 2025 by Gaëtan Serré
-/

import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Metric

/-- A function between pseudometric spaces is continuous if and only if for every point and every
positive ε, there exists a positive δ such that points within distance δ are mapped to points
within distance ε (using non-strict inequalities). -/
lemma continuous_iff_le {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Continuous f ↔ ∀ b, ∀ ε > 0, ∃ δ > 0, ∀ a, dist a b ≤ δ → dist (f a) (f b) ≤ ε := by
  rw [Metric.continuous_iff]
  constructor
  · intro h b ε hε
    obtain ⟨δ, hδ, h⟩ := h b ε hε
    refine ⟨δ/2, half_pos hδ, ?_⟩
    intro a ha
    exact le_of_lt (h a (lt_of_le_of_lt ha (div_two_lt_of_pos hδ)))
  intro h b ε hε
  obtain ⟨δ, hδ, h⟩ := h b (ε/2) (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  exact lt_of_le_of_lt (h a (le_of_lt ha)) (div_two_lt_of_pos hε)

end Metric
