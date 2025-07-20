/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Defs.NPos
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs

variable (α : Type*) [Nonempty α] [PseudoMetricSpace α] [CompactSpace α]

/-! For any nonempty compact space `a` equipped with a pseudo-metric, there exists a finite cover
 of `α` by balls of radius `ε`. -/
lemma ε_cover_ne {ε : ℝ} (hε : ε > 0) :
    {n : ℕ₀ | ∃ (t : Finset α), t.card = n ∧ Set.univ = ⋃ x ∈ t, Metric.ball x ε}.Nonempty := by
  let U := fun (x : α) => Metric.ball x ε
  have hU : ∀ (x : α), U x ∈ nhds x := fun x => Metric.ball_mem_nhds x hε
  obtain ⟨t, ht⟩ := finite_cover_nhds hU
  refine ⟨⟨t.card, ?_⟩, t, rfl, ht.symm⟩
  by_contra h_contra
  have union_is_empty : ⋃ x ∈ t, U x = ∅ := by
    rw [Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero <| Nat.le_of_not_lt h_contra)]
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
  rw [union_is_empty] at ht
  exact Set.empty_ne_univ ht
