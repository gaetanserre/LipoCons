/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Defs.NPos
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Order.Basic

open Filter Topology

namespace Filter.Tendsto

variable {α β : Type*} [TopologicalSpace β] [Preorder α]

lemma nstar_tendsto_iff_tendsto {f : ℕ → β} {b : β} :
    Tendsto (fun (n : ℕ₀) => f n) atTop (𝓝 b) ↔ Tendsto f atTop (𝓝 b) := by
  set g := (fun (n : ℕ₀) => f n)
  constructor
  · intro h U hU
    specialize h hU
    simp_rw [mem_map, mem_atTop_sets, Set.mem_preimage] at h ⊢
    obtain ⟨a, ha⟩ := h
    use a
    intro y hy
    exact ha ⟨y, Nat.lt_of_lt_of_le a.2 hy⟩ hy
  intro h U hU
  specialize h hU
  simp_rw [mem_map, mem_atTop_sets, Set.mem_preimage] at h ⊢
  obtain ⟨a, ha⟩ := h
  use ⟨a + 1, Nat.zero_lt_succ a⟩
  intro b hb
  exact ha b <| Nat.le_of_succ_le hb

variable [Preorder β] [OrderTopology β]

lemma tendsto_le_nat {f g h : ℕ → β} {b : β}
    (hgf : ∀ n > 0, g n ≤ f n) (hfh : ∀ n > 0, f n ≤ h n)
    (hg : Tendsto g atTop (𝓝 b)) (hh : Tendsto h atTop (𝓝 b)) :
    Tendsto f atTop (𝓝 b) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
    <;> rw [eventually_atTop]
    <;> use 1
    <;> intro b hb
  · exact hgf b hb
  · exact hfh b hb

variable [AddZeroClass β] [CanonicallyOrderedAdd β]

lemma tendsto_zero_le_nat {f g : ℕ → β} (hfg : ∀ n > 0, f n ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  let c := fun (_ : ℕ) => (0 : β)
  exact tendsto_le_nat (fun x _ => zero_le (f x)) hfg tendsto_const_nhds hg

end Filter.Tendsto
