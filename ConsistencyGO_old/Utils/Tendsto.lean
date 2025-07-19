/-
- Created in 2025 by Gaëtan Serré
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.Basic

open Filter Topology

def nstar := {n : ℕ | 0 < n}

instance : Nonempty nstar := ⟨1, Nat.one_pos⟩

namespace Tendsto

variable {α β : Type*} [TopologicalSpace β]

lemma nstar_tendsto_iff_tendsto {f : ℕ → β} {b : β} :
    Tendsto (fun (n : nstar) => f n.1) atTop (𝓝 b) ↔ Tendsto f atTop (𝓝 b) := by
  set g := (fun (n : nstar) => f n.1)
  constructor
  · intro h U hU
    specialize h hU
    simp_rw [mem_map, mem_atTop_sets, Set.mem_preimage] at h ⊢
    obtain ⟨a, ha⟩ := h
    use a.1
    intro y hy
    exact ha ⟨y, Nat.lt_of_lt_of_le a.2 hy⟩ hy
  intro h U hU
  specialize h hU
  simp_rw [mem_map, mem_atTop_sets, Set.mem_preimage] at h ⊢
  obtain ⟨a, ha⟩ := h
  use ⟨a + 1, Nat.zero_lt_succ a⟩
  intro b hb
  exact ha b.1 <| Nat.le_of_succ_le hb

variable [Preorder α] [Preorder β] [OrderTopology β] [AddZeroClass β]

lemma tendsto_le_nat {f g h : ℕ → β} {b : β}
    (h1 : ∀ n > 0, f n ≤ g n) (h2 : ∀ n > 0, h n ≤ f n)
    (hg : Tendsto g atTop (𝓝 b)) (hh : Tendsto h atTop (𝓝 b)) :
    Tendsto f atTop (𝓝 b) := by
  let c := fun (_ : ℕ) => (0 : β)
  have ev_le_fg : ∀ᶠ n in atTop, f n ≤ g n := by
    rw [eventually_iff]
    suffices h : {n | n > 0 ∧ f n ≤ g n} ∈ atTop by
      filter_upwards [h] with _ hn using hn.2
    rw [mem_atTop_sets]
    use 1
    intro b hb
    exact ⟨hb, h1 b hb⟩

  have ev_le_hf : ∀ᶠ n in atTop, h n ≤ f n := by
    rw [eventually_iff]
    suffices h : {n | n > 0 ∧ h n ≤ f n} ∈ atTop by
      filter_upwards [h] with _ hn using hn.2
    rw [mem_atTop_sets]
    use 1
    intro b hb
    exact ⟨hb, h2 b hb⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hh hg ev_le_hf ev_le_fg

variable [CanonicallyOrderedAdd β]

lemma tendsto_zero_le_nat {f g : ℕ → β} (h : ∀ n > 0, f n ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  let c := fun (_ : ℕ) => (0 : β)
  have le_const : ∀ n > 0, c n ≤ f n := (fun x _ => zero_le (f x))
  exact tendsto_le_nat h le_const hg tendsto_const_nhds

end Tendsto
