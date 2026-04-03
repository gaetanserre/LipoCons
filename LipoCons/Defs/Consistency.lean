/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Algorithm
import LipoCons.Defs.Lipschitz
import LipoCons.Utils.Compact
import Mathlib.Analysis.Normed.Order.Lattice

variable {α : Type*} [PseudoMetricSpace α]

/-- Given a sequence `u` and a element `x`, returns `min_(0 ≤ i < n) dist (u i) x. -/
-- ANCHOR: min_dist_x
noncomputable def min_dist_x :=
  fun {n : ℕ} (u : iter α n) (x : α) => Tuple.min ((fun xi => dist xi x) ∘ u)
-- ANCHOR_END: min_dist_x

/-- For any `(u : iter α n)`, `min_dist_x u` is continuous -/
lemma min_dist_x_continuous {n : ℕ} (u : iter α n) : Continuous (min_dist_x u) := by
  haveI ne_fin : Nonempty (Finset.Iic n) := inferInstance
  have ne_univ : (Finset.univ : Finset (Finset.Iic n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ne_fin
  set g := fun (i : Finset.Iic n) (x : α) => dist (u i) x
  have continuous_inf_g : Continuous (Finset.univ.inf' ne_univ g) := by
    suffices h : ∀ i ∈ Finset.univ, Continuous (g i) from Continuous.finset_inf' ne_univ h
    intro i _
    fun_prop
  suffices h : min_dist_x u = Finset.univ.inf' ne_univ g by rwa [h]
  ext x
  unfold min_dist_x
  simp [g]
  congr

variable {β : Type*} [CompactSpace α] [Nonempty α] [MeasurableSpace α] [MeasurableSpace β]
  [PseudoMetricSpace β] [OpensMeasurableSpace α] [BorelSpace β]

/-- Given a sequence `u`, maximum over `α` of `min_dist_x u`: the maximum distance between
any element in `α` and `u`. -/
-- ANCHOR: max_min_dist
noncomputable def max_min_dist {n : ℕ} (u : iter α n) :=
  min_dist_x u (compact_argmax (min_dist_x_continuous u))
-- ANCHOR_END: max_min_dist

open Filter Topology in
/-- **Main definition**: Given a function `f`, an algorithm `A` sample the whole space
if `∀ ε > 0, lim_(n → ∞) A.measure f n {u | max_min_dist u > ε} = 0`. -/
-- ANCHOR: sample_whole_space
noncomputable def sample_whole_space (A : Algorithm α β) {f : α → β} (hf : Continuous f) :=
  ∀ ε > 0, Tendsto (fun n =>
    A.fin_measure hf.measurable {u : iter α n | max_min_dist u > ε}) atTop (𝓝 0)
-- ANCHOR_END: sample_whole_space

variable [Nonempty β] [LinearOrder β] [ClosedIciTopology β] [ClosedIicTopology β]

/-- The maximum of a Lipschitz function over `α`. -/
noncomputable def fmax {f : α → β} (hf : Lipschitz f) := f (compact_argmax hf.continuous)

/-- The minimum of a Lipschitz function over `α`. -/
noncomputable def fmin {f : α → β} (hf : Lipschitz f) := f (compact_argmin hf.continuous)

variable [MeasurableSpace α] [MeasurableSpace β] [OpensMeasurableSpace α] [BorelSpace β]

/-- The set of sequences of size `n + 1` such that the maximum of `f` over
these sequences is at least `ε` away from from `fmax`. -/
-- ANCHOR: set_dist_max
def set_dist_max {f : α → β} (hf : Lipschitz f) {n : ℕ} (ε : ℝ) :=
  {u : iter α n | dist (Tuple.max (f ∘ u)) (fmax hf) > ε}
-- ANCHOR_END: set_dist_max

/-- Given an algorithm `A`, the function that, given `ε` and `n`, returns
the measure of the set of sequences of size `n + 1` such that the maximum of
`f` over these sequences is at least `ε` away from from `fmax`. -/
-- ANCHOR: measure_dist_max
noncomputable def measure_dist_max (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) :=
  fun ε n => A.fin_measure hf.measurable (set_dist_max hf (n := n) ε)
-- ANCHOR_END: measure_dist_max

open Filter Topology
/-- **Main definition**: An algorithm `A` is consistent over a Lipschitz function `f`
if for any `ε > 0`, `lim_(n → ∞) measure_dist_max n = 0`. -/
-- ANCHOR: is_consistent
def is_consistent (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) :=
  ∀ ⦃ε⦄, 0 < ε → Tendsto (measure_dist_max A hf ε) atTop (𝓝 0)
-- ANCHOR_END: is_consistent

open unitInterval
