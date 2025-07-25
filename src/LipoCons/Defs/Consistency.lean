/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Defs.Algorithm
import LipoCons.Defs.Lipschitz
import LipoCons.Utils.Compact
import Mathlib.Analysis.Normed.Order.Lattice

set_option maxHeartbeats 0

variable {α : Type*} [PseudoMetricSpace α]

/-- Given a sequence `u` and a element `x`, returns `min_(0 ≤ i < n) dist (u i) x. -/
-- ANCHOR: min_dist_x
noncomputable def min_dist_x :=
  fun {n : ℕ} (u : iter α n) (x : α) => Tuple.min ((fun xi => dist xi x) ∘ u)
-- ANCHOR_END: min_dist_x

/-- `min_dist_x` is continuous -/
lemma min_dist_x_continuous {n : ℕ} (u : iter α n) : Continuous (min_dist_x u) := by

  haveI ne_fin : Nonempty (Fin (n + 1)) := instNonemptyOfInhabited

  have ne_univ : (Finset.univ : Finset (Fin (n + 1))).Nonempty :=
      Finset.univ_nonempty_iff.mpr ne_fin
  set g := fun (i : Fin (n + 1)) (x : α) => dist (u i) x

  have continuous_inf_g : Continuous (Finset.univ.inf' ne_univ g) := by
    suffices h : ∀ i ∈ Finset.univ, Continuous (g i) from Continuous.finset_inf' ne_univ h
    intro i _
    fun_prop

  suffices h : min_dist_x u = Finset.univ.inf' ne_univ g by rwa [h]
  ext x
  unfold min_dist_x Tuple.min Fintype.min_image Fintype.min_image'
  split
  · simp only [Function.comp_apply, Finset.inf'_apply, g]
  · contradiction

variable [CompactSpace α] [Nonempty α] {β : Type*} [Nonempty β] [PseudoMetricSpace β]
  [LinearOrder β] [ClosedIciTopology β] [ClosedIicTopology β]

/-- The maximum of a Lipschitz function over `α`. -/
noncomputable def fmax {f : α → β} (hf : Lipschitz f) := f (compact_argmax hf.continuous)

/-- The minimum of a Lipschitz function over `α`. -/
noncomputable def fmin {f : α → β} (hf : Lipschitz f) := f (compact_argmin hf.continuous)

variable [MeasurableSpace α] [MeasurableSpace β] [OpensMeasurableSpace α] [BorelSpace β]

/-- The set of sequences of size `n` such that the maximum of `f` over
these sequences is at least `ε` away from from `fmax`. -/
def set_dist_max {f : α → β} (hf : Lipschitz f) {n : ℕ} (ε : ℝ) : Set (iter α n) :=
  {u | dist (Tuple.max (f ∘ u)) (fmax hf) > ε}

/-- Given an algorithm `A`, the function that, given `ε` and `n`, returns
the measure of the set of sequences of size `n` such that the maximum of
`f` over these sequences is at least `ε` away from from `fmax`. -/
noncomputable def measure_dist_max (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) :=
  fun ε n => A.measure hf.continuous n (set_dist_max hf ε)

open Filter Topology
/-- **Main definition**: An algorithm `A` is consistent over a Lipschitz function `f`
if for any `ε > 0`, `lim_(n → ∞) measure_dist_max n = 0`. -/
-- ANCHOR: is_consistent
def is_consistent (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) : Prop :=
  ∀ ⦃ε⦄, 0 < ε → Tendsto (measure_dist_max A hf ε) atTop (𝓝 0)
-- ANCHOR_END: is_consistent

/-- An algorithm `A` is consistent over all Lipschitz functions. -/
def is_consistent_over_Lipschitz (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) : Prop :=
  is_consistent A hf

/-- Given a sequence `u`, maximum over `α` of `min_dist_x u`: the maximum distance between
any element in `α` and `u`. -/
-- ANCHOR: max_min_dist
noncomputable def max_min_dist {n : ℕ} (u : iter α n) :=
  min_dist_x u (compact_argmax (min_dist_x_continuous u))
-- ANCHOR_END: max_min_dist

/-- **Main definition**: Given a function `f`, an algorithm `A` sample the whole space
if `∀ ε > 0, lim_(n → ∞) A.measure f n {u | max_min_dist u > ε} = 0`. -/
-- ANCHOR: sample_whole_space
noncomputable def sample_whole_space (A : Algorithm α β) {f : α → β} (hf : Continuous f) : Prop :=
  ∀ ε > 0, Tendsto (fun n => A.measure hf n {u | max_min_dist u > ε}) atTop (𝓝 0)
-- ANCHOR_END: sample_whole_space

open unitInterval
