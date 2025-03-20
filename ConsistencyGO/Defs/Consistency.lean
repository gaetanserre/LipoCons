/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Algorithm
import ConsistencyGO.Utils.Compact
import ConsistencyGO.Utils.Tendsto
import Mathlib.Analysis.Normed.Order.Lattice

variable {α : Type*} [PseudoMetricSpace α]

/--
Given a sequence `u` and a element `x`, returns `min_(0 ≤ i < n) dist (u i) x.
-/
noncomputable def min_dist_x :=
  fun {n : ℕ} (u : Fin n → α) (x : α) => Tuple.min ((fun xi => dist xi x) ∘ u)

/--
`min_dist_x` is continuous
-/
lemma min_dist_x_continuous {n : ℕ} (u : Fin n → α) : Continuous (min_dist_x u) := by
  by_cases h : n = 0
  · have empty : ¬Nonempty (Fin n) := by
      rw [←Fin.pos_iff_nonempty]
      exact Eq.not_gt h
    let e : ℝ := instNonemptyOfInhabited.some
    suffices h : min_dist_x u = fun x => e by rw [h]; exact continuous_const
    ext x
    unfold min_dist_x Tuple.min Fintype.min_image Fintype.min_image'
    split
    · contradiction
    rfl

  have ne_fin : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero h)
  have ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ne_fin

  set g := fun (i : Fin n) (x : α) => dist (u i) x

  have continuous_inf_g : Continuous (Finset.univ.inf' ne g) := by
    suffices h : ∀ i ∈ Finset.univ, Continuous (g i) from Continuous.finset_inf' ne h
    intro i _
    exact Continuous.dist continuous_const continuous_id

  suffices h : min_dist_x u = Finset.univ.inf' ne g by rwa [h]
  ext x
  unfold min_dist_x Tuple.min Fintype.min_image Fintype.min_image'
  split
  · simp only [Function.comp_apply, Finset.inf'_apply, g]
  contradiction

variable {Ω : Set α} [CompactSpace Ω] [Nonempty Ω]
variable {β : Type*} [Nonempty β] [PseudoMetricSpace β] [LinearOrder β] [ClosedIciTopology β]

/--
The maximum of a continuous function over `α`.
-/
noncomputable def fmax {f : Ω → β} (cont : Continuous f) := f (compact_argmax cont)

variable [MeasurableSpace α]

/--
Given an algorithm `A`, the function that, given `ε` and `n`, returns
the measure of the set of sequences of size `n` such that the maximum of
`f` over these sequences is at least `ε` away from from `fmax`.
-/
def measure_dist_max (A : Algorithm Ω β) {f : Ω → β} (cont : Continuous f) :=
  fun ε n => A.μ f n {u | dist (Tuple.max (f ∘ u)) (fmax cont) > ε}


open Filter Topology
/--
**Main definition**: An algorithm `A` is consistent over `f`
if for any `ε > 0`, `lim_(n → ∞) measure_dist_max n = 0`.
-/
def isConsistent (A : Algorithm Ω β) {f : Ω → β} (cont : Continuous f) : Prop :=
  ∀ ε > 0, Tendsto (measure_dist_max A cont ε) atTop (𝓝 0)

/--
The set of all Lipschitz functions.
-/
def all_lipschitz := {f : Ω → β | ∃ κ, LipschitzWith κ f}

/--
An algorithm `A` is consistent over all Lipschitz functions.
-/
def isConsistentOverLipschitz (A : Algorithm Ω β) {f : Ω → β} (hf : f ∈ all_lipschitz) : Prop :=
  isConsistent A hf.choose_spec.continuous

/--
Given a sequence `u`, maximum over `Ω` of `min_dist_x u`: the maximum distance between
any element in `Ω` and `u`.
-/
noncomputable def max_min_dist {n : ℕ} (u : Fin n → Ω) :=
  min_dist_x u (compact_argmax (min_dist_x_continuous u))

/--
**Main definition**: Given a function `f`, an algorithm `A` sample the whole space
if `∀ ε > 0, lim_(n → ∞) A.μ f n {u | max_min_dist u > ε} = 0`.
-/
noncomputable def sample_whole_space (A : Algorithm Ω β) (f : Ω → β) : Prop :=
  ∀ ε > 0, Tendsto (fun n => A.μ f n {u | max_min_dist u > ε}) atTop (𝓝 0)

lemma ε_cover_ne {ε : ℝ} (hε : ε > 0) {α : Type*} [PseudoMetricSpace α] (Ω : Set α)
    [Nonempty Ω] [CompactSpace Ω] :
    {n : nstar | ∃ (t : Finset Ω), t.card = n.1 ∧ Set.univ = ⋃ x ∈ t, Metric.ball x ε}.Nonempty
    := by
  let U := fun (x : Ω) => Metric.ball x ε
  have hU : ∀ (x : Ω), U x ∈ nhds x := fun x => Metric.ball_mem_nhds x hε
  obtain ⟨t, ht⟩ := finite_cover_nhds hU
  refine ⟨⟨t.card, ?_⟩, t, rfl, ht.symm⟩
  by_contra h_contra
  have union_is_empty : ⋃ x ∈ t, U x = ∅ := by
      rw [Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero <| Nat.le_of_not_lt h_contra)]
      simp only [Finset.not_mem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
  rw [union_is_empty] at ht
  exact Set.empty_ne_univ ht
