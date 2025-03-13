/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Algorithm
import ConsistencyGO.Compact
import ConsistencyGO.Utils
import Mathlib

open Tuple NNReal Filter Topology

variable {α : Type*} [PseudoMetricSpace α] {Ω : Set α}

/--
Given a sequence `u` and a element `x`, returns `min_(0 ≤ i < n) dist (u i) x.
-/
noncomputable def min_dist_x :=
  fun {n : ℕ} (u : Fin n → Ω) (x : Ω) => Tuple.min ((fun xi => dist xi x) ∘ u)

/--
`min_dist_x` is continuous
-/
lemma min_dist_x_continuous {n : ℕ} (u : Fin n → Ω) : Continuous (min_dist_x u) := by
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

  set g := fun (i : Fin n) (x : Ω) => dist (u i) x

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

/-
We define two spaces `α` and `β` with topological properties and we define
a continuous function `f` over a compact set of `α`, `Ω`.
-/
variable {β : Type*} [MeasurableSpace α]
[Nonempty β] [Dist β] [LinearOrder β] [PseudoMetricSpace β]
[ClosedIciTopology β] [ClosedIicTopology β]
[Nonempty Ω] [CompactSpace Ω]

/--
The maximum of a continuous function over `Ω`.
-/
noncomputable def fmax {f : Ω → β} (cont : Continuous f) := f (compact_argmax cont)

/--
Given an algorithm `A`, the function that, given `ε` and `n`, returns
the measure of the set of sequences of size `n` such that the maximum of
`f` over these sequences is at least `ε` away from from `fmax`.
-/
def measure_dist_max (A : Algorithm Ω β) {f : Ω → β} (cont : Continuous f) :=
  fun ε n => A.μ f n {u | dist (Tuple.max (f ∘ u)) (fmax cont) > ε}

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

variable [SemilatticeSup Ω]

example (A : Algorithm Ω ℝ) :
    (∀ ⦃f : Ω → ℝ⦄, f ∈ all_lipschitz → sample_whole_space A f)
    ↔
    (∀ ⦃f : Ω → ℝ⦄, (hf : f ∈ all_lipschitz) → isConsistentOverLipschitz A hf)
    := by
  constructor
  · intro h f hf ε hε
    have hcont := hf.choose_spec.continuous

    suffices h' : ∃ δ > 0, ∀ n > 0,
        {(u : Fin n → Ω) | dist (Tuple.max (f ∘ u)) (fmax hcont) > ε} ⊆ {u | max_min_dist u > δ} by
      obtain ⟨δ, hδ, h'⟩ := h'
      have μ_mono : ∀ n > 0, measure_dist_max A hcont ε n ≤ (A.μ f n) {u | max_min_dist u > δ} :=
        fun n hn => MeasureTheory.OuterMeasureClass.measure_mono (A.μ f n) (h' n hn)
      exact Tendsto.tendsto_zero_le_nat μ_mono (h hf δ hδ)

    let Xₑ := {x | dist (f x) (fmax hcont) ≤ ε}
    let x' := compact_argmax hcont
    have : f x' = fmax hcont := rfl
    obtain ⟨δ, hδ, hdist⟩ := (Metric.continuous_iff.mp hcont) x' ε hε
    let B := Metric.ball x' δ
    have : B ⊆ Xₑ := by
      intro e he
      rw [this] at hdist
      exact le_of_lt (hdist e he)
    use δ
    refine ⟨hδ, ?_⟩
    intro n n_pos
    -- Réécrire la preuve proprement
    have : {(u : (Fin n) → Ω) | dist (Tuple.max (f ∘ u)) (fmax hcont) > ε} ⊆
        {u | ∀ i, u i ∉ B} := by
      intro e (he : dist (Tuple.max (f ∘ e)) (fmax hcont) > ε)
      intro i
      set ei := e i
      by_contra hcontra
      specialize hdist ei hcontra
      rw [Compact.dist_max_compact hcont ei] at hdist
      have univ_ne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp n_pos
      obtain ⟨j, hj⟩ := arg_tuple_max f n_pos e
      rw [←hj] at he
      unfold fmax at he
      rw [Compact.dist_max_compact hcont (e j)] at he
      have : f ei ≤ f (e j) := by
        rw [hj]
        exact Tuple.le_max (f ∘ e) n_pos i
      have : f (compact_argmax hcont) - f (e j) ≤ f (compact_argmax hcont) - f ei :=
        tsub_le_tsub_left this _
      have : f (compact_argmax hcont) - f (e j) < ε := lt_of_le_of_lt this hdist
      linarith

    sorry
  sorry
