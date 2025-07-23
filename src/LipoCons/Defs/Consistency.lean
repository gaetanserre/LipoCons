/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Defs.Algorithm
import LipoCons.Defs.Lipschitz
import LipoCons.Defs.NPos
import LipoCons.Utils.Compact
import Mathlib.Analysis.Normed.Order.Lattice

set_option maxHeartbeats 0

variable {α : Type*} [PseudoMetricSpace α]

/-! Given a sequence `u` and a element `x`, returns `min_(0 ≤ i < n) dist (u i) x. -/
noncomputable def min_dist_x :=
  fun {n : ℕ} (u : Fin n → α) (x : α) => Tuple.min ((fun xi => dist xi x) ∘ u)

/-- `min_dist_x` is continuous -/
@[continuity]
lemma min_dist_x_continuous {n : ℕ} (u : Fin n → α) : Continuous (min_dist_x u) := by
  by_cases h : n = 0
  · haveI : ¬Nonempty (Fin n) := by
      rw [←Fin.pos_iff_nonempty]
      exact Eq.not_gt h
    let e := Classical.arbitrary ℝ
    suffices h : min_dist_x u = fun x => e by rw [h]; exact continuous_const
    ext x
    unfold min_dist_x Tuple.min Fintype.min_image Fintype.min_image'
    split
    · contradiction
    rfl

  have ne_fin : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero h)

  have ne_univ : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ne_fin
  set g := fun (i : Fin n) (x : α) => dist (u i) x

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

/- lemma min_dist_x_continuous' (n : ℕ) : Continuous (min_dist_x (α := α) (n := n)) := by
  refine continuous_pi ?_
  intro i
  exact?

  sorry -/

variable [CompactSpace α] [Nonempty α] {β : Type*} [Nonempty β] [PseudoMetricSpace β]
  [LinearOrder β] [ClosedIciTopology β] [ClosedIicTopology β]

/-- The maximum of a Lipschitz function over `α`. -/
noncomputable def fmax {f : α → β} (hf : Lipschitz f) := f (compact_argmax hf.continuous)
noncomputable def fmin {f : α → β} (hf : Lipschitz f) := f (compact_argmin hf.continuous)

variable [MeasurableSpace α]

/-! The set of sequences of size `n` such that the maximum of `f` over
these sequences is at least `ε` away from from `fmax`. -/
def set_dist_max {f : α → β} (hf : Lipschitz f) {n : ℕ} (ε : ℝ) : Set (Fin n → α) :=
  {u | dist (Tuple.max (f ∘ u)) (fmax hf) > ε}

/-! Given an algorithm `A`, the function that, given `ε` and `n`, returns
the measure of the set of sequences of size `n` such that the maximum of
`f` over these sequences is at least `ε` away from from `fmax`. -/
def measure_dist_max (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) :=
  fun ε n => A.μ f n (set_dist_max hf ε)

open Filter Topology
/-! **Main definition**: An algorithm `A` is consistent over a Lipschitz function `f`
if for any `ε > 0`, `lim_(n → ∞) measure_dist_max n = 0`. -/
def isConsistent (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) : Prop :=
  ∀ ⦃ε⦄, 0 < ε → Tendsto (measure_dist_max A hf ε) atTop (𝓝 0)

/-! An algorithm `A` is consistent over all Lipschitz functions. -/
def isConsistentOverLipschitz (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) : Prop :=
  isConsistent A hf

/-! Given a sequence `u`, maximum over `α` of `min_dist_x u`: the maximum distance between
any element in `α` and `u`. -/
noncomputable def max_min_dist {n : ℕ} (u : Fin n → α) :=
  min_dist_x u (compact_argmax (min_dist_x_continuous u))

lemma max_min_dist_continuous {n : ℕ₀} : Continuous (max_min_dist (n := n) (α := α)) := by
  /- have : ∀ (u : Fin n → α), Continuous (min_dist_x u) :=
    fun u ↦ min_dist_x_continuous u
  refine Continuous.comp' (by exact?) ?_ -/
  let f := fun u : Fin n → α => compact_argmax (min_dist_x_continuous u)
  have t : ∀ u1 u2, dist (max_min_dist u1) (max_min_dist u2) ≤ dist u1 u2 + dist (f u1) (f u2) := by
    intro u1 u2
    unfold max_min_dist
    set x1 := compact_argmax (min_dist_x_continuous u1)
    set x2 := compact_argmax (min_dist_x_continuous u2)
    rw [show f u1 = x1 by rfl]
    rw [show f u2 = x2 by rfl]
    unfold min_dist_x
    obtain ⟨i1, hi1⟩ := Tuple.argmin (fun xi ↦ dist xi x1) n.2 u1
    obtain ⟨i2, hi2⟩ := Tuple.argmin (fun xi ↦ dist xi x2) n.2 u2
    rw [←hi1, ←hi2]
    have : 0 ≤ dist (u1 i1) x1 - dist (u2 i2) x2 := by sorry
    show |dist (u1 i1) x1 - dist (u2 i2) x2| ≤ dist u1 u2 + dist x1 x2
    rw [abs_of_nonneg this]
    suffices dist (u1 i1) x1 ≤ dist u1 u2 + dist x1 x2 + dist (u2 i2) x2 from
      (OrderedSub.tsub_le_iff_right _ _ _).mpr this

    let i := (Tuple.dist_exists n.2 u1 u2).choose
    have di : dist u1 u2 = dist (u1 i) (u2 i) :=
      (Tuple.dist_exists n.2 u1 u2).choose_spec
    rw [di]

    have : ∀ i, dist (u1 i1) x1 ≤ dist (u1 i) x1 :=



    sorry

  have : Continuous f := by sorry

  rw [Metric.continuous_iff]
  intro u1 ε ε_pos

  have ε_4_pos : 0 < ε / 4 := by
    rw [show ε / 4 = ε / 2 / 2 by ring]
    exact half_pos (half_pos ε_pos)
  obtain ⟨δ, δ_pos, hδ⟩ := Metric.continuous_iff.mp this u1 (ε / 4) ε_4_pos
  refine ⟨min δ (ε/4), ?_, ?_⟩
  · show 0 < min δ (ε / 4)
    rw [lt_min_iff]
    exact ⟨δ_pos, ε_4_pos⟩
  intro u2 hu2
  have : dist u2 u1 < δ := by
    rw [lt_min_iff] at hu2
    exact hu2.1
  specialize hδ u2 this
  have : dist u2 u1 < ε/4 := by
    rw [lt_min_iff] at hu2
    exact hu2.2
  rw [dist_comm]
  specialize t u1 u2
  calc _ ≤ dist u1 u2 + dist (f u1) (f u2) := t
  _ < ε/4 + dist (f u1) (f u2) := by
    rw [dist_comm] at this
    exact (add_lt_add_iff_right (dist (f u1) (f u2))).mpr this
  _ < ε/4 + ε/4 := by
    rw [dist_comm] at hδ
    exact (Real.add_lt_add_iff_left (ε / 4)).mpr hδ
  _ = ε/2 := by ring
  _ < ε := div_two_lt_of_pos ε_pos


  /- suffices LipschitzWith 1 max_min_dist from this.continuous
  refine LipschitzWith.of_le_add ?_
  intro u1 u2
  let i := (Tuple.dist_exists n.2 u1 u2).choose
  have di : dist u1 u2 = dist (u1 i) (u2 i) :=
    (Tuple.dist_exists n.2 u1 u2).choose_spec
  rw [di]
  simp [max_min_dist]
  set x1 := compact_argmax (min_dist_x_continuous u1)
  set x2 := compact_argmax (min_dist_x_continuous u2)
  have : |min_dist_x u1 x1 - min_dist_x u1 x2| ≤ |dist u1 u2 + dist x1 x2| := by sorry -/
  --have : ∀ u1, ∀ ε > 0, ∃ δ > 0, ∀ u2, dist u1 u2 < δ → dist

  /- refine Metric.continuous_iff.mpr ?_
  intro u₁ ε ε_pos
  refine ⟨ε, ε_pos, ?_⟩
  intro u₂ hu₁u₂
  let i := (Tuple.dist_exists n.2 u₂ u₁).choose
  have di : dist u₂ u₁ = dist (u₂ i) (u₁ i) :=
    (Tuple.dist_exists n.2 u₂ u₁).choose_spec
  rw [di] at hu₁u₂
  simp [max_min_dist]
  replace hu₁u₂ : dist (u₂ i) (u₁ i) < ε := hu₁u₂
  set x₂ := compact_argmax (min_dist_x_continuous u₂)
  set x₁ := compact_argmax (min_dist_x_continuous u₁)
  have : ∀ j, dist (u₂ j) (u₁ j) ≤ dist (u₂ i) (u₁ i) := Tuple.dist_exists_le n.2 u₂ u₁
  have : ∀ x, min_dist_x u₂ x ≤ min_dist_x u₂ x₂ :=
    fun x => compact_argmax_apply (min_dist_x_continuous u₂) x
  have : ∀ x, min_dist_x u₁ x ≤ min_dist_x u₁ x₁ :=
    fun x => compact_argmax_apply (min_dist_x_continuous u₁) x -/

  --sorry




/-! **Main definition**: Given a function `f`, an algorithm `A` sample the whole space
if `∀ ε > 0, lim_(n → ∞) A.μ f n {u | max_min_dist u > ε} = 0`. -/
noncomputable def sample_whole_space (A : Algorithm α β) (f : α → β) : Prop :=
  ∀ ε > 0, Tendsto (fun n => A.μ f n {u | max_min_dist u > ε}) atTop (𝓝 0)

open unitInterval
