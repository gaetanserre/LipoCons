/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Algorithm
import ConsistencyGO.Compact
import ConsistencyGO.Tuple
import Mathlib

open Tuple NNReal Filter Topology

def CompactNe {α : Type*} [TopologicalSpace α] (A : Set α) : Prop := IsCompact A ∧ A.Nonempty

/-
We define two spaces `α` and `β` with topological properties and we define
a continuous function `f` over a compact set of `α`, `Ω`.
-/
variable {α β : Type*} [MetricSpace α] [MeasurableSpace α]
[Nonempty β] [Dist β] [LinearOrder β] [MetricSpace β]
[ClosedIciTopology β] [ClosedIicTopology β]
{Ω : Set α} [Nonempty Ω] [CompactSpace Ω]
{f : Ω → β} (cont : Continuous f)

/--
The maximum of `f` over `Ω`.
-/
noncomputable def fmax := f (compact_argmax cont)

/--
Given an algorithm `A`, the function that, given `ε` and `n`, returns
the measure of the set of sequences of size `n` such that the maximum of
`f` over these sequences is at least `ε` away from from `fmax`.
-/
def measure_dist_max (A : Algorithm Ω β) := fun ε n =>
  A.μ f n {u | dist (Tuple.max (f ∘ u)) (fmax cont) > ε}

/--
**Main definition**: we say that an algorithm `A` is consistent over `f`
if for any `ε > 0`, `lim_(n → ∞) measure_dist_max n = 0`.
-/
def isConsistent (A : Algorithm Ω β) : Prop :=
  ∀ ε > 0, Tendsto (measure_dist_max cont A ε) atTop (𝓝 0)


/--
The set of all Lipschitz functions.
-/
def all_lipschitz := {f : Ω → β | ∃ κ, LipschitzWith κ f}

/--
An algorithm `A` is consistent over all Lipschitz functions.
-/
def isConsistentOverLipschitz (A : Algorithm Ω β) {f : Ω → β} (hf : f ∈ all_lipschitz) : Prop :=
  isConsistent hf.choose_spec.continuous A

noncomputable def test :=
  fun {n : ℕ} (u : Fin n → Ω) (x : Ω) => Tuple.min ((fun xi => dist xi x) ∘ u)

variable {n : ℕ} (u : Fin n → Ω)

lemma tttt : Continuous (test u) := by
  by_cases h : n = 0
  · have : ¬ 0 < n := Eq.not_gt h
    rw [Fin.pos_iff_nonempty] at this

    let e : ℝ := instNonemptyOfInhabited.some

    suffices h : test u = fun x => e by rw [h]; exact continuous_const
    ext x
    unfold test Tuple.min Fintype.min_image Fintype.min_image'
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

  suffices h : test u = Finset.univ.inf' ne g by rwa [h]
  ext x
  unfold test Tuple.min Fintype.min_image Fintype.min_image'
  split
  · simp only [Function.comp_apply, Finset.inf'_apply, g]
  contradiction

#check test u (compact_argmax (tttt u))
example : ∀ y, test u y ≤ test u (compact_argmax (tttt u)) := by
  exact compact_argmax_apply (tttt u)

noncomputable def testt (A : Algorithm Ω β) (f : Ω → β) : Prop :=
  Tendsto (fun ε n => A.μ f n {u | test u (compact_argmax (tttt u)) > ε}) atTop (𝓝 0)
