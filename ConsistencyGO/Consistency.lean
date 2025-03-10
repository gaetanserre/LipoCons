/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib
import ConsistencyGO.Algorithm
import ConsistencyGO.Compact
import ConsistencyGO.Tuple

open Tuple NNReal Filter Topology

def CompactNe {α : Type*} [TopologicalSpace α] (A : Set α) : Prop := IsCompact A ∧ A.Nonempty

/-
We define two spaces `α` and `β` with topological properties and we define
a Lipschitz function `f` over a compact set of `α`, `Ω`.
-/
variable {α β : Type*} [PseudoEMetricSpace α] [MeasurableSpace α]
[Nonempty β] [Dist β] [LinearOrder β] [PseudoEMetricSpace β]
[ClosedIciTopology β] [ClosedIicTopology β]
{Ω : Set α} (compact_ne : CompactNe Ω)
{f : Ω → β} {κ : ℝ≥0} (lipschitz : LipschitzWith κ f)

/--
The maximum of `f` over `Ω`.
-/
noncomputable def fmax := f (compact_ne.1.exists_argmax lipschitz.continuous compact_ne.2).choose

/--
Given an algorithm `A`, the function that, given `ε` and `n`, returns
the measure of the set of sequences of size `n` such that the maximum of
`f` over these sequences is at least `ε` away from from `fmax`.
-/
def measure_dist_max (A : Algorithm Ω β) := fun ε n =>
  A.μ f n {u | dist (Tuple.max (image u f)) (fmax compact_ne lipschitz) > ε}

/--
**Main definition**: we say that an algorithm `A` is consistent over `f`
if for any `ε > 0`, `lim_(n → ∞) measure_dist_max n = 0`.
-/
def isConsistent (A : Algorithm Ω β) : Prop :=
  ∀ ε > 0, Tendsto (measure_dist_max compact_ne lipschitz A ε) atTop (𝓝 0)
