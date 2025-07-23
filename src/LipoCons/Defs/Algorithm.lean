/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.Tuple
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.CompletePartialOrder

open MeasureTheory Tuple

/-! One way to define an iterative algorithm applied to a function is to represent it as a probability measure over sequences in `Ω`: `ν : Measure (ℕ → Ω)`.

This measure represents the distribution of the iteration sequences produced by the algorithm in infinite time. This definition also allows us to study finite iteration sequences: for any integer `n` and any predicate `P : (Fin n → Ω) → Prop`, we can measure the set of iterations of size `n` that satisfy `P`: `ν {u : ℕ → Ω | P (u[1:n])}`.

However, this measure `ν` may be difficult to define. Indeed, it is necessary to know the distribution of the limits of the iteration sequences of the algorithm.

A simpler way to define an iterative algorithm is to represent it by a sequence of probability measures `μ : (n : ℕ) → Measure (Fin n → Ω)`. For any integer `n`, the measure `μ n` acts on the space of sequences of length `n` and represents the distribution of the first `n` iterations of the algorithm.

It is very simple to define `μ` from `ν`:
`μ = λ n (s : Set (Fin n → Ω)) ↦ ν {u : ℕ → Ω | u[1:n] ∈ s}`.
From this definition, it is trivial to show that
`μ n {u : Fin n → Ω | P u} = ν {u : ℕ → Ω | P (u[1:n])}`,
which implies
`lim_(n → ∞) μ n {u : Fin n → Ω | P u} = lim_(n → ∞) ν {u : ℕ → Ω | P (u[1:n])}`

Thus, `f g : (n : ℕ) → Fin n → Ω` converge in measure (with respect to `ν`) to one another if and only if
`∀ ε > 0, lim_(n → ∞) μ n {u : Fin n → Ω | |f n u - g n u| > ε} = 0`.

The drawback of this definition is that the object `μ ∞ = ν` is not directly accessible: for a predicate `P` on sequences, it will be necessary to construct a predicate `P'` on finite sequences such that
`lim_(n → ∞) μ n {u : Fin n → Ω | P' u} = ν {u : ℕ → Ω | P u}`.

However, in most convergence analyses of iterative algorithms, only the convergence in measure of predicates on iteration sequences is studied. Thus, we will use the sequence of measures `μ (n : ℕ) → Measure (Fin n → Ω)` to represent an iterative algorithm. -/
structure Algorithm (α β : Type*) [MeasurableSpace α] where
  μ : (α → β) → (n : ℕ) → Measure (Fin n → α)

  private μ_prob f n : IsProbabilityMeasure (μ f n)

  /-- Equivalent to `∀ n ≤ m, μ f n A = μ f m {u | u[1:n] ∈ A}` -/
  μ_mono f : ∀ ⦃n m A B⦄, MeasurableSet B → n ≤ m → {u | toTuple m u ∈ A} ⊆ {u | toTuple n u ∈ B} → μ f m A ≤ μ f n B

  /-- If two functions are indistinguishable on a set `s`, then the probability
  that no iteration lies in `sᶜ` is the same for both functions.

  Indeed, since the algorithm only has access to function evaluations,
  the distribution of the i-th point in the iteration sequence depends
  on the previous points.

  Now, if none of these points are in `sᶜ` and `f = g` on `s`, then the
  distribution of the i-th point is the same for both functions.

  Thus, the distribution of iteration sequences that contain no point in `sᶜ`
  is the same for both functions.

  However, the distribution of iteration sequences that contain one or more points
  may differ (e.g., if `g` is minimized on `sᶜ`). -/
  μ_eq_restrict : ∀ ⦃f g : α → β⦄, ∀ ⦃s : Set α⦄, (∀ a ∈ s, f a = g a) → ∀ n,
      μ f n {u | ∀ i, u i ∉ sᶜ} = μ g n {u | ∀ i, u i ∉ sᶜ}

namespace Algorithm

variable {α β : Type*} [MeasurableSpace α] (A : Algorithm α β)

instance {f : α → β} {n : ℕ} : IsProbabilityMeasure (A.μ f n) := A.μ_prob f n

end Algorithm
