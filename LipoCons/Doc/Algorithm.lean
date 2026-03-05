/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Utils.Kernel
import LeanGO.Utils.Measure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open MeasureTheory ProbabilityTheory

/-- `Algorithm α β` represents a general iterative stochastic optimization algorithm.

It models a sequence of updates where:
- `α` is the search space (e.g., parameters, candidate solutions),
- `β` is the evaluation space (e.g., objective values, feedback),
- `ν` is the initial probability measure over `α` (the starting distribution of candidates),
- `kernel_iter n` is a Markov kernel that outputs a new candidate in `α`
  given the history of the first `n` points and their evaluations,
  i.e., from the space `prod_iter_image α β n` = (`α × β`)ⁿ,
- `markov_kernel n` asserts that each such `kernel_iter n` is a valid Markov kernel.

It allows formal reasoning over joint distributions of evaluated points and convergence
properties. -/
-- ANCHOR: Algorithm
structure Algorithm (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  prob_measure : IsProbabilityMeasure ν
  kernel_iter (n : ℕ) : Kernel (prod_iter_image α β n) α
  markov_kernel (n : ℕ) : IsMarkovKernel (kernel_iter n)
-- ANCHOR_END: Algorithm
