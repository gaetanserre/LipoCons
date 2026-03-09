/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import Manual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LipoCons.Doc.Algorithm"

#doc (Manual) "Stochastic iterative algorithm" =>
%%%
htmlSplit := .never
%%%

To formalize the Proposition 3 of {citep Malherbe2017}[], we need to abstract the notion of a stochastic iterative global optimization algorithm. The full documentation of this framework can be found [here](https://gaetanserre.fr/LeanGO). We give here a brief overview of the definition of a stochastic iterative global optimization algorithm.

# Definition
A stochastic iterative global optimization algorithm can be seen as a stochastic process that iteratively samples from a search space, producing a sequence of samples. The first sample is drawn from a probability measure inherent to the algorithm, and subsequent samples are generated based on Markov kernels that depend on the previous samples and their associated evaluations by a measurable function. We define the following structure to represent such an algorithm.

```anchor Algorithm
structure Algorithm (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  [prob_measure : IsProbabilityMeasure ν]
  kernel_iter (n : ℕ) : Kernel (prod_iter_image α β n) α
  [markov_kernel (n : ℕ) : IsMarkovKernel (kernel_iter n)]
```
The type {anchorTerm Algorithm}`prod_iter_image` is the product type `(Iic n → α) × (Iic n → β)` which represents the sequence of samples and their evaluations at each iteration. The measure {anchorTerm Algorithm}`ν` is the initial probability measure from which the first sample is drawn, and {anchorTerm Algorithm}`kernel_iter` is the Markov kernel that defines how to sample the next element based on the previous ones.
