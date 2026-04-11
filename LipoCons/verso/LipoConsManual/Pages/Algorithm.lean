/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanGO.Algorithm
import LipoConsManual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

#doc (Manual) "Stochastic iterative algorithm" =>
%%%
htmlSplit := .never
%%%

To formalize the Proposition 3 of {citep Malherbe2017}[], we need to abstract the notion of a stochastic iterative global optimization algorithm. The full documentation of this framework can be found [here](https://gaetanserre.fr/LeanGO). We give here a brief overview of the definition of a stochastic iterative global optimization algorithm.

# Definition
A stochastic iterative global optimization algorithm can be seen as a stochastic process that iteratively samples from a search space, producing a sequence of samples. The first sample is drawn from a probability measure inherent to the algorithm, and subsequent samples are generated based on Markov kernels that depend on the previous samples and their associated evaluations by a measurable function. We define the following structure to represent such an algorithm.

{docstring Algorithm}

The type {name prod_iter_image}`prod_iter_image` is the product type `(Iic n → α) × (Iic n → β)` which represents the sequence of samples and their evaluations at each iteration. The measure {name Algorithm.ν}`ν` is the initial probability measure from which the first sample is drawn, and {name Algorithm.kernel_iter}`kernel_iter` is the Markov kernel that defines how to sample the next element based on the previous ones.
