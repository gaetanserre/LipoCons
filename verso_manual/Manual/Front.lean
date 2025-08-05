/-
 - Created in 2025 by Gaëtan Serré
-/

import Manual.Pages.Algorithm
import Manual.Pages.Consistency
import Manual.Pages.Indistinguishable.Indistinguishable
import Manual.Pages.LipoCons
import Manual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Consistency of global optimization algorithms" =>
%%%
authors := ["Gaëtan Serré"]
shortTitle := "Consistency of global optimization algorithms"
%%%

In 2017, the paper _*{citehere Malherbe2017}[]*_ introduced two global optimization algorithms consistent on any Lipschitz function, i.e, they converge to the global maximum of any Lipschitz function. To prove this result, the authors proved a proposition on meta-optimization, which state that, for any global optimization algorithm, being consistent on any Lipschitz function is equivalent to sample the whole search space.

![](static/ackley_contour.svg)

More formally, *Proposition 3* states that, for any stochastic iterative global optimization algorithm $`A`, the two following statements are equivalent:
1. For any Lipschitz function $`f` defined on $`\mathcal{X}`,
  $$`\sup_{x \in \mathcal{X}} \min_{i = 1 \dots n} f(X_i) \xrightarrow{p} 0.`
1. For any Lipschitz function $`f` defined on $`\mathcal{X}`,
  $$`\max_{i = 1 \dots n} f(X_i) \xrightarrow{p} \max_{x \in \mathcal{X}} f(x).`

Here $`\mathcal{X} \subset \mathbb{R}^d` is compact, $`(X_i)_{1 \le i \le n}` are the samples produced by the algorithm $`A` after $`n` iterations, and $`\xrightarrow{p}` denotes the convergence in probability.

One can see that *(2)* is a popular definition of the consistency of a stochastic iterative global optimization algorithm while *(1)* means that $`A` samples the whole domain $`\mathcal{X}`.

This manual is dedicated to the [`L∃∀N`](https://lean-lang.org/) formalization of this proposition.

{include 0 Manual.Pages.Algorithm}

{include 0 Manual.Pages.Consistency}

{include 0 Manual.Pages.LipoCons}

{include 0 Manual.Pages.Indistinguishable.Indistinguishable}
