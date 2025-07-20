/-
 - Created in 2025 by Gaëtan Serré
-/


import VersoBlog
open Verso Genre Blog


#doc (Page) "About" =>

On this page, you will find the Lean formalization of the Proposition 3 of [Global optimization of Lipschitz functions, Malherbe C. & Vayatis N., 2017](http://proceedings.mlr.press/v70/malherbe17a/malherbe17a.pdf). It states that, for any iterative stochastic global optimization algorithm $`A`, the following two statements are equivalent:
1. For any Lipschitz function $`f` defined on a compact domain $`\mathcal{X}`,
  $$`\max_{i = 1 \dots n} f(X_i) \xrightarrow{p} \max_{x \in \mathcal{X}} f(x).`
1. For any Lipschitz function $`f` defined on a compact domain $`\mathcal{X}`,
  $$`\sup_{x \in \mathcal{X}} \min_{i = 1 \dots n} f(X_i) \xrightarrow{p} 0.`


Here $`(X_i)_{1 \le i \le n}` are the samples  produced by the algorithm $`A` after $`n` iterations, and $`\xrightarrow{p}` denotes convergence in probability.

One can see that **(1)** is a popular definition of the consistency of an algorithm while **(2)** means that $`A` samples the whole domain $`\mathcal{X}`.

To see the main definitions used in the formalization, see
- [`Algorithm`](/Algorithm) for the definition of an iterative stochastic global optimization algorithm;
- [`isConsistentOverLipschitz`](/Consistency) for the definition of consistency over Lipschitz functions;
- [`sample_whole_space`](/Consistency) for the definition of sampling the whole space.

To directly see the statement of the theorem, see [Consistency $`\Leftrightarrow` Pure random search](/Theorem)
