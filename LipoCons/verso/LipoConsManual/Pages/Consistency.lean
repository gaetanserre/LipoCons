/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LipoCons.Defs.Consistency
import LipoConsManual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "."

set_option verso.exampleModule "LipoCons.Defs.Consistency"

#doc (Manual) "Consistency and sampling" =>
%%%
htmlSplit := .never
%%%

In {citep Malherbe2017}[], the authors provided definitions for the consistency of a stochastic iterative global optimization algorithm and for the fact that an algorithm samples the whole search space.

# Consistency of algorithms

In the paper, the consistency of an algorithm is defined using convergence in probability. A stochastic iterative global optimization algorithm is sait to be consistent over $`f` if the maximum of the evaluations of the samples produced by the algorithm converges in probability to the maximum of $`f` over the search space, i.e.
$$`
\max_{0 \le i \le n} f(X_i) \xrightarrow{p} \max_{x \in \mathcal{X}} f(x),
`
where $`X_i` is the $`i`-th sample produced by the algorithm. Note that we consider here the case where an algorithm searches to maximize a function, but the definition can be adapted to the case of minimization.

The latter definition can be unfolded as follows:
$$`
\forall \varepsilon > 0, \; \mathbb{P}(|\max_{0 \le i \le n} f(X_i) - \max_{x \in \mathcal{X}} f(x)| > \varepsilon) \xrightarrow[n \to \infty]{} 0,
`
where $`\mathbb{P}` denotes the probability measure on sequences of samples of size $`n + 1` produced by the algorithm. In our formalization, we showed that $`\mathbb{P}` is equal to {name Algorithm.fin_measure}`Algorithm.fin_measure`.

To formally define the consistency using {name Algorithm.fin_measure}`Algorithm.fin_measure`, we define the set of sequences of samples of size $`n + 1` such that the maximum of the evaluations is at least $`\varepsilon` away from the maximum of $`f` over the compact search space (noted {name fmax}`fmax`).
```anchor set_dist_max
def set_dist_max {f : α → β} (hf : Lipschitz f) {n : ℕ} (ε : ℝ) :=
  {u : iter α n | dist (Tuple.max (f ∘ u)) (fmax hf) > ε}
```

We can now define the measure of this set of sequences.
```anchor measure_dist_max
noncomputable def measure_dist_max (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) :=
  fun ε n => A.fin_measure hf.measurable (set_dist_max hf (n := n) ε)
```

Finally, an algorithm $`A` is consistent over a Lipschitz function $`f` if {name measure_dist_max}`measure_dist_max` tends to $`0` when $`n` tends to infinity.
```anchor is_consistent
def is_consistent (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) :=
  ∀ ⦃ε⦄, 0 < ε → Tendsto (measure_dist_max A hf ε) atTop (𝓝 0)
```

# Sampling whole space

In the original paper, the authors also defined the fact that, given a function, an algorithm samples the whole search space. An algorithm is said to sample the whole search space, given $`f`, if the supremum of the minimum distance between the samples and a point in the search space tends to $`0` in probability, i.e.
$$`
\sup_{x \in \mathcal{X}} \min_{0 \le i \le n} \| x - X_i\| \xrightarrow{p} 0,
`
where $`\| \cdot \|` denotes a norm on the search space (usually the Euclidean norm), and $`X_i` is the $`i`-th sample produced by the algorithm given $`f`.

This definition can be unfolded as follows:
$$`
\forall \varepsilon > 0, \; \mathbb{P}(\sup_{x \in \mathcal{X}} \min_{0 \le i \le n} \| x - X_i\| > \varepsilon) \xrightarrow[n \to \infty]{} 0,
`
where $`\mathbb{P}` is equal to {name Algorithm.fin_measure}`Algorithm.fin_measure`.

To formalize this definition, we define the minimum distance between a point in the search space and a sequence of samples.
```anchor min_dist_x
noncomputable def min_dist_x :=
  fun {n : ℕ} (u : iter α n) (x : α) => Tuple.min ((fun xi => dist xi x) ∘ u)
```

As {name min_dist_x}`min_dist_x` is a continuous function, we can define the maximum of this function over the compact search space. Hence, the $`\sup` in the above definition can be replaced by a $`\max` over the search space.
```anchor max_min_dist
noncomputable def max_min_dist {n : ℕ} (u : iter α n) :=
  min_dist_x u (compact_argmax (min_dist_x_continuous u))
```

Finally, given a continuous function $`f`, an algorithm $`A` samples the whole search space if the measure of the set of sequences of samples of size $`n + 1` such that, {name max_min_dist}`max_min_dist` is greater than $`\varepsilon`, tends to $`0` when $`n` tends to infinity.
```anchor sample_whole_space
noncomputable def sample_whole_space (A : Algorithm α β) {f : α → β} (hf : Continuous f) :=
  ∀ ε > 0, Tendsto (fun n =>
    A.fin_measure hf.measurable {u : iter α n | max_min_dist u > ε}) atTop (𝓝 0)
```

Now, we have all the definitions needed to formalize the Proposition 3 of {citep Malherbe2017}[].
