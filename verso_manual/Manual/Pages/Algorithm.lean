/-
 - Created in 2025 by Gaëtan Serré
-/

import Manual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.exampleProject "src/"

set_option verso.exampleModule "LipoCons.Defs.Algorithm"

#doc (Manual) "Stochastic iterative algorithm" =>
%%%
htmlSplit := .default
%%%

To formalize the Proposition 3 of {citep Malherbe2017}[], we need to abstract the notion of a stochastic iterative global optimization algorithm. Some proofs are not included in this manual for readability purposes, but they can be found in the source code of the project.

# Definition
A stochastic iterative global optimization algorithm can be seen as a stochastic process that iteratively samples from a search space, producing a sequence of samples. The first sample is drawn from a probability measure inherent to the algorithm, and subsequent samples are generated based on Markov kernels that depend on the previous samples and their associated evaluations by a continuous function. We define the following structure to represent such an algorithm.

```anchor Algorithm
structure Algorithm (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  prob_measure : IsProbabilityMeasure ν
  kernel_iter (n : ℕ) : Kernel (prod_iter_image α β n) α
  markov_kernel (n : ℕ) : IsMarkovKernel (kernel_iter n)
```
The type {anchorTerm Algorithm}`prod_iter_image` is the product type `(Fin (n + 1) → α) × (Fin (n + 1) → β)` which represents the sequence of samples and their evaluations at each iteration. The measure {anchorTerm Algorithm}`ν` is the initial probability measure from which the first sample is drawn, and {anchorTerm Algorithm}`kernel_iter` is the Markov kernel that defines how to sample the next element based on the previous ones.

*To assess the validity of this definition, we encompass three well-known algorithms in the literature into this framework.*

## Pure Random Search
The Pure Random Search algorithm is a simple stochastic iterative global optimization algorithm that samples uniformly from the search space at each iteration. It can be defined as follows:
- {anchorTerm Algorithm}`ν` := $`\mathcal{U}(\alpha)` is the uniform measure on the search space $`\alpha`.

- {anchorTerm Algorithm}`kernel_iter n` `:=` $`\_ \mapsto \mathcal{U}(\alpha)` is the Markov kernel that maps any pair of samples/evaluations to the uniform measure on $`\alpha`.

## AdaLIPO
The AdaLIPO algorithm has been introduced in {citep Malherbe2017}[] and is a more sophisticated stochastic iterative global optimization algorithm made for Lipschitz functions. It uses a estimation of the Lipschitz constant to adaptively sample the search space. The algorithm can be defined as follows:
- {anchorTerm Algorithm}`ν` := $`\mathcal{U}(\alpha)` is the uniform measure on the search space $`\alpha`.

- {anchorTerm Algorithm}`kernel_iter n` `:=` $`(X, f(X)) \mapsto \mathcal{U}(E(X, f(X)))` is the Markov kernel that maps any pair of samples/evaluations to the uniform measure on the set $`E(X, f(X))` defined as
  $$`
  E(X, f(X)) := \{x : \alpha \; | \; \max_{1 \le i \le n} f(X_i) \le \min_{1 \le i \le n} f(X_i) + \kappa(X, f(X)) \cdot d(x, X_i)\}
  `
  where $`(X, f(X)) \triangleq \left[(X_1, \dots, X_n), (f(X_1), \dots, f(X_n))\right]` and $`\kappa(X, f(X))` is an estimation of the Lipschitz constant of the function $`f` based on the previous samples and their evaluations.

### CMA-ES
The CMA-ES (Covariance Matrix Adaptation Evolution Strategy) is a popular stochastic iterative global introduced in {citep Hansen1996}[]. It samples from a multivariate normal distribution whose mean and covariance matrix is adapted based on the previous samples. The algorithm can be defined as follows:
- {anchorTerm Algorithm}`ν` := $`\mathcal{N}(\mu, \Sigma)` is the multivariate normal measure on the search space $`\alpha` with mean $`\mu` and covariance matrix $`\Sigma`.

- {anchorTerm Algorithm}`kernel_iter n` `:=` $`(X, f(X)) \mapsto \mathcal{N}(\mu(X, f(X)), \Sigma(X, f(X)))` is the Markov kernel that maps any pair of samples/evaluations to the multivariate normal distribution with mean $`\mu(X, f(X))` and covariance matrix $`\Sigma(X, f(X))` adapted based on the previous samples and their evaluations.

# Measure on sequences
To use the definition of consistency of a stochastic iterative global optimization algorithm, we need to use the initial probability measure and the Markov kernels of an algorithm to define a probability measure on sequences of samples produced. This measure is defined as a finite composition of the initial measure and the Markov kernels, i.e.:
$$`
\mathbb{P}(X_1, \dots, X_n) := \nu(X_1) \otimes \kappa_1(X_1, f(X_1)) \otimes \dots \otimes \kappa_{n-1}(X_1, \dots X_{n - 1}, f(X_1), \dots, f(X_{n-1})),
`
where $`\kappa_i` is {anchorTerm Algorithm}`kernel_iter` `i` (see {citep Kallenberg2021}[] for more details on decomposition of product measures using Markov kernels).

To be able to compose a {anchorTerm Algorithm}`Measure α` with a {anchorTerm Algorithm}`Kernel (prod_iter_image α β n) α`, we need to pullback the kernel along a function that, given a sequence of samples `u` and a continuous function `f`, returns `(u, f ∘ u)`. This new kernel is defined using {anchorTerm iter_comap}`iter_comap`.

```anchor iter_comap
def iter_comap {f : α → β} (hf : Continuous f) {n : ℕ} :
  Kernel (iter α n) α :=
  (A.kernel_iter n).comap
    (prod_eval n f)
    (measurable_prod_eval n hf.measurable)
```

It allows to define a measure on sequences of size $`n + 1` given a measure on sequences of size $`n` and a continuous function $`f`. This corresponds to one step of the stochastic iterative global optimization algorithm. This new measure is defined using the composition between the measure (noted $`\mu`) on the previous sequences of size $`n` and the kernel that maps a sequence to the next sample (noted $`\kappa`):
$$`
(\mu \otimes \kappa) A = \int_{u} \int_{x} \mathbf{1}_A (u_1, \dots, u_n, x) \, \mathrm{d} \kappa(u, x) \, \mathrm{d} \mu(u).
`

```anchor next_measure_def
noncomputable def next_measure {f : α → β} (hf : Continuous f) {n : ℕ} (μ : Measure (iter α n)) :
    Measure (iter α (n + 1)) := by
  refine Measure.ofMeasurable
    (fun s hs => ∫⁻ u, (∫⁻ x, s.indicator 1 (append u x) ∂ A.iter_comap hf u) ∂ μ) ?_ ?_
```

Finally, we can define the measure on sequences of samples of size `n` (noted $`\mu_n`) as a recursive composition of the initial measure and the Markov kernels:
$$`
\mu_n \triangleq \begin{cases}
  \nu & n = 0 \\
  \mu_{n - 1} \otimes \kappa_{n - 1} & n > 0
\end{cases},
`
where $`\kappa_{n - 1}` is the pullback of the Markov kernel {anchorTerm Algorithm}`kernel_iter` `n - 1` along the function that maps a sequence of samples to itself and their evaluations (see {anchorTerm iter_comap}`iter_comap`).
```anchor measure
noncomputable def measure {f : α → β} (hf : Continuous f) (n : ℕ) : Measure (iter α n) :=
  if h : n = 0 then
    Measure.pi (fun _ => A.ν)
  else by
    rw [←Nat.succ_pred_eq_of_ne_zero h]
    exact A.next_measure hf (measure hf (n - 1))
```

Because {anchorTerm Algorithm}`ν` is a probability measure, and all kernels {anchorTerm Algorithm}`kernel_iter` are Markov kernels, {anchorTerm measure}`measure` is a also probability measure on sequences of samples.
```anchor measure_isProbability
instance {n : ℕ} {f : α → β} {hf : Continuous f} : IsProbabilityMeasure (A.measure hf n) := by
```

# Useful lemmas
This definition of a stochastic iterative global optimization algorithm allows to prove two lemmas on the measure on sequences of samples. These lemmas happen to be useful in our formalization.

## Monotone
The first lemma states that, given two natural integers such that $`n \le m`, a measurable set $`S` of sequences of size $`n`, and a set $`E` of sequences of size $`m`, if the subsequences of size $`n` in $`E` are contained in $`S`, then the measure of $`E` is less than or equal to the measure of $`S`.

The informal intuition behind this lemma is that a sequence of size $`m` can be seen as a "continuation" of a sequence of size $`n`. Thus, the hypothesis that the subsequences of size $`n` in $`E` are contained in $`S` means that $`E` is a subset of all possible continuations of sequences in $`S`. Therefore, the measure of $`E` is less than or equal to the measure of $`S`.
```anchor mono
lemma mono {n m : ℕ} {s : Set (iter α n)} (hs : MeasurableSet s) {e : Set (iter α m)} (hmn : n ≤ m)
    (hse : e ⊆ {u | subTuple hmn u ∈ s}) {f : α → β} (hf : Continuous f) :
    A.measure hf m e ≤ A.measure hf n s := by
```
## Restricted measures
The second lemma states that, given two continuous functions $`f` and $`g` and a measurable set $`S` of elements of the search space $`\alpha` such that $`f` and $`g` are equal on $`S`, the measure on sequences produced by the algorithm using $`f` restricted to the set of sequences where all elements are in $`S` is equal to the same restricted measure using $`g`.

This is natural as the measures on sequences are entirely determined by the evaluations of the function on the samples.
```anchor eq_restrict
lemma eq_restrict {f g : α → β} (hf : Continuous f) (hg : Continuous g) {s : Set α}
    (hs : MeasurableSet s) (h : s.restrict f = s.restrict g) (n : ℕ) :
    (A.measure hf n).restrict (univ.pi (fun _ => s)) =
    (A.measure hg n).restrict (univ.pi (fun _ => s)) := by
```
