/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LipoCons.Defs.Indistinguishable
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option linter.dupNamespace false
set_option pp.rawOnError true

set_option verso.exampleProject "."

set_option verso.exampleModule "LipoCons.Defs.Indistinguishable"

#doc (Manual) "Indistinguishable function" =>
%%%
htmlSplit := .never
%%%

Given a Lipschitz function $`f` on a compact (pseudo)metric space $`\alpha`, a positive real number $`\varepsilon`, and an element of $`\alpha` $`c`, we construct a new Lipschitz function $`\tilde{f}` such that $`f = \tilde{f}` outside of the ball centered at $`c` with radius $`\varepsilon/2`, and such that the maximum value of $`\tilde{f}` is inside this ball and is strictly greater than the maximum value of $`f`.

# Expression
We define the function $`\tilde{f}` as follows:
$$`
\tilde{f}(x) \triangleq \begin{cases}
  f (x) + 2 \cdot \left(1 - \frac{d(x, c)}{\varepsilon / 2} \right) \cdot (\max_{x \in \alpha} f(x) - \min_{x \in \alpha} f(x) + 1) & \text{if } x \in B(c, \varepsilon / 2) \\
  f (x) & \text{otherwise}
\end{cases}
`

Here is a visualization of this expression using the reverse [Ackley function](https://www.sfu.ca/~ssurjano/ackley.html).

![](static/ackley_tilde.png)

{docstring Lipschitz.f_tilde}

```anchor f_tilde
noncomputable def f_tilde (ε : ℝ) (x : α) :=
  if x ∈ ball c (ε/2) then
    f x + 2 * ((1 - (dist x c) / (ε/2)) * (fmax hf - fmin hf + 1))
  else f x
```

# Lipschitz property
We show that $`\tilde{f}` is Lipschitz continuous. Writing $`\tilde{f} = f + g` on $`B(c, \varepsilon / 2)` and $`\tilde{f} = f` elsewhere, the Lipschitz function $`g` is nonnegative inside the ball and nonpositive outside of it. Hence $`\tilde{f} = f + \max(g, 0)`, which is Lipschitz as a sum of Lipschitz functions (see {name LipschitzWith.if}`LipschitzWith.if`). This argument only uses the metric structure of $`\alpha`: no vector space structure is required.
```anchor f_tilde_lipschitz
lemma f_tilde_lipschitz {ε : ℝ} (ε_pos : 0 < ε) : Lipschitz (hf.f_tilde c ε) := by
  have hK : 0 ≤ fmax hf - fmin hf + 1 := by
    have : 0 ≤ fmax hf - fmin hf := compact_argmax_sub_argmin_pos hf.continuous
    linarith
  refine hf.if ?_ ?_ ?_
  · intro a ha
    have : dist a c / (ε / 2) < 1 := (div_lt_one (half_pos ε_pos)).mpr (mem_ball.mp ha)
    have : 0 ≤ (1 - dist a c / (ε / 2)) * (fmax hf - fmin hf + 1) := mul_nonneg (by linarith) hK
    linarith
  · intro a ha
    have : 1 ≤ dist a c / (ε / 2) :=
      (one_le_div (half_pos ε_pos)).mpr (not_lt.mp (mt mem_ball.mpr ha))
    have : (1 - dist a c / (ε / 2)) * (fmax hf - fmin hf + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hK
    linarith
  · refine const_mul <| mul_const <| sub lipschitz_const ?_
    exact div_const (dist_left c)
```

# Maximum of $`\tilde{f}`
One can show that $`\tilde{f}(c)` is strictly greater than the maximum of $`f` (see {name Lipschitz.max_f_lt_f_tilde_c}`max_f_lt_f_tilde_c`). Hence, by transitivity, the maximum of $`\tilde{f}` is strictly greater than the maximum of $`f`.
```anchor max_f_lt_max_f_tilde
lemma max_f_lt_max_f_tilde {ε : ℝ} (ε_pos : 0 < ε) :
    fmax hf < fmax (hf.f_tilde_lipschitz c ε_pos) :=
  suffices h : fmax hf < hf.f_tilde c ε c from
    lt_of_le_of_lt' (compact_argmax_apply (hf.f_tilde_lipschitz c ε_pos).continuous c) h
  hf.max_f_lt_f_tilde_c c ε_pos
```

Finally, we show that the maximum of $`\tilde{f}` is attained in the ball $`B(c, \varepsilon / 2)`.
```anchor max_f_tilde_in_ball
lemma max_f_tilde_in_ball {ε : ℝ} (ε_pos : 0 < ε) :
    compact_argmax (hf.f_tilde_lipschitz c ε_pos).continuous ∈ ball c (ε/2) := by
  set x' := compact_argmax (hf.f_tilde_lipschitz c ε_pos).continuous
  by_contra h_contra
  have : fmax (hf.f_tilde_lipschitz c ε_pos) ≤ fmax hf := by
    simp only [fmax, hf.f_tilde_apply_out c h_contra, x']
    exact compact_argmax_apply hf.continuous x'
  have := hf.max_f_lt_max_f_tilde c ε_pos
  linarith
```
