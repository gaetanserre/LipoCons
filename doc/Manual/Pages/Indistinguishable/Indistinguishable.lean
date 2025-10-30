/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LipoCons.Defs.Indistinguishable"

#doc (Manual) "Indistinguishable function" =>
%%%
htmlSplit := .never
%%%

Given a Lipschitz function $`f` on a compact domain $`\alpha`, a positive real number $`\varepsilon`, and an element of $`\alpha` $`c`, we construct a new Lipschitz function $`\tilde{f}` such that $`f = \tilde{f}` outside of the ball centered at $`c` with radius $`\varepsilon/2`, and such that the maximum value of $`\tilde{f}` is inside this ball and is strictly greater than the maximum value of $`f`.

# Expression
We define the function $`\tilde{f}` as follows:
$$`
\tilde{f}(x) \triangleq \begin{cases}
  f (x) + 2 \cdot \left(1 - \frac{\|x - c\|}{\varepsilon / 2} \right) \cdot (\max_{x \in \alpha} f(x) - \min_{x \in \alpha} f(x) + 1) & \text{if } x \in B(c, \varepsilon / 2) \\
  f (x) & \text{otherwise}
\end{cases}
`

Here is a visualization of this expression using the reverse [Ackley function](https://www.sfu.ca/~ssurjano/ackley.html).

![](static/ackley_tilde.png)

```anchor f_tilde
noncomputable def f_tilde (ε : ℝ) (x : α) :=
  if x ∈ ball c (ε/2) then
    f x + 2 * ((1 - (dist x c) / (ε/2)) * (fmax hf - fmin hf + 1))
  else f x
```

# Lipschitz property
We show that $`\tilde{f}` is Lipschitz continuous. The proof relies on the fact that $`\tilde{f}` is a cases function of two Lipschitz functions that are equal on the frontier of the ball $`B(c, \varepsilon / 2)`.
```anchor f_tilde_lipschitz
lemma f_tilde_lipschitz {ε : ℝ} (ε_pos : 0 < ε) : Lipschitz (hf.f_tilde c ε) := by
  refine hf.if ?_ ?_
  · intro a ha
    rw [ha]
    suffices h : ε / 2 / (ε / 2) = 1 by
      rw [h]
      ring
    exact CommGroupWithZero.mul_inv_cancel _ ((ne_of_lt (half_pos ε_pos)).symm)
  · refine const_mul <| mul_const <| sub lipschitz_const ?_
    exact div_const (dist_left c)
```

# Maximum of $`\tilde{f}`
One can show that $`\tilde{f}(c)` is strictly greater than the maximum of $`f` (see {anchorTerm max_f_lt_max_f_tilde}`max_f_lt_f_tilde_c`). Hence, by transitivity, the maximum of $`\tilde{f}` is strictly greater than the maximum of $`f`.
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
