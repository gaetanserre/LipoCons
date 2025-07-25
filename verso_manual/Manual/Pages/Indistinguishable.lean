/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.exampleProject "src/"

set_option verso.exampleModule "LipoCons.Utils.Indistinguishable"

#doc (Manual) "Indistinguishable function" =>

```anchor f_tilde
noncomputable def f_tilde (ε : ℝ) := fun x =>
  if x ∈ Metric.ball c (ε/2) then
    f x + 2 * ((1 - (dist x c) / (ε/2)) * (fmax hf - fmin hf + 1))
  else f x
```

```anchor f_tilde_lipschitz
lemma f_tilde_lipschitz {ε : ℝ} (ε_pos : 0 < ε) : Lipschitz (hf.f_tilde c ε) := by
  let g := fun a => 2 * ((1 - (dist a c) / (ε/2)) * (fmax hf - fmin hf + 1))
  have hg : Lipschitz g := by
    refine const_mul ?_
    refine mul_const ?_
    refine sub lipschitz_const ?_
    exact div_const (dist_left c)
  refine hf.if ?_ hg
  intro a ha
  rw [ha]
  suffices h : ε / 2 / (ε / 2) = 1 by
    rw [h]
    ring
  exact CommGroupWithZero.mul_inv_cancel _ ((ne_of_lt (half_pos ε_pos)).symm)
```

```anchor max_f_lt_max_f_tilde
lemma max_f_lt_max_f_tilde {ε : ℝ} (ε_pos : 0 < ε) :
    fmax hf < fmax (hf.f_tilde_lipschitz c ε_pos) :=
  suffices h : fmax hf < hf.f_tilde c ε c from
    lt_of_le_of_lt' (compact_argmax_apply (hf.f_tilde_lipschitz c ε_pos).continuous c) h
  hf.max_f_lt_f_tilde_c c ε_pos
```
