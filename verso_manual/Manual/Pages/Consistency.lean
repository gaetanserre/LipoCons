/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.exampleProject "src/"

set_option verso.exampleModule "LipoCons.Defs.Consistency"

#doc (Manual) "Consistency of algorithms" =>

```anchor is_consistent
def is_consistent (A : Algorithm α β) {f : α → β} (hf : Lipschitz f) : Prop :=
  ∀ ⦃ε⦄, 0 < ε → Tendsto (measure_dist_max A hf ε) atTop (𝓝 0)
```

```anchor min_dist_x
noncomputable def min_dist_x :=
  fun {n : ℕ} (u : iter α n) (x : α) => Tuple.min ((fun xi => dist xi x) ∘ u)
```

```anchor max_min_dist
noncomputable def max_min_dist {n : ℕ} (u : iter α n) :=
  min_dist_x u (compact_argmax (min_dist_x_continuous u))
```

```anchor sample_whole_space
noncomputable def sample_whole_space (A : Algorithm α β) {f : α → β} (hf : Continuous f) : Prop :=
  ∀ ε > 0, Tendsto (fun n => A.measure hf n {u | max_min_dist u > ε}) atTop (𝓝 0)
```
