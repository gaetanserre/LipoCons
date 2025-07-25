/-
 - Created in 2025 by Gaëtan Serré
-/

import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.exampleProject "src/"

set_option verso.exampleModule "LipoCons.Verso.LipoCons_Verso"

#doc (Manual) "Consistency equivalence" =>

```anchor sample_iff_consistent
theorem sample_iff_consistent' (A : Algorithm α ℝ) :
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → sample_whole_space A hf.continuous)
    ↔
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → is_consistent_over_Lipschitz A hf) := by
```
