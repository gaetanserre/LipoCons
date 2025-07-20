/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
import DemoSite.Categories

open Lean.MessageSeverity

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "src"
set_option verso.exampleModule "LipoCons"

set_option pp.rawOnError true
set_option maxHeartbeats 0

#doc (Page) "Consistency ⇔ Pure random search" =>
Here, we prove that an iterative stochastic global optimization algorithm
is consistent over Lipschitz functions if and only if it, for any Lipschitz function,
it samples the whole space.
Please refer to
- [`Algorithm`](/Algorithm) for the definition of an algorithm;
- [`Lipschitz`](/Lipschitz) for the definition of Lipschitz functions.
- [`isConsistentOverLipschitz`](/Consistency) for the definition of consistency over Lipschitz functions;
- [`sample_whole_space`](/Consistency) for the definition of sampling the whole space.

```anchor thm_sample_iff_consistent
theorem sample_iff_consistent' (A : Algorithm α ℝ) :
    (∀ ⦃f : α → ℝ⦄, Lipschitz f → sample_whole_space A f)
    ↔
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → isConsistentOverLipschitz A hf) := by
  sorry
```
Because the proof is long, we do not include it here. Please refer to the file
[`LipoCons.lean`](https://github.com/gaetanserre/LipoCons/blob/main/src/LipoCons.lean).
