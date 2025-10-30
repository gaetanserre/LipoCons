/-
 - Created in 2025 by Gaëtan Serré
-/

import Manual.Papers
import VersoManual

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

set_option pp.rawOnError true

set_option verso.exampleProject "../"

set_option verso.exampleModule "LipoCons.Verso.LipoCons_Verso"

#doc (Manual) "Consistency equivalence" =>

We prove the equivalence between {anchorTerm sample_iff_consistent}`sample_whole_space` and {anchorTerm sample_iff_consistent}`is_consistent` for any stochastic iterative global optimization {anchorTerm sample_iff_consistent}`Algorithm` $`A`. This corresponds to *Proposition 3* of the paper _*{citehere Malherbe2017}[]*_.

```anchor sample_iff_consistent
theorem sample_iff_consistent (A : Algorithm α ℝ) :
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → sample_whole_space A hf.continuous)
    ↔
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → is_consistent A hf) := by
```
The proof of the proposition is available in the ArXiv preprint of the original paper {citep Malherbe2017ArXiv}[]. We follow the same structure while adapting the proof to the Lean formalization. We also fixed a small mistake in the original proof, which was pointed out to the authors in a private discussion.

The modus ponens direction is easy to prove, as the continuity of $`f` implies that sequences of samples such that, the maximum of their evaluations under $`f` is at least $`\varepsilon`, do not belong to a ball centered on the maximum of $`f` with positive radius. The {anchorTerm sample_iff_consistent}`sample_whole_space` hypothesis implies that the set of such sequences has measure tending to $`0` as $`n` tends to infinity, which proves {anchorTerm sample_iff_consistent}`is_consistent`.

The converse direction is more involved. The proof is done by contradiction: if the algorithm does not sample the whole space for a given function $`f`, then there exists a ball such that the measure of the set of sequences of samples that do not belong to this ball does not tend to $`0` as $`n` tends to infinity. The idea is to construct a function $`\tilde{f}` that is indistinguishable from $`f` outside of this ball, such that the maximum of $`\tilde{f}` is strictly greater than the maximum of $`f` and such that the $`\arg \max` of $`\tilde{f}` is inside the ball. This contradicts the {anchorTerm sample_iff_consistent}`is_consistent` hypothesis, as the maximum of $`\tilde{f}` is almost never sampled by the algorithm.

Our construction of the function $`\tilde{f}` has a slightly simpler expression than the one in the original paper but provides the same properties. For more details, see [Indistinguishable function](/Indistinguishable-function).
