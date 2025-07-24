/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/--
`iter α n` is the type of finite sequences of elements in `α` of length `n + 1`.

It represents the history of `n + 1` steps in an iterative process,
with entries indexed by `Fin (n + 1)` (i.e., from `0` to `n`).

Used in the context of stochastic iterative algorithms to store past evaluations or points.
-/
abbrev iter (α : Type*) (n : ℕ) := Fin (n + 1) → α

/--
`prod_iter_image α β n` is the input space of the algorithm at iteration `n`.

It consists of:
- a sequence of `n + 1` past points in `α`,
- and their corresponding evaluations in `β`.

This pair encodes the full information available up to iteration `n`.
-/
abbrev prod_iter_image (α β : Type*) (n : ℕ) := (iter α n) × (iter β n)

/--
`iter_mequiv α n` is a measurable equivalence between `iter α (n + 1)` and `α × iter α n`.

This equivalence decomposes a sequence of length `n + 2` (indexed by `Fin (n + 2)`)
into its last element and the remaining sequence of length `n + 1`.

Specifically, it maps a function `f : Fin (n + 2) → α` to the pair `(f (Fin.last (n + 1)), g)`
where `g : Fin (n + 1) → α` is defined by `g i = f (Fin.castSucc i)`.

This is useful for inductive constructions on iterative sequences, allowing to separate
the "current" step from the "history" of previous steps.
-/
def iter_mequiv (α : Type*) [MeasurableSpace α] (n : ℕ) : iter α (n + 1) ≃ᵐ α × iter α n :=
  MeasurableEquiv.piFinSuccAbove (fun _ => α) (Fin.last (n + 1))
