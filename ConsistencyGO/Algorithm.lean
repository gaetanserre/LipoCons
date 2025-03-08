import Mathlib
import ConsistencyGO.Tuple

open MeasureTheory Tuple

structure Algorithm {Ω : Set ℝ} (f : Ω → ℝ) where
  /--
  Un algorithme peut être représenté comme une mesure de probabilité `μ` sur les suites
  infinies. Lorsque l'on veut mesurer un prédicat `P` sur des séquences de taille `n`,
  il suffit de mesurer les suites infinies telles que les `n` premiers éléments vérifient
  `P`. De manière équivalente, on pourrait définir un algorithme comme une suite de mesure
  `ν : (n : ℕ) → Measure (Fin n → Ω)` afin que `ν n` mesure seulement des ensembles
  de séquences de taille `n`. On aurait alors que "`ν n s = μ {u | u[1:n] ∈ s}`".
  -/
  μ : Measure (ℕ → Ω)
  μ_prob : IsProbabilityMeasure μ
  g : (n : ℕ) → (0 < n) → (ℕ → Ω) → ℝ := fun n h u => by
    have := Fin.pos_iff_nonempty.mp h
    exact max (image (toTuple u n) f)

variable {Ω : Set ℝ} (f : Ω → ℝ) (A : Algorithm f)

def ff (n : ℕ) (s : Set (Fin n → Ω)) := {u : ℕ → Ω | toTuple u n ∈ s}
