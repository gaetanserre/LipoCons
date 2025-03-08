import Mathlib.MeasureTheory.Measure.Typeclasses

open MeasureTheory
/--
Une manière de définir un algorithme itératif serait de le représenter comme
une mesure de probabilité sur les suites dans `Ω` : `ν : Measure (ℕ → Ω)`.
Cette mesure représente la distribution des suites d'itérations produites par
l'algorithme en temps infini. Cette définition permet aussi étudier les séquences
d'itérations finies : pour tout entier `n` et tout prédicat `P : (Fin n → Ω) → Prop`,
on peut mesurer l'ensemble d'itérations de taille `n` qui vérifie `P` :
`ν {u : ℕ → Ω | P (u[1:n])}`. Cette mesure `ν` peut cependant s'avérer difficile à
définir. En effet, il est nécessaire de connaître la distribution des limites des
séquences d'itérations de l'algorithme. Une manière plus simple de définir un
algorithme itératif serait de le représenter par une suite de mesures de probabilité
`μ : (n : ℕ) → Measure (Fin n → Ω)`. Pour tout entier `n`, la mesure `μ n` agit sur
l'espace des séquences de longueur `n` et représente la distribution des `n` premières
itérations de l'algorithme. Il est très simple de définir `μ` à partir de `ν` :
`μ = λ n (s : Set (Fin n → Ω)) ↦ ν {u : ℕ → Ω | u[1:n] ∈ s}`. À partir de cette
définition, il est trivial de montrer que
`μ n {u : Fin n → Ω | P u} = ν {u : ℕ → Ω | P (u[1:n])}`,
ce qui implique
`lim_(n → ∞) μ n {u : Fin n → Ω | P u} = lim_(n → ∞) ν {u : ℕ → Ω | P (u[1:n])}`
(voir `equiv_convergence`).
Ainsi, `f g : (n : ℕ) → Fin n → Ω` converge en mesure (par rapport à `ν`)
l'une vers l'autre si et seulement si
`∀ ε > 0, lim_(n → ∞) μ n {u : Fin n → Ω | |f n u - g n u| > ε} = 0`.
L'inconvénient de cette définition est que l'objet `μ ∞ = ν` n'est pas
directement accessible : pour un prédicat `P` sur les suites, il sera nécessaire
de construire un prédicat `P'` sur les séquences tel que
`lim_(n → ∞) μ n {u : Fin n → Omega | P' u} = ν {u : ℕ → Ω | P u}`.
Cependant, dans la plupart des analyses de convergence d'algorithmes itératifs,
seul la convergence de mesure de prédicats sur les séquences d'itérations est
étudiée. Ainsi, nous utiliserons la suite de mesures `μ (n : ℕ) → Measure (Fin n → Ω)`
pour représenter un algorithme itératif.
-/
structure Algorithm {α β : Type*} [MeasurableSpace α] [LinearOrder β] (f : α → β) where
  μ : (n : ℕ) → Measure (Fin n → α)
  μ_prob : (n : ℕ) → IsProbabilityMeasure (μ n)
