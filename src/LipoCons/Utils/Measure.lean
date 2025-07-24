/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open Set

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]

lemma pi_space_eq
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ (pi univ s) = ν (pi univ s)) :
    μ = ν := by
  refine Measure.FiniteSpanningSetsIn.ext
    generateFrom_pi.symm (IsPiSystem.pi (fun _ => MeasurableSpace.isPiSystem_measurableSet)) ?_ ?_
  · refine { set := fun _ => univ, set_mem := ?_, finite := ?_, spanning := ?_ }
    · intro i
      use (fun _ => univ)
      refine ⟨?_, Set.pi_univ univ⟩
      exact mem_univ_pi.mpr (fun _ => MeasurableSet.univ)
    · intro _
      exact measure_lt_top _ _
    · exact iUnion_const univ
  · rintro _ ⟨s, hs, rfl⟩
    rw [mem_univ_pi] at hs
    exact h s hs

end MeasureTheory.Measure
