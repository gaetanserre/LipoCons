import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  {μ ν : Measure (∀ i, α i)} [IsFiniteMeasure μ]

/-- Two measures on a finite product space are equal if they agree on all measurable rectangles
of the form `univ.pi s`, provided one of them is finite. -/
lemma pi_space_eq
    (h : ∀ s : ∀ i, Set (α i), (∀ i, MeasurableSet (s i)) → μ (univ.pi s) = ν (univ.pi s)) :
    μ = ν := by
  refine Measure.FiniteSpanningSetsIn.ext
    generateFrom_pi.symm (IsPiSystem.pi (fun _ => MeasurableSpace.isPiSystem_measurableSet)) ?_ ?_
  · refine { set := fun _ => univ, set_mem := ?_, finite := ?_, spanning := ?_ }
    · intro i
      use (fun _ => univ)
      refine ⟨?_, Set.pi_univ univ⟩
      exact mem_univ_pi.mpr (fun _ => MeasurableSet.univ)
    · exact fun _ => measure_lt_top _ _
    · exact iUnion_const univ
  · rintro _ ⟨s, hs, rfl⟩
    rw [mem_univ_pi] at hs
    exact h s hs

end MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]
  (κ₁ κ₂ : (n : ℕ) → Kernel (Π _ : Finset.Iic n, α) α)
  [∀ n, IsMarkovKernel (κ₁ n)] [∀ n, IsMarkovKernel (κ₂ n)]
  {s : Set α} (hs : MeasurableSet s)
  (h : ∀ n, (univ.pi (fun _ => s)).EqOn (fun a => κ₁ n a) (fun a => κ₂ n a))

example {a b : ℕ} (hab : a ≤ b) : ∀ e ∈ univ.pi (fun _ => s),
    (Kernel.partialTraj (X := fun _ => α) κ₁ a b e).restrict (univ.pi (fun _ => s)) =
    (Kernel.partialTraj (X := fun _ => α) κ₂ a b e).restrict (univ.pi (fun _ => s)) := by
  intro e e_mem
  refine Measure.pi_space_eq ?_
  intro B B_m
  let C := fun i => (B i) ∩ s
  induction b, hab using Nat.le_induction with
    | base => simp
    | succ k h hk =>
      simp only [Kernel.partialTraj_succ_eq_comp h, Kernel.partialTraj_succ_self]
      sorry
