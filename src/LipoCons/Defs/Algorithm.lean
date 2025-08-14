/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Defs.Iter
import LipoCons.Utils.Measure
import LipoCons.Utils.Set
import LipoCons.Utils.Tuple
import LipoCons.Utils.Kernel
import Mathlib
/- import Mathlib.Algebra.Order.Star.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral -/

open MeasureTheory ProbabilityTheory

/-- `Algorithm α β` represents a general iterative stochastic optimization algorithm.

It models a sequence of updates where:
- `α` is the search space (e.g., parameters, candidate solutions),
- `β` is the evaluation space (e.g., objective values, feedback),
- `ν` is the initial probability measure over `α` (the starting distribution of candidates),
- `kernel_iter n` is a Markov kernel that outputs a new candidate in `α`
  given the history of the first `n` points and their evaluations,
  i.e., from the space `prod_iter_image α β n` = (`α × β`)ⁿ,
- `markov_kernel n` asserts that each such `kernel_iter n` is a valid Markov kernel.

It allows formal reasoning over joint distributions of evaluated points and convergence
properties. -/
-- ANCHOR: Algorithm
structure Algorithm (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  prob_measure : IsProbabilityMeasure ν
  kernel_iter (n : ℕ) : Kernel (prod_iter_image α β n) α
  markov_kernel (n : ℕ) : IsMarkovKernel (kernel_iter n)
-- ANCHOR_END: Algorithm

namespace Algorithm

open Tuple ENNReal Set

variable {α β : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] (A : Algorithm α β)

instance : IsProbabilityMeasure (A.ν) := A.prob_measure

instance {n : ℕ} : IsMarkovKernel (A.kernel_iter n) := A.markov_kernel n

instance : Unique (Finset.Iic 0) where
  default := ⟨0, Finset.mem_Iic.mpr (Nat.zero_le 0)⟩
  uniq a := by
    refine Subtype.coe_eq_of_eq_mk ?_
    by_contra h
    have := Finset.mem_Iic.mp a.2
    omega

noncomputable def ν_mequiv : Measure (Finset.Iic 0 → α) := A.ν.comap (MeasurableEquiv.funUnique _ _)

def iter_comap {f : α → β} (hf : Continuous f) (n : ℕ) :
  Kernel (iter α n) α :=
  (A.kernel_iter n).comap
    (prod_eval n f)
    (measurable_prod_eval n hf.measurable)

instance {f : α → β} {hf : Continuous f} : ∀ n, IsMarkovKernel (A.iter_comap (n := n) hf) := by
  simp only [iter_comap]
  infer_instance

variable {f : α → β} (hf : Continuous f)

#check A.iter_comap hf

#check Kernel.traj (X := fun _ => α) (A.iter_comap hf) 0

noncomputable def measure (A : Algorithm α β) {f : α → β} (hf : Continuous f) : Measure (ℕ → α) :=
  (Kernel.traj (A.iter_comap hf) 0).avg A.ν_mequiv

instance : IsProbabilityMeasure (A.measure hf) := by sorry

open Preorder
noncomputable abbrev fin_measure {f : α → β} (hf : Continuous f)
    {n : ℕ} : Measure (iter α n) :=
  ((Kernel.traj (X := fun _ => α) (A.iter_comap hf) 0).map (frestrictLe n)).avg A.ν_mequiv

lemma fin_measure_mono {n m : ℕ} {s : Set (iter α n)} (hs : MeasurableSet s)
    {e : Set (iter α m)} (he : MeasurableSet e) (hmn : n ≤ m)
    (hse : e ⊆ {u | subTuple hmn u ∈ s}) {f : α → β} (hf : Continuous f) :
    A.fin_measure hf e ≤ A.fin_measure hf s := by
  simp [fin_measure]
  rw [Kernel.avg_apply _ _ he]
  rw [Kernel.avg_apply _ _ hs]

  set κ := (Kernel.traj (X := fun _ => α) (A.iter_comap hf) 0)

  have : ∀ a, κ.map (frestrictLe n) a s = (κ a) ((frestrictLe n) ⁻¹' s) := by
    intro a
    exact Kernel.map_apply' κ (measurable_frestrictLe n) a hs
  simp_rw [this]
  clear this

  have : ∀ a, κ.map (frestrictLe m) a e = (κ a) ((frestrictLe m) ⁻¹' e) := by
    intro a
    exact Kernel.map_apply' κ (measurable_frestrictLe m) a he
  simp_rw [this]
  clear this
  rw [preimage, preimage]

  suffices {x : ℕ → α | frestrictLe m x ∈ e} ⊆ {x | frestrictLe n x ∈ s} by
    have : ∀ a, (κ a) {x : ℕ → α | frestrictLe m x ∈ e} ≤ (κ a) {x | frestrictLe n x ∈ s} := by
      intro a
      exact (κ a).mono this
    exact lintegral_mono this
  intro x hx
  specialize hse hx
  simp_all only [mem_setOf_eq]
  exact hse

/- lemma fin_measure_mono {f : α → β} (hf : Continuous f)
    {n : ℕ} {s₁ s₂ : Set (iter α n)} (h : s₁ ⊆ s₂) :
    A.fin_measure hf s₁ ≤ A.fin_measure hf s₂ := (A.fin_measure hf).mono h

lemma fin_measure_biUnion {ι : Type*} {f : α → β} (hf : Continuous f)
    {n : ℕ} (I : Finset ι) (s : ι → Set (iter α n)) :
    A.fin_measure hf (⋃ i ∈ I, s i) ≤ ∑ i in I, A.fin_measure hf (s i) := by
  exact measure_biUnion_finset_le I s -/

/- noncomputable abbrev fin_measure_restrict {f : α → β} (hf : Continuous f)
    {n : ℕ} (s : Set (iter α n)) := (A.measure hf).restrict (from_iter_set s) -/

lemma eq_restrict {f g : α → β} (hf : Continuous f) (hg : Continuous g)
    {s : Set α} (hs : MeasurableSet s) (h : s.restrict f = s.restrict g) (n : ℕ) :
    (A.fin_measure hf).restrict (univ.pi (fun (_ : Finset.Iic n) => s)) =
    (A.fin_measure hg).restrict (univ.pi (fun (_ : Finset.Iic n) => s)) := by
  haveI : ∀ n, IsProbabilityMeasure (A.fin_measure (n := n) hf) := by sorry
  refine Measure.pi_space_eq ?_
  intro B B_m
  have : MeasurableSet (univ.pi B) := MeasurableSet.univ_pi B_m
  rw [Measure.restrict_apply this]
  rw [Measure.restrict_apply this]
  simp [fin_measure]
  let C := fun i => (B i) ∩ s
  have pi_inter : univ.pi B ∩ (univ.pi (fun _ => s)) = univ.pi C := pi_inter_distrib.symm
  rw [pi_inter]
  clear pi_inter

  --have : MeasurableSet (univ.pi C) := MeasurableSet.univ_pi fun i => (B_m i).inter hs
  rw [Kernel.traj_map_frestrictLe]
  rw [Kernel.traj_map_frestrictLe]

  rw [Kernel.partialTraj_avg_rect_eq _ (Nat.zero_le n) _ (fun i ↦ (B_m i).inter hs)]
  rw [Kernel.partialTraj_avg_rect_eq _ (Nat.zero_le n) _ (fun i ↦ (B_m i).inter hs)]

  set E := univ.pi (fun (i : Finset.Iic 0) => C ⟨i, mem_iic_le (Nat.zero_le n) i.2⟩)

  suffices E.EqOn (fun a => Kernel.partialTraj (X := fun _ => α) (A.iter_comap hf) 0 n a (univ.pi C)) (fun a => Kernel.partialTraj (X := fun _ => α) (A.iter_comap hg) 0 n a (univ.pi C)) by
    rw [setLIntegral_congr_fun ?_ this]
    exact MeasurableSet.univ_pi (fun i => (B_m ⟨i, mem_iic_le (Nat.zero_le n) i.2⟩).inter hs)
  intro a a_mem

  sorry

end Algorithm

/- open Set ProbabilityTheory Kernel
example {α : Type*} [MeasurableSpace α] (κ₁ κ₂ : (n : ℕ) → Kernel (Π i : Finset.Iic n, α) α)
    [∀ n, IsMarkovKernel (κ₁ n)] [∀ n, IsMarkovKernel (κ₂ n)] (s : Set α) (hs : MeasurableSet s)
    (h : ∀ n, ∀ a ∈ (univ.pi (fun (_ : Finset.Iic n) => s)), κ₁ n a = κ₂ n a) :
    ∀ a ∈ (univ.pi (fun (_ : Finset.Iic 0) => s)), traj (X := fun _ => α) κ₁ 0 a {u : ℕ → α | ∀ i, u i ∈ s} = traj (X := fun _ => α) κ₂ 0 a {u : ℕ → α | ∀ i, u i ∈ s} := by
  intro a a_mem
  set s_inf := {u : ℕ → α | ∀ i, u i ∈ s}
  rw [traj_apply]
  rw [traj_apply]
  simp [trajFun]
  rw [MeasureTheory.AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm]
  rw [MeasureTheory.AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm]
  · simp [trajContent, projectiveFamilyContent_eq]

    sorry
  · have : s_inf = univ.pi (fun _ => s) := by sorry
    rw [this]
    apply?
    refine ⟨Finset.Iic 0, (univ.pi (fun (_ : Finset.Iic 0) => s)), ?_, ?_⟩
    · exact MeasurableSet.univ_pi fun i ↦ hs
    · simp [cylinder]
      rw [preimage]
      sorry
  · sorry -/
