/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.Tuple
import LipoCons.Utils.Measure
import LipoCons.Utils.Set
import LipoCons.Utils.ENNReal
import LipoCons.Defs.NPos
import Mathlib

set_option maxHeartbeats 0

open MeasureTheory ProbabilityTheory

namespace Tuple

variable {α β : Type*}

def prod_eval (n : ℕ) (f : α → β) (u : Fin n → α) := (u, f ∘ u)

lemma prod_eval_eq_restrict (n : ℕ) {f g : α → β} (s : Set α) (hfg : s.restrict f = s.restrict g)
    {u : Fin n → α} (hu : ∀ i, u i ∈ s) : prod_eval n f u = prod_eval n g u := by
  ext i
  · rfl
  · specialize hu i
    simp_all only [Set.restrict_eq_restrict_iff]
    have fwd : f (u i) = g (u i) := Set.EqOn.eq_of_mem hfg hu
    exact fwd

variable [MeasurableSpace α] [MeasurableSpace β]

lemma measurable_prod_eval (n : ℕ) {f : α → β} (hf : Measurable f) :
    Measurable (prod_eval n f) := by
  refine Measurable.prodMk measurable_id ?_
  unfold Function.comp
  apply measurable_pi_lambda
  intro a
  apply Measurable.comp'
  · exact hf
  · exact measurable_pi_apply _

abbrev append {n : ℕ} (u : Fin n → α) (a : α) : Fin (n + 1) → α := Fin.snoc u a

def pop {n : ℕ} (u : Fin (n + 1) → α) : Fin n → α := fun i => u i.castSucc

end Tuple

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {n : ℕ}

open Tuple

variable (κ : Kernel α β) (μ : Measure α)

noncomputable def avg : Measure β := by
  refine Measure.ofMeasurable (fun s hs => ∫⁻ a, κ a s ∂μ) ?_ ?_
  · simp only [measure_empty, MeasureTheory.lintegral_const, zero_mul]
  intro f f_m f_d
  simp_rw [fun x => measure_iUnion f_d f_m]
  refine lintegral_tsum ?_
  intro i
  specialize f_m i
  exact (κ.measurable_coe f_m).aemeasurable

@[simp]
lemma avg_apply {s : Set β} (hs : MeasurableSet s) :
  κ.avg μ s = ∫⁻ a, κ a s ∂μ := Measure.ofMeasurable_apply s hs

end ProbabilityTheory.Kernel

abbrev iter (α : Type*) (n : ℕ) := Fin (n + 1) → α

def iter_mequiv (α : Type*) [MeasurableSpace α] (n : ℕ) : iter α (n + 1) ≃ᵐ α × iter α n :=
  MeasurableEquiv.piFinSuccAbove (fun _ => α) (Fin.last (n + 1))




abbrev prod_iter_image (α β : Type*) (n : ℕ) := (iter α n) × (iter β n)

structure Algo (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  ν : Measure α
  prob_measure : IsProbabilityMeasure ν
  kernel_iter (n : ℕ) : Kernel (prod_iter_image α β n) α
  markov_kernel (n : ℕ) : IsMarkovKernel (kernel_iter n)

namespace Algo


open Tuple Set ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (A : Algo α β)

instance : IsProbabilityMeasure A.ν := A.prob_measure
instance {n : ℕ}: IsMarkovKernel (A.kernel_iter n) := A.markov_kernel n

def iter_comap {n : ℕ} {f : α → β} (hf : Measurable f) :=
    (A.kernel_iter n).comap (prod_eval (n + 1) f) (measurable_prod_eval (n + 1) hf)

noncomputable def jsp {n : ℕ} {f : α → β} (hf : Measurable f) (μ : Measure (iter α n)) :
    Measure (iter α (n + 1)) := by
  refine Measure.ofMeasurable
    (fun s hs => ∫⁻ u, (∫⁻ x, s.indicator 1 (append u x) ∂ A.iter_comap hf u) ∂ μ) ?_ ?_
  · simp
  · intro f f_m f_d
    simp only
    set g := fun i x (u : iter α n) => ((f i).indicator 1 (append u x) : ℝ≥0∞)
    have tt : ∀ i, Measurable (Function.uncurry (g i)) := by
      intro i
      refine measurable_of_Ici ?_
      intro x
      rw [preimage]
      simp [Function.uncurry, mem_Ici, -measurableSet_setOf, g]
      by_cases hx : x = 0
      · rw [hx]
        simp only [zero_le, setOf_true, MeasurableSet.univ]
      · by_cases hx' : 1 < x
        · suffices {e : α × iter α n | x ≤ (f i).indicator 1 (append e.2 e.1)} = ∅ by
            rw [this]
            exact MeasurableSet.empty
          ext e
          constructor
          swap
          · intro
            contradiction
          · intro he
            have t : (1 : ℝ≥0∞) < (f i).indicator 1 (append e.2 e.1) := by
              exact lt_of_le_of_lt' he hx'
            have : (f i).indicator 1 (append e.2 e.1) ≤ (1 : ℝ≥0∞) := by
              by_cases h : (append e.2 e.1) ∈ (f i)
              · rw [indicator_of_mem h]
                rfl
              · rw [indicator_of_notMem h]
                exact zero_le _
            exact ENNReal.contra_ineq t this
        · push_neg at hx
          push_neg at hx'
          replace hx : 0 < x := by exact pos_of_ne_zero hx
          suffices MeasurableSet {e : α × iter α n | append e.2 e.1 ∈ (f i)} by
            have : {e : α × iter α n | x ≤ (f i).indicator 1 (append e.2 e.1)} =
                {e | append e.2 e.1 ∈ (f i)} := by
              ext e
              constructor
              · intro he
                have : (f i).indicator 1 (append e.2 e.1) ≠ (0 : ℝ≥0∞) :=
                  (ne_of_lt (lt_of_le_of_lt' he hx)).symm
                have := mem_of_indicator_ne_zero this
                exact this
              · intro he
                have : (f i).indicator 1 (append e.2 e.1) = (1 : ℝ≥0∞) := by
                  exact (indicator_eq_one_iff_mem ℝ≥0∞).mpr he
                rwa [←this] at hx'
            rwa [this]
          specialize f_m i
          let eq := iter_mequiv α n
          have : {e : α × iter α n | append e.2 e.1 ∈ f i} = eq '' (f i) := by
            ext e
            constructor
            · intro he
              rw [image]
              refine ⟨append e.2 e.1, he, ?_⟩
              simp [append]
              let t : Fin (n + 1 + 1) → α := Fin.snoc e.2 e.1
              let tt := t (Fin.last (n + 1))
              let ttt := Fin.removeNth (Fin.last (n + 1)) t
              show (tt, Fin.removeNth (Fin.last (n + 1)) t) = e
              simp_all only [mem_setOf_eq, Fin.snoc_last, Fin.removeNth_last, Fin.init_snoc, Prod.mk.eta, tt, t]
            · rintro ⟨a, a_mem, ha⟩
              suffices a = append e.2 e.1 by
                rwa [this] at a_mem





              sorry
          rw [this]
          exact eq.measurableSet_image.mpr f_m
    simp_rw [indicator_iUnion f_d]
    have : ∀ u, ∫⁻ x, ∑' i, (f i).indicator 1 (append u x) ∂(A.iter_comap hf) u =
        ∑' i, ∫⁻ x, (f i).indicator 1 (append u x) ∂(A.iter_comap hf) u := by
      intro u
      refine lintegral_tsum ?_
      intro i
      apply Measurable.aemeasurable
      exact (tt i).of_uncurry_right
    simp_rw [this]
    refine lintegral_tsum ?_
    intro i
    apply Measurable.aemeasurable
    haveI : IsFiniteKernel (A.iter_comap (n := n) hf) := by
      simp [iter_comap]
      infer_instance
    show Measurable (fun u ↦ ∫⁻ x, g i x u ∂(A.iter_comap hf) u)
    exact Measurable.lintegral_kernel_prod_left (tt i)

noncomputable def marginal (n : ℕ) {f : α → β} (hf : Measurable f) : Measure (iter α n) :=
  if h : n = 0 then Measure.pi (fun _ => A.ν)
  else by
    rw [←Nat.succ_pred_eq_of_ne_zero h]
    exact A.jsp hf (marginal (n - 1) hf)

instance {n : ℕ} {f : α → β} {hf : Measurable f} : IsProbabilityMeasure (A.marginal n hf) := by
  induction n with
  | zero =>
    simp [marginal]
    infer_instance
  | succ m hm =>

    have succ_m_ne_zero : m + 1 ≠ 0 := (Nat.zero_ne_add_one m).symm
    rw [marginal] at ⊢
    split
    · contradiction
    set μf : Measure (iter α (m + 1)) := by
      rw [←Nat.succ_pred_eq_of_ne_zero succ_m_ne_zero]
      exact A.jsp hf (A.marginal (m + 1 - 1) hf)
    have : μf = A.jsp hf (A.marginal m hf) := by rfl
    rw [this]
    clear this
    suffices (A.jsp hf (A.marginal m hf)) univ = 1 from isProbabilityMeasure_iff.mpr this
    simp [jsp, Measure.ofMeasurable_apply _ MeasurableSet.univ]
    haveI : IsMarkovKernel (A.iter_comap (n := m) hf) := by
      simp [iter_comap]
      infer_instance
    simp?

example {f g : α → β} (hf : Measurable f) (hg : Measurable g) {s : Set α}
    (hs : MeasurableSet s) (h : s.restrict f = s.restrict g) (n : ℕ) :
    (A.marginal n hf).restrict {u | ∀ i, u i ∉ sᶜ} =
    (A.marginal n hg).restrict {u | ∀ i, u i ∉ sᶜ} := by
  simp only [mem_compl_iff, not_not]
  induction n with
  | zero =>
    simp [marginal]
  | succ m hm =>
    apply pi_eq
    intro B hB
    simp [Measure.restrict_apply <| MeasurableSet.univ_pi hB]
    set us := univ.pi B ∩ {u : iter α (m + 1) | ∀ i, u i ∈ s}

    let C := fun i => (B i) ∩ s
    have : us = univ.pi C := by
      ext u
      constructor
      · intro u_mem
        exact fun i _ => ⟨u_mem.1 i trivial, u_mem.2 i⟩
      · intro u_mem
        constructor
        · exact fun i _ => (u_mem i trivial).1
        . exact fun i => (u_mem i trivial).2
    rw [this]
    clear this

    rw (occs := .pos [1]) [marginal]
    rw (occs := .pos [2]) [marginal]
    split
    · contradiction
    next succ_m_ne_zero =>
    set tf : Measure (iter α (m + 1)) := by
      rw [←Nat.succ_pred_eq_of_ne_zero succ_m_ne_zero]
      exact A.jsp hf (A.marginal (m + 1 - 1) hf)


    set tg : Measure (iter α (m + 1)) := by
      rw [←Nat.succ_pred_eq_of_ne_zero succ_m_ne_zero]
      exact A.jsp hg (A.marginal (m + 1 - 1) hg)

    have : tf = A.jsp hf (A.marginal m hf) := by rfl
    rw [this]
    clear this

    have : tg = A.jsp hg (A.marginal m hg) := by rfl
    rw [this]
    clear this

    have measurable_prod : MeasurableSet (univ.pi C : Set (iter α (m + 1))) :=
      MeasurableSet.univ_pi (fun i => (hB i).inter hs)
    simp [jsp, Measure.ofMeasurable_apply _ measurable_prod]

    let C_head := fun i : Fin (m + 1) => (B i.castSucc) ∩ s
    let C_last := C ⟨m + 1, lt_add_one (m + 1)⟩

    have : ∀ ⦃f⦄, (hf : Measurable f) → ∀ u,
        ∫⁻ (x : α), (univ.pi C).indicator 1 (append u x) ∂(A.iter_comap hf) u =
        (univ.pi C_head).indicator
          (fun u => ∫⁻ (x : α), C_last.indicator 1 x ∂(A.iter_comap hf) u) u :=
      by
        intro f hf u
        by_cases u_mem : u ∉ univ.pi C_head
        · rw [indicator_of_notMem u_mem]
          suffices ∀ x, (append u x) ∉ (univ.pi C) by
            have : ∀ x, (univ.pi C).indicator 1 (append u x) = (0 : ℝ≥0∞) :=
              fun x => indicator_of_notMem (this x) _
            simp_rw [this]
            exact lintegral_zero
          by_contra h_contra
          push_neg at h_contra
          obtain ⟨x, hx⟩ := h_contra
          obtain ⟨i, hi⟩ := not_forall.mp fun a ↦ u_mem fun i _ ↦ a i
          specialize hx i.castSucc trivial

          have : append u x i.castSucc = u i := by
            simp? [append]
            sorry

          rw [this] at hx
          have : C i.castSucc = C_head i := rfl
          rw [this] at hx
          contradiction
        · push_neg at u_mem
          rw [indicator_of_mem u_mem]
          suffices ∀ x, (univ.pi C).indicator 1 (append u x) = (C_last.indicator 1 x : ℝ≥0∞) by
            simp_rw [this]
          intro x
          suffices x ∈ C_last ↔ (append u x) ∈ univ.pi C by
            by_cases hx : x ∈ C_last
            · rw [indicator_of_mem hx]
              rw [indicator_of_mem (this.mp hx)]
              rfl
            · rw [indicator_of_notMem hx]
              rw [this] at hx
              rw [indicator_of_notMem hx]
          constructor
          · intro hx i _
            by_cases hi : i = m + 1
            · have : append u x i = x := by
                simp only [append, hi, lt_self_iff_false, ↓reduceDIte]
              rwa [this, Fin.eq_mk_iff_val_eq.mpr hi]
            · have le : i < m + 1 :=
                Nat.lt_of_le_of_ne (Fin.is_le i) hi
              have : append u x i = u ⟨i, le⟩ := by
                simp only [append, le, ↓reduceDIte]
              rw [this]
              exact u_mem ⟨i, le⟩ trivial

          · intro hx
            specialize hx ⟨m + 1, lt_add_one (m + 1)⟩ trivial
            simp [append] at hx
            exact hx

    simp_rw [this hf]
    simp_rw [this hg]
    clear this

    have measurable_head : MeasurableSet (univ.pi C_head) := by
      refine MeasurableSet.univ_pi (fun i => (hB i.castSucc).inter hs)

    rw [lintegral_indicator measurable_head]
    rw [lintegral_indicator measurable_head]


    set us' := {u : iter α m | ∀ i, u i ∈ s}
    have : univ.pi C_head ⊆ us' :=
      fun _ u_mem i => (u_mem i trivial).2

    set f_int := fun u : iter α m => ∫⁻ (x : α), C_last.indicator 1 x ∂(A.iter_comap hf) u
    set g_int := fun u : iter α m => ∫⁻ (x : α), C_last.indicator 1 x ∂(A.iter_comap hg) u

    set μf := (A.marginal m hf).restrict (univ.pi C_head)
    set μg := (A.marginal m hg).restrict (univ.pi C_head)

    have : μf = μg := by
      simp [μf, μg]
      rw [←(A.marginal m hf).restrict_restrict_of_subset this]
      rw [←(A.marginal m hg).restrict_restrict_of_subset this]
      rw [(A.marginal m hf).restrict_restrict measurable_head]
      rw [(A.marginal m hg).restrict_restrict measurable_head]

      ext E hE
      rw [Measure.restrict_apply hE]
      rw [Measure.restrict_apply hE]
      have : E ∩ (univ.pi C_head ∩ us') = E ∩ univ.pi C_head ∩ us' :=
        (inter_assoc E (univ.pi C_head) us').symm
      rw [this]
      have tt := congrFun (congrArg DFunLike.coe hm) (E ∩ univ.pi C_head)
      have : MeasurableSet (E ∩ univ.pi C_head) := hE.inter measurable_head
      rw [Measure.restrict_apply this] at tt
      rwa [Measure.restrict_apply this] at tt
    rw [this]

    suffices ∀ u ∈ univ.pi C_head, f_int u = g_int u from
      setLIntegral_congr_fun measurable_head this

    intro u u_mem

    suffices (A.iter_comap hf) u = (A.iter_comap hg) u by
      simp [f_int, g_int]
      rw [this]

    simp only [iter_comap, Kernel.coe_comap, Function.comp_apply]

    suffices ∀ i, u i ∈ s by rw [prod_eval_eq_restrict (m + 1) s h this]

    exact fun i => (u_mem i trivial).2


end Algo
