/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib
import ConsistencyGO.Defs.Consistency
import ConsistencyGO.Utils.Tendsto
import ConsistencyGO.Utils.Metric
import ConsistencyGO.Utils.ENNReal
import ConsistencyGO.Defs.Tuple

open Tendsto Tuple MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
variable {Ω : Set α} [CompactSpace Ω] [Nonempty Ω]

example (A : Algorithm Ω ℝ) :
    (∀ ⦃f : Ω → ℝ⦄, f ∈ all_lipschitz → sample_whole_space A f)
    ↔
    (∀ ⦃f : Ω → ℝ⦄, (hf : f ∈ all_lipschitz) → isConsistentOverLipschitz A hf)
    := by
  constructor
  · intro h f hf ε hε
    have hcont := hf.choose_spec.continuous

    suffices h' : ∃ δ > 0, ∀ n > 0,
        {(u : Fin n → Ω) | dist (Tuple.max (f ∘ u)) (fmax hcont) > ε} ⊆ {u | max_min_dist u > δ} by
      obtain ⟨δ, hδ, h'⟩ := h'
      have μ_mono : ∀ n > 0, measure_dist_max A hcont ε n ≤ (A.μ f n) {u | max_min_dist u > δ} :=
        fun n hn => OuterMeasureClass.measure_mono (A.μ f n) (h' n hn)
      exact tendsto_zero_le_nat μ_mono (h hf δ hδ)

    let x' := compact_argmax hcont
    obtain ⟨δ, hδ, hdist⟩ := (Metric.continuous_iff_le.mp hcont) x' ε hε
    let B := Metric.closedBall x' δ
    refine ⟨δ, hδ, ?_⟩
    intro n n_pos

    have max_dist_ss_ball : {(u : (Fin n) → Ω) | dist (Tuple.max (f ∘ u)) (fmax hcont) > ε} ⊆
        {u | ∀ i, u i ∉ B} := by
      intro e (he : dist (Tuple.max (f ∘ e)) (fmax hcont) > ε) i
      set ei := e i
      by_contra hcontra
      have le_lt : ∀ ⦃x⦄, x ≤ δ/2 → x < δ := fun _ hx => lt_of_le_of_lt hx (div_two_lt_of_pos hδ)
      specialize hdist ei hcontra
      rw [Compact.dist_max_compact hcont ei] at hdist

      obtain ⟨j, hj⟩ := Tuple.tuple_argmax f n_pos e
      rw [←hj] at he
      unfold fmax at he
      rw [Compact.dist_max_compact hcont (e j)] at he
      have : f (compact_argmax hcont) - f (e j) ≤ ε := by
        have ineq : f ei ≤ f (e j) := by
          rw [hj]
          exact Tuple.le_max (f ∘ e) n_pos i
        exact Preorder.le_trans _ _ _ (tsub_le_tsub_left ineq _) hdist
      linarith

    suffices h' : {(u : (Fin n) → Ω) | ∀ i, u i ∉ B} ⊆ {u | max_min_dist u > δ} from
      fun _ ha ↦ h' (max_dist_ss_ball ha)

    intro u (hu : ∀ i, u i ∉ B)
    replace hu : ∀ i, dist (u i) x' > δ := fun i => lt_of_not_ge (hu i)
    obtain ⟨i, hi⟩ := Tuple.tuple_argmin (fun xi => dist xi x') n_pos u
    specialize hu i
    rw [hi] at hu
    have argmax_le : min_dist_x u x' ≤ max_min_dist u :=
      compact_argmax_apply (min_dist_x_continuous u) x'
    exact gt_of_ge_of_gt argmax_le hu

  intro h f hf ε₁ hε₁
  apply nstar_tendsto_imp_tendsto
  set gε₁ := fun (n : nstar) => A.μ f n {u | max_min_dist u > ε₁}
  have antitone_gε₁ : Antitone gε₁ := by
    intro n m hnm
    let S := fun n => {(u : Fin n → Ω) | max_min_dist u > ε₁}
    suffices h : {(u : ℕ → Ω) | Tuple.toTuple m u ∈ S m} ⊆ {(u : ℕ → Ω) | Tuple.toTuple n u ∈ S n}
        from A.μ_mono f h
    intro u (hu : max_min_dist (toTuple m u) > ε₁)
    unfold max_min_dist min_dist_x at hu
    set x' := compact_argmax (min_dist_x_continuous (toTuple m u))
    obtain ⟨i, hi⟩ :=
      Tuple.tuple_argmin (f := (fun xi ↦ dist xi x')) m.2 (toTuple m u)
    rw [←hi] at hu
    obtain ⟨j, hj⟩ :=
      Tuple.tuple_argmin (f := (fun xi ↦ dist xi x')) n.2 (toTuple n u)

    suffices h : dist (toTuple m u i) x' ≤ dist (toTuple n u j) x' from
        gt_of_ge_of_gt
        (compact_argmax_apply (min_dist_x_continuous (toTuple n u)) x')
        (lt_of_lt_of_eq (gt_of_ge_of_gt h hu) hj)
    have le_min :=
      Tuple.le_min (f := (fun xi ↦ dist xi x') ∘ (toTuple m u)) m.2 ⟨j, Fin.val_lt_of_le j hnm⟩
    rwa [←hi] at le_min

  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone antitone_gε₁]
  by_contra h_contra
  push_neg at h_contra
  obtain ⟨ε₂, hε₂, h_contra⟩ := h_contra

  -- Step 1: Ball almost never hit by `A`. **RADIUS `ε₁/2` NOT `ε₁`!!!**

  obtain ⟨t, t_card, ht⟩ := (ε_cover_ne (half_pos hε₁) Ω).some_mem
  set N₁ := (ε_cover_ne (half_pos hε₁) Ω).some
  have : ∃ c ∈ t, ∀ (n : nstar),
      ε₂/(2 * N₁) ≤ A.μ f n {u : Fin n → Ω | ∀ i, u i ∉ Metric.ball c (ε₁/2)} := by
    by_contra h_contra
    push_neg at h_contra
    replace h_contra : ∃ (n : nstar), ∀ c ∈ t,
      A.μ f n {u : Fin n → Ω | ∀ i, u i ∉ Metric.ball c (ε₁/2)} < ε₂/(2 * N₁) := by
      choose choice_fun h_contra using h_contra
      let choice_fun' := fun (c : t) => choice_fun c.1 c.2
      let n_max := Fintype.max_image choice_fun'
      use n_max
      intro c hc
      let S := fun n => {(u : Fin n → Ω) | ∀ i, u i ∉ Metric.ball c (ε₁/2)}
      let n := choice_fun c hc
      suffices h : {u | toTuple n_max u ∈ S n_max} ⊆ {u | toTuple n u ∈ S n} from
        lt_of_le_of_lt (A.μ_mono f h) <| h_contra c hc

      have n_le_n_max : n ≤ n_max := by
        have ne_subtype : Nonempty { x // x ∈ t } := by
          have card_pos : 0 < t.card := by
            rw [t_card]
            exact N₁.2
          have t_ne : t.Nonempty := Finset.card_pos.mp card_pos
          exact ⟨t_ne.choose, t_ne.choose_spec⟩
        exact Fintype.le_max_image choice_fun' ⟨c, hc⟩
      exact fun _ hu i => hu ⟨i.1, Fin.val_lt_of_le i n_le_n_max⟩
    obtain ⟨n_max, hn_max⟩ := h_contra

    have le_μ_cover : gε₁ n_max ≤ A.μ f n_max {u | ∃ c ∈ t, ∀ i, u i ∉ Metric.ball c (ε₁/2)} := by
      suffices h : {(u : Fin n_max → Ω) | max_min_dist u > ε₁} ⊆
          {u | ∃ c ∈ t, ∀ i, u i ∉ Metric.ball c (ε₁/2)} from OuterMeasureClass.measure_mono _ h

      intro u (hu : max_min_dist u > ε₁)
      let x' := (compact_argmax (min_dist_x_continuous u))

      obtain ⟨c, c_in_t, hc⟩ : ∃ c ∈ t, x' ∈ Metric.ball c (ε₁/2) := by
        have x'_in_cover : x' ∈ ⋃ c ∈ t, Metric.ball c (ε₁/2) := by
          rw [←ht]
          trivial
        simp_all only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop, Subtype.exists]

      refine ⟨c, c_in_t, ?_⟩

      unfold max_min_dist min_dist_x at hu
      set m := Tuple.min ((fun xi ↦ dist xi x') ∘ u)

      intro i

      have : ε₁ < dist (u i) x' := by
        suffices h : m ≤ dist (u i) x' from gt_of_ge_of_gt h hu
        exact Tuple.le_min ((fun xi ↦ dist xi x') ∘ u) n_max.2 i

      by_contra h
      suffices dist (u i) x' < ε₁ by linarith
      calc dist (u i) x' ≤ dist (u i) c + dist c x' := dist_triangle (u i) c x'
        _ < ε₁/2 + dist c x' := (add_lt_add_iff_right _).mpr h
        _ = ε₁/2 + dist x' c := by rw [dist_comm c x']
        _ < ε₁/2 + ε₁/2 := (add_lt_add_iff_left _).mpr hc
        _ = ε₁ := by ring

    set S := {(u : Fin n_max → Ω) | ∃ c ∈ t, ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁ / 2)}

    have le_μ_ε₂ : gε₁ n_max ≤ ε₂ := by
      suffices h : gε₁ n_max ≤ ε₂ / 2 from Preorder.le_trans _ _ _ h ENNReal.half_le_self
      calc gε₁ n_max ≤ (A.μ f n_max) S := le_μ_cover
      _ ≤ A.μ f n_max (⋃ c ∈ t, {u | ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁ / 2)}) := by
        suffices h : S ⊆ ⋃ c ∈ t, {u | ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁ / 2)} from
          OuterMeasureClass.measure_mono _ h
        rintro u ⟨c, hc, hu⟩
        rw [Set.mem_iUnion]
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨c, hc, hu⟩
      _ ≤ ∑ c ∈ t, A.μ f n_max {u | ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁ / 2)} :=
        measure_biUnion_finset_le t _
      _ ≤ ∑ c ∈ t, ε₂ / (2 * N₁) := Finset.sum_le_sum (fun c hc => le_of_lt <| hn_max c hc)
      _ = ε₂ / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, t_card]
        calc N₁ * (ε₂ / (2 * N₁)) = N₁ * (ε₂ * ((2 * N₁) : ℝ≥0∞)⁻¹) := rfl
        _ = N₁ * (ε₂ * (2⁻¹ * (N₁ : ℝ≥0∞)⁻¹)) := by
          rw [ENNReal.mul_inv (Or.inr <| natCast_ne_top ↑N₁) (Or.inl ofNat_ne_top)]
        _ = N₁ * (N₁ : ℝ≥0∞)⁻¹ * ε₂ * 2⁻¹ := by ring
        _ = ε₂ / 2 := by
          rw [
            ENNReal.mul_inv_cancel
            (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt N₁.2))
            (natCast_ne_top ↑N₁),
            one_mul
          ]
          rfl
    specialize h_contra n_max
    exact ENNReal.contra_ineq
          (LT.lt.ne_top h_contra)
          (prop_measure_ne_top (A.μ_prob f n_max))
          h_contra
          le_μ_ε₂

        /- have : N₁ * (ε₂ / (2 * N₁)) = N₁ * ε₂ / (2 * N₁) := (mul_div_assoc _ _ _).symm
        --rw [this]
        have : ε₂ / (2 * N₁) = ε₂ * ((2 * N₁) : ℝ≥0∞)⁻¹ := by
          rfl
        rw [show ε₂ / (2 * N₁) = ε₂ * ((2 * N₁) : ℝ≥0∞)⁻¹ by rfl]
        rw [ENNReal.mul_inv (Or.inr <| natCast_ne_top ↑N₁) (Or.inl ofNat_ne_top)]
        have : N₁ * (ε₂ * (2⁻¹ * (N₁ : ℝ≥0∞)⁻¹)) = N₁ * ε₂ * 2⁻¹ * (N₁ : ℝ≥0∞)⁻¹ := by
          ring

        --rw [←mul_div_assoc]
        --calc N₁ * (ε₂ / (2 * N₁)) =
        sorry -/

    /- have : A.μ f n_max {u | ∀ c ∈ t, ∃ i, u i ∈ Metric.ball c (ε₁/2)}
        ≤ A.μ f n_max {u | max_min_dist u ≤ ε₁} := by
      suffices h : {(u : Fin n_max → Ω) | ∀ c ∈ t, ∃ i, u i ∈ Metric.ball c (ε₁/2)} ⊆
          {u | max_min_dist u ≤ ε₁} from OuterMeasureClass.measure_mono _ h
      intro u hu
      let x' := (compact_argmax (min_dist_x_continuous u))
      obtain ⟨c, c_in_t, hc⟩ : ∃ c ∈ t, x' ∈ Metric.ball c (ε₁/2) := by
        have x'_in_cover : x' ∈ ⋃ c ∈ t, Metric.ball c (ε₁/2) := by
          rw [←ht]
          trivial
        simp_all only [Set.iUnion_coe_set, Set.mem_iUnion, exists_prop, Subtype.exists]
      obtain ⟨i, hi⟩ := hu c c_in_t
      have dist_ui_x'_lt_ε₁ : dist (u i) x' < ε₁ := by
        suffices h : dist (u i) c + dist c x' < ε₁ from lt_of_le_of_lt (dist_triangle (u i) c x') h
        calc dist (u i) c + dist c x' < ε₁/2 + dist c x' :=
          (add_lt_add_iff_right _).mpr hi
        _ = ε₁/2 + dist x' c := by rw [dist_comm c x']
        _ < ε₁/2 + ε₁/2 := (add_lt_add_iff_left _).mpr hc
        _ = ε₁ := by ring
      suffices h : Tuple.min ((fun xi ↦ dist xi x') ∘ u) < ε₁ from le_of_lt h
      exact lt_of_le_of_lt (Tuple.le_min _ n_max.2 i) dist_ui_x'_lt_ε₁ -/


  sorry

open ENNReal

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) : (a + b).toReal = a.toReal + b.toReal := by
  exact toReal_add ha hb

example (μ : Measure ℝ) (A : Set ℝ) (h : MeasurableSet A) [IsFiniteMeasure μ] :
  μ A = μ Set.univ - μ Aᶜ := by
  have : MeasurableSet Aᶜ := MeasurableSet.compl_iff.mpr h
  have := measure_compl this (measure_ne_top μ Aᶜ)
  rw [←this, compl_compl A]


example (μ : Measure ℝ) (A : ℕ → Set ℝ) : μ (⋃ i, A i) ≤ ∑' i, μ (A i) := by
  exact measure_iUnion_le A

example (μ : Measure ℝ) (n : ℕ) (A : Fin n → Set ℝ) : μ (⋃ i, A i) ≤ ∑ i, μ (A i) := by
  exact measure_iUnion_fintype_le μ A

example (ι : Type*) (s : Finset ι) (b : ℝ≥0∞) : ∑ _ ∈ s, b = s.card * b := by
  simp_all only [nonempty_subtype, Finset.sum_const, nsmul_eq_mul]

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  exact ENNReal.mul_inv (Or.inr hb) (Or.inl ha)

example (a : ℝ≥0∞) (ha : a ≠ ⊤) (ha2 : a ≠ 0) : a * a⁻¹ = 1 := by
  exact ENNReal.mul_inv_cancel ha2 ha

example (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (h1 : a < b) (h2 : b ≤ a) : False := by
  have : a.toReal < b.toReal := toReal_strict_mono hb h1
  have : b.toReal ≤ a.toReal := (toReal_le_toReal hb ha).mpr h2
  linarith
