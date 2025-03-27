/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib
import ConsistencyGO.Defs.Consistency
import ConsistencyGO.Utils.Tendsto
import ConsistencyGO.Utils.Metric
import ConsistencyGO.Utils.ENNReal
import ConsistencyGO.Defs.Tuple

open Tendsto Tuple MeasureTheory ENNReal Classical

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
variable {Ω : Set α} [CompactSpace Ω] [Nonempty Ω]

example (A : Algorithm Ω ℝ) :
    (∀ ⦃f : Ω → ℝ⦄, Continuous f → sample_whole_space A f)
    ↔
    (∀ ⦃f : Ω → ℝ⦄, (hf : Continuous f) → isConsistentOverContinuous A hf)
    := by
  constructor
  · intro h f hf ε hε

    suffices h' : ∃ δ > 0, ∀ n > 0,
        {(u : Fin n → Ω) | dist (Tuple.max (f ∘ u)) (fmax hf) > ε} ⊆ {u | max_min_dist u > δ} by
      obtain ⟨δ, hδ, h'⟩ := h'
      have μ_mono : ∀ n > 0, measure_dist_max A hf ε n ≤ (A.μ f n) {u | max_min_dist u > δ} :=
        fun n hn => OuterMeasureClass.measure_mono (A.μ f n) (h' n hn)
      exact tendsto_zero_le_nat μ_mono (h hf δ hδ)

    let x' := compact_argmax hf
    obtain ⟨δ, hδ, hdist⟩ := Metric.continuous_iff_le.mp hf x' ε hε
    let B := Metric.closedBall x' δ
    refine ⟨δ, hδ, ?_⟩
    intro n n_pos

    have max_dist_ss_ball : {(u : (Fin n) → Ω) | dist (Tuple.max (f ∘ u)) (fmax hf) > ε} ⊆
        {u | ∀ i, u i ∉ B} := by
      intro e (he : dist (Tuple.max (f ∘ e)) (fmax hf) > ε) i
      set ei := e i
      by_contra hcontra
      have le_lt : ∀ ⦃x⦄, x ≤ δ/2 → x < δ := fun _ hx => lt_of_le_of_lt hx (div_two_lt_of_pos hδ)
      specialize hdist ei hcontra
      rw [Compact.dist_max_compact hf ei] at hdist

      obtain ⟨j, hj⟩ := Tuple.tuple_argmax f n_pos e
      rw [←hj] at he
      unfold fmax at he
      rw [Compact.dist_max_compact hf (e j)] at he
      have : f (compact_argmax hf) - f (e j) ≤ ε := by
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
  rw [←nstar_tendsto_iff_tendsto]
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
  by_contra not_sample_space
  push_neg at not_sample_space
  obtain ⟨ε₂, hε₂, not_sample_space⟩ := not_sample_space

  -- Step 1: Ball almost never hit by `A`. **RADIUS `ε₁/2` NOT `ε₁`!!!**

  obtain ⟨t, t_card, ht⟩ := (ε_cover_ne (half_pos hε₁) Ω).some_mem
  set N₁ := (ε_cover_ne (half_pos hε₁) Ω).some

  obtain ⟨c, c_in_t, hc⟩ : ∃ c ∈ t, ∀ (n : nstar),
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

    suffices h : gε₁ n_max ≤ ε₂ by
      specialize not_sample_space n_max
      exact ENNReal.contra_ineq
            (prop_measure_ne_top (A.μ_prob f n_max))
            not_sample_space
            h

    set S := {(u : Fin n_max → Ω) | ∃ c ∈ t, ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁ / 2)}

    have le_μ_cover : gε₁ n_max ≤ A.μ f n_max S := by
      suffices h : {(u : Fin n_max → Ω) | max_min_dist u > ε₁} ⊆ S from
        OuterMeasureClass.measure_mono _ h

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

  --obtain ⟨κ, hf⟩ := hf

  /-
  We define `f~` differently : we just want to ensure that it is maximized within
  `Metric.closedBall c (ε₁/2)`. This allows to show that it exists a `δ > 0` such that,
  for any `x ∉ Metric.closedBall c (ε₁/2)`, `|f~ x - f~ x^*| > δ`. The latter leads
  to a contradiction as the algorithm almost never samples in `Metric.closedBall c (ε₁/2)` and
  thus, cannot produce iterates that are `δ`-close to `f~ x^*`.
  -/

  let f_tilde := fun x =>
    if x ∈ Metric.ball c (ε₁ / 2) then
    f x + 2 * (1 - (dist c x) / (ε₁ / 2)) *
    (fmax hf - fmin hf)
    else f x

  have hf_tilde : Continuous f_tilde := by sorry


  let x' := (compact_argmax hf_tilde)

  obtain ⟨δ, δ_pos, hδ⟩ :
      ∃ δ > 0, ∀ x ∉ Metric.ball c (ε₁/2), dist (f_tilde x) (f_tilde x') > δ := by
    set fma := fmax hf
    set fmi := fmin hf

    have f_tilde_eq_f_outside : ∀ ⦃x⦄, x ∉ Metric.ball c (ε₁/2) → f_tilde x = f x := by
      intro x hx
      unfold f_tilde
      split
      · contradiction
      rfl


    have f_tilde_c_eq : f_tilde c = fma + ((f c - fmi) + (fma - fmi)) := by
      have c_in_ball : c ∈ Metric.ball c (ε₁/2) :=
        Metric.mem_ball_self (half_pos hε₁)
      unfold f_tilde
      split ; swap
      · contradiction
      rw [dist_self, zero_div]
      ring

    have sum_dist_pos : 0 < ((f c - fmi) + (fma - fmi)) := by
      have sub_argmin_nonneg : 0 ≤ (f c - fmi) :=
        sub_nonneg_of_le (compact_argmin_apply hf c)

      have non_constant : 0 < (fma - fmi) := by sorry

      exact add_pos_of_nonneg_of_pos sub_argmin_nonneg non_constant

    have x'_in_ball : x' ∈ Metric.ball c (ε₁/2) := by
      by_contra h_contra

      set fma := fmax hf
      set fmi := fmin hf

      have f_tilde_x'_lt_f_tilde_c : f_tilde x' < f_tilde c := by
        have f_tilde_c_gt_max_f : fma < f_tilde c := by

          rw [f_tilde_c_eq]

          exact lt_add_of_pos_right fma sum_dist_pos

        have f_tilde_x'_le_max_f : f_tilde x' ≤ fma := by
          have f_tilde_x'_eq : f_tilde x' = f x' := by
            unfold f_tilde
            split
            · contradiction
            rfl
          rw [f_tilde_eq_f_outside h_contra]
          exact compact_argmax_apply hf x'

        exact lt_of_le_of_lt f_tilde_x'_le_max_f f_tilde_c_gt_max_f

      have f_tilde_c_le_f_tilde_x' : f_tilde c ≤ f_tilde x' :=
        compact_argmax_apply hf_tilde c
      linarith

    have f_tilde_max_gt_fma : 0 < f_tilde x' - fma := by
      suffices h : fma < f_tilde c by
        exact gt_of_ge_of_gt
          (tsub_le_tsub_right (compact_argmax_apply hf_tilde c) fma)
          (sub_pos.mpr h)
      rw [f_tilde_c_eq]
      exact lt_add_of_pos_right fma sum_dist_pos

    have half_f_tilde_max_gt_fma := half_pos f_tilde_max_gt_fma

    refine ⟨(f_tilde x' - fma)/2, half_f_tilde_max_gt_fma, ?_⟩
    intro y hy
    rw [dist_comm]
    rw [show dist (f_tilde x') (f_tilde y) = |f_tilde x' - f_tilde y| by rfl]
    rw [abs_of_nonneg (sub_nonneg_of_le (compact_argmax_apply hf_tilde y))]
    rw [f_tilde_eq_f_outside hy]

    have fma_ge_fy : f_tilde x' - fma ≤ f_tilde x' - f y :=
      tsub_le_tsub_left (compact_argmax_apply hf y) (f_tilde x')
    have half_distmax_lt_distmax : (f_tilde x' - fma) / 2 < f_tilde x' - fma :=
      div_two_lt_of_pos f_tilde_max_gt_fma

    exact gt_of_ge_of_gt fma_ge_fy half_distmax_lt_distmax


  /- obtain ⟨δ, δ_pos, hδ⟩ :
      ∃ δ > 0, ∀ x ∈ Metric.ball c (ε₁/2), dist (f_tilde x) (f_tilde x') ≤ δ := by
    suffices h : ∃ δ > 0, ∀ x ∈ Metric.closedBall c (ε₁/2), dist (f_tilde x) (f_tilde x') ≤ δ by
      obtain ⟨δ, δ_pos, hδ⟩ := h
      exact ⟨δ, δ_pos, fun x hx => hδ x <| le_of_lt (α := ℝ) hx⟩

    set im_ball := f_tilde '' Metric.closedBall c (ε₁/2)

    have compact_im : IsCompact im_ball :=
      IsCompact.image (isCompact_closedBall c (ε₁/2)) hf_tilde.continuous

    have image_ne : im_ball.Nonempty := by
      suffices h : (Metric.closedBall c (ε₁/2)).Nonempty from
        ⟨f_tilde h.some, h.some, h.some_mem, rfl⟩
      exact Metric.nonempty_closedBall.mpr <| le_of_lt <| half_pos hε₁


    obtain ⟨M, hM_in, hM⟩ := compact_im.exists_isGreatest image_ne
    obtain ⟨m, hm_in, hm⟩ := compact_im.exists_isLeast image_ne

    have M_sub_m_pos : 0 < M - m := by
      suffices h : m < M from sub_pos.mpr h
      sorry

    refine ⟨M-m, M_sub_m_pos, ?_⟩
    intro y hy

    have x'_in_ball : x' ∈ Metric.closedBall c (ε₁/2) := by
      by_contra h_contra

      set fma := fmax hf.continuous
      set fmi := fmin hf.continuous

      have f_tilde_x'_lt_f_tilde_c : f_tilde x' < f_tilde c := by
        have f_tilde_c_gt_max_f : fma < f_tilde c := by
          have f_tilde_c_eq : f_tilde c = fma + ((f c - fmi) + (fma - fmi)) := by
            have : c ∈ Metric.closedBall c (ε₁/2) :=
              Metric.mem_closedBall_self (le_of_lt <| half_pos hε₁)
            unfold f_tilde
            split ; swap
            · contradiction
            rw [dist_self, zero_div]
            ring

          rw [f_tilde_c_eq]

          have sub_argmin_nonneg : 0 ≤ (f c - fmi) :=
            sub_nonneg_of_le (compact_argmin_apply hf.continuous c)

          have non_constant : 0 < (fma - fmi) := by sorry

          exact lt_add_of_pos_right fma (add_pos_of_nonneg_of_pos sub_argmin_nonneg non_constant)

        have f_tilde_x'_le_max_f : f_tilde x' ≤ fma := by
          have f_tilde_x'_eq : f_tilde x' = f x' := by
            unfold f_tilde
            split
            · contradiction
            rfl
          rw [f_tilde_x'_eq]
          exact compact_argmax_apply hf.continuous x'

        exact lt_of_le_of_lt f_tilde_x'_le_max_f f_tilde_c_gt_max_f

      have f_tilde_c_le_f_tilde_x' : f_tilde c ≤ f_tilde x' :=
        compact_argmax_apply hf_tilde.continuous c
      linarith


    have M_eq_max : M = f_tilde x' := by
      specialize hM ⟨x', x'_in_ball, rfl⟩
      by_contra h_contra
      push_neg at h_contra
      replace hM : f_tilde x' < M := lt_of_le_of_ne hM h_contra.symm
      obtain ⟨y, _, hy⟩ := hM_in
      have := compact_argmax_apply hf_tilde.continuous y
      linarith


    rw [M_eq_max, dist_comm]
    rw [show dist (f_tilde x') (f_tilde y) = |f_tilde x' - f_tilde y| by rfl]
    have nonneg_sub_max : 0 ≤ f_tilde x' - f_tilde y := by
      suffices h : f_tilde y ≤ f_tilde x' from sub_nonneg_of_le h
      exact compact_argmax_apply hf_tilde.continuous y
    rw [abs_of_nonneg nonneg_sub_max]

    exact tsub_le_tsub_left (hm ⟨y, hy, rfl⟩) _ -/


  have ratio_ε₂_pos : ε₂ / (2 * N₁) ≠ 0 := by
    have denom_pos : (2 * (N₁ : ℝ≥0∞))⁻¹ ≠ 0 := by
      suffices h : 2 * (N₁ : ℝ≥0∞) ≠ ⊤ from ENNReal.inv_ne_zero.mpr h
      exact mul_ne_top (ENNReal.ofNat_ne_top) (natCast_ne_top N₁)
    exact (mul_ne_zero_iff_right denom_pos).mpr <| pos_iff_ne_zero.mp hε₂

  /- have t : (ε₂ / (2 * N₁)) / 2 < ε₂ / (2 * N₁) := by
    refine ENNReal.half_lt_self ?_ ?_
    · exact this
    have neq_top : (2 * (N₁ : ℝ≥0∞))⁻¹ ≠ ⊤ := by
      suffices h : (2 * (N₁ : ℝ≥0∞)) ≠ 0 from inv_ne_top.mpr h
      have pos_2 : (2 : ℝ≥0∞) ≠ 0 := (NeZero.ne' 2).symm
      have pos_N₁ : (N₁ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt N₁.2
      exact (mul_ne_zero_iff_right pos_N₁).mpr pos_2
    rw [show ε₂ / (2 * N₁) = ε₂ * (2 * (N₁ : ℝ≥0∞))⁻¹ by rfl]
    exact mul_ne_top (LT.lt.ne_top (h_contra N₁)) neq_top -/

  specialize h hf_tilde δ δ_pos
  rw [←nstar_tendsto_iff_tendsto, ENNReal.tendsto_atTop_zero] at h
  obtain ⟨N, hN⟩ := h ((ε₂ / (2 * N₁)) / 2) (ENNReal.half_pos ratio_ε₂_pos)
  let N_succ : nstar := ⟨N.1 + 1, Nat.add_pos_left N.2 1⟩
  specialize hN N_succ (Nat.le_add_right N 1)
  specialize hc N_succ
  unfold measure_dist_max at hN

  suffices h_suff : {(u : Fin N_succ → Ω) | ∀ i, u i ∉ Metric.ball c (ε₁ / 2)}
      ⊆ {u | dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ} by
    set B := {(u : Fin N_succ → Ω) | ∀ i, u i ∉ Metric.ball c (ε₁ / 2)}
    set C := {u | dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ}

    have measure_f_tilde_gt : (ε₂ / (2 * N₁)) / 2 < A.μ f_tilde N_succ C := by
      have mono : A.μ f_tilde N_succ B ≤ A.μ f_tilde N_succ C :=
        OuterMeasureClass.measure_mono (A.μ f_tilde N_succ) h_suff

      have half_lt_ε₂ : (ε₂ / (2 * N₁)) / 2 < ε₂ / (2 * N₁) := by
        refine ENNReal.half_lt_self ?_ ?_
        · exact ratio_ε₂_pos
        have neq_top : (2 * (N₁ : ℝ≥0∞))⁻¹ ≠ ⊤ := by
          suffices h : (2 * (N₁ : ℝ≥0∞)) ≠ 0 from inv_ne_top.mpr h
          have pos_2 : (2 : ℝ≥0∞) ≠ 0 := (NeZero.ne' 2).symm
          have pos_N₁ : (N₁ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr <| Nat.ne_zero_of_lt N₁.2
          exact (mul_ne_zero_iff_right pos_N₁).mpr pos_2
        rw [show ε₂ / (2 * N₁) = ε₂ * (2 * (N₁ : ℝ≥0∞))⁻¹ by rfl]
        exact mul_ne_top (LT.lt.ne_top (not_sample_space N₁)) neq_top

      have measure_eq_f_set : A.μ f N_succ B = A.μ f_tilde N_succ B := by sorry
      have measure_f_tilde_le : (ε₂ / (2 * N₁)) ≤ A.μ f_tilde N_succ B := by
        rwa [←measure_eq_f_set]
      exact gt_of_ge_of_gt mono (gt_of_ge_of_gt measure_f_tilde_le half_lt_ε₂)

    exact ENNReal.contra_ineq
      (prop_measure_ne_top (A.μ_prob f_tilde N_succ))
      measure_f_tilde_gt
      hN
  intro u hu
  obtain ⟨i, hi⟩ := tuple_argmax f_tilde N_succ.2 u
  show dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ
  rw [←hi]
  exact hδ (u i) (hu i)

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

/- example (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε) :
    ∃ δ, f '' Metric.ball a ε = Metric.ball (f a) δ := by
  apply?
  sorry -/

example (a ε : ℝ) : IsCompact (Metric.closedBall a ε) := by
  exact isCompact_closedBall a ε

example (f : ℕ → ℝ) (hf : ∀ ε > 0, ∃ x, ∀ y ≥ x, |f y - 0| < ε) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  exact Metric.tendsto_atTop.mpr hf
