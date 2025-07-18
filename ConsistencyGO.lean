/-
- Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Defs.Consistency
import ConsistencyGO.Utils.ENNReal
import ConsistencyGO.Utils.Metric
import ConsistencyGO.Utils.ConstructF
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.RCLike.Basic

open Tendsto Tuple MeasureTheory ENNReal Continuous Classical Set

variable {α : Type*} [MeasurableSpace α] [SeminormedAddCommGroup α] [NormedSpace ℝ α]
[CompactSpace α] [Nonempty α]

theorem sample_iff_consistent (A : Algorithm α ℝ) :
    (∀ ⦃f : α → ℝ⦄, Lipschitz f → sample_whole_space A f)
    ↔
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → isConsistentOverLipschitz A hf) := by
  constructor
  · intro h f hf ε hε
    have hfc := hf.continuous
    suffices h' : ∃ δ > 0, ∀ n > 0,
        {(u : Fin n → α) | dist (Tuple.max (f ∘ u)) (fmax hf) > ε} ⊆ {u | max_min_dist u > δ} by
      obtain ⟨δ, hδ, h'⟩ := h'
      have μ_mono : ∀ n > 0, measure_dist_max A hf ε n ≤ (A.μ f n) {u | max_min_dist u > δ} :=
        fun n hn => (A.μ f n).mono (h' n hn)
      exact tendsto_zero_le_nat μ_mono (h hf δ hδ)

    let x' := compact_argmax hfc
    obtain ⟨δ, hδ, hdist⟩ := Metric.continuous_iff_le.mp hfc x' ε hε
    let B := Metric.closedBall x' δ
    refine ⟨δ, hδ, ?_⟩
    intro n n_pos

    have max_dist_ss_ball : {(u : (Fin n) → α) | dist (Tuple.max (f ∘ u)) (fmax hf) > ε} ⊆
        {u | ∀ i, u i ∉ B} := by
      intro e (he : dist (Tuple.max (f ∘ e)) (fmax hf) > ε) i
      by_contra hcontra
      have le_lt : ∀ ⦃x⦄, x ≤ δ/2 → x < δ := fun _ hx => lt_of_le_of_lt hx (div_two_lt_of_pos hδ)
      specialize hdist (e i) hcontra
      rw [Compact.dist_max_compact hfc (e i)] at hdist

      obtain ⟨j, hj⟩ := Tuple.tuple_argmax f n_pos e
      rw [←hj] at he
      unfold fmax at he
      rw [Compact.dist_max_compact hfc (e j)] at he
      have : f (compact_argmax hfc) - f (e j) ≤ ε := by
        have ineq : f (e i) ≤ f (e j) := by
          rw [hj]
          exact Tuple.le_max (f ∘ e) n_pos i
        exact le_trans (tsub_le_tsub_left ineq _) hdist
      linarith

    suffices h' : {(u : (Fin n) → α) | ∀ i, u i ∉ B} ⊆ {u | max_min_dist u > δ} from
      fun _ ha ↦ h' (max_dist_ss_ball ha)

    intro u (hu : ∀ i, u i ∉ B)
    replace hu : ∀ i, dist (u i) x' > δ := fun i => lt_of_not_ge (hu i)
    obtain ⟨i, hi⟩ := Tuple.tuple_argmin (fun xi => dist xi x') n_pos u
    specialize hu i
    rw [hi] at hu
    have argmax_le : min_dist_x u x' ≤ max_min_dist u :=
      compact_argmax_apply (min_dist_x_continuous u) x'
    exact lt_of_le_of_lt' argmax_le hu

  · intro h f hf ε₁ ε₁_pos
    rw [←nstar_tendsto_iff_tendsto]
    set gε₁ := fun (n : nstar) => A.μ f n {u | max_min_dist u > ε₁}
    have antitone_gε₁ : Antitone gε₁ := by
      intro n m hnm
      let S := fun n => {(u : Fin n → α) | max_min_dist u > ε₁}
      suffices h : {(u : ℕ → α) | Tuple.toTuple m u ∈ S m} ⊆ {(u : ℕ → α) | Tuple.toTuple n u ∈ S n}
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
        lt_of_le_of_lt'
        (compact_argmax_apply (min_dist_x_continuous (toTuple n u)) x')
        (lt_of_lt_of_eq (lt_of_le_of_lt' h hu) hj)
      have le_min :=
        Tuple.le_min (f := (fun xi ↦ dist xi x') ∘ (toTuple m u)) m.2 ⟨j, Fin.val_lt_of_le j hnm⟩
      rwa [←hi] at le_min
    rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone antitone_gε₁]
    by_contra not_sample_space
    push_neg at not_sample_space
    obtain ⟨ε₂, ε₂_pos, not_sample_space⟩ := not_sample_space

    -- Step 1: Ball almost never hit by `A`. **RADIUS `ε₁/2` NOT `ε₁`!!!**

    -- To construct such a ball, we select an arbitrary finite cover of the universe.
    obtain ⟨t, t_card, h_cover⟩ := (ε_cover_ne (half_pos ε₁_pos) α).some_mem
    set N₁ := (ε_cover_ne (half_pos ε₁_pos) α).some

    /- We construct a ball for which the probability to never sample inside is
    strictly positive for all `n > 0`. -/
    obtain ⟨c, c_in_t, hc⟩ : ∃ c ∈ t, ∀ (n : nstar),
        ε₂/(2 * N₁) ≤ A.μ f n {u : Fin n → α | ∀ i, u i ∉ Metric.ball c (ε₁/2)} := by
      by_contra h_contra
      push_neg at h_contra
      /- We take the maximum of the choice function `f : t → ℕ`. -/
      replace h_contra : ∃ (n : nstar), ∀ c ∈ t,
        A.μ f n {u : Fin n → α | ∀ i, u i ∉ Metric.ball c (ε₁/2)} < ε₂/(2 * N₁) := by
        choose choice_fun h_contra using h_contra
        let choice_fun' := fun (c : t) => choice_fun c.1 c.2
        let n_max := Fintype.max_image choice_fun'
        use n_max
        intro c hc
        let S := fun n => {(u : Fin n → α) | ∀ i, u i ∉ Metric.ball c (ε₁/2)}
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
      suffices h : gε₁ n_max ≤ ε₂ / 2 from
        ENNReal.contra_ineq (measure_ne_top _ _) (not_sample_space n_max)
          (le_trans h ENNReal.half_le_self)

      set S := {(u : Fin n_max → α) | ∃ c ∈ t, ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁/2)}

      /- The set of iterations such that max_x min_(u i) dist (u i) x > ε₁ is included
      in a set of iterations that are outside of a specific ball. As `t` is a
      `ε₁`-cover of the universe, `∃ c ∈ t, x' := argmax_x min_(u i) dist (u i) x > ε₁ ∈ B(c, ε₁)`
      and thus, any point outside `B(c, ε₁)` is at least at `ε₁` away from `x'`. -/
      have le_μ_cover : gε₁ n_max ≤ A.μ f n_max S := by
        suffices h : {(u : Fin n_max → α) | max_min_dist u > ε₁} ⊆ S from (A.μ f n_max).mono h

        intro u (hu : max_min_dist u > ε₁)
        let x' := (compact_argmax (min_dist_x_continuous u))

        obtain ⟨c, c_in_t, hc⟩ : ∃ c ∈ t, x' ∈ Metric.ball c (ε₁/2) := by
          have x'_in_cover : x' ∈ ⋃ c ∈ t, Metric.ball c (ε₁/2) := by
            rw [←h_cover]
            trivial
          simp_all only [mem_iUnion, exists_prop]

        refine ⟨c, c_in_t, ?_⟩

        unfold max_min_dist min_dist_x at hu
        set m := Tuple.min ((fun xi ↦ dist xi x') ∘ u)

        intro i

        have : ε₁ < dist (u i) x' :=
          suffices h : m ≤ dist (u i) x' from lt_of_le_of_lt' h hu
          Tuple.le_min ((fun xi ↦ dist xi x') ∘ u) n_max.2 i

        by_contra h
        suffices dist (u i) x' < ε₁ by linarith
        calc dist (u i) x' ≤ dist (u i) c + dist c x' := dist_triangle (u i) c x'
          _ < ε₁/2 + dist c x' := (add_lt_add_iff_right _).mpr h
          _ = ε₁/2 + dist x' c := by rw [dist_comm c x']
          _ < ε₁/2 + ε₁/2 := (add_lt_add_iff_left _).mpr hc
          _ = ε₁ := by ring

      calc gε₁ n_max ≤ (A.μ f n_max) S := le_μ_cover
      _ ≤ A.μ f n_max (⋃ c ∈ t, {u | ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁/2)}) := by
        suffices h : S ⊆ ⋃ c ∈ t, {u | ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁/2)} from
          (A.μ f n_max).mono h
        rintro u ⟨c, hc, hu⟩
        rw [mem_iUnion]
        simp only [mem_iUnion, exists_prop]
        exact ⟨c, hc, hu⟩
      _ ≤ ∑ c ∈ t, A.μ f n_max {u | ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁/2)} :=
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

    have ratio_ε₂_pos : ε₂ / (2 * N₁) ≠ 0 :=
      have denom_pos : (2 * (N₁ : ℝ≥0∞))⁻¹ ≠ 0 :=
        suffices h : 2 * (N₁ : ℝ≥0∞) ≠ ⊤ from ENNReal.inv_ne_zero.mpr h
        mul_ne_top (ENNReal.ofNat_ne_top) (natCast_ne_top N₁)
      (mul_ne_zero_iff_right denom_pos).mpr <| pos_iff_ne_zero.mp ε₂_pos


    /- We define `f~` differently : we just want to ensure that it is maximized within
    `Metric.closedBall c (ε₁/2)`. This allows to show that it exists a `δ > 0` such that,
    for any `x ∉ Metric.closedBall c (ε₁/2)`, `|f~ x - f~ x^*| > δ`. The latter leads
    to a contradiction as the algorithm almost never samples in `Metric.closedBall c (ε₁/2)` and
    thus, cannot produce iterates that are `δ`-close to `f~ x^*`. -/
    have hfc := hf.continuous
    let f_tilde := hf.f_tilde c ε₁
    have hf_tilde : Lipschitz f_tilde := hf.f_tilde_lipschitz c ε₁_pos
    have hf_tildec := hf_tilde.continuous

    let x' := compact_argmax hf_tilde.continuous

    /- As we know that `max f < f~(c) ≤ max f~`, setting `δ := max f~ - max f > 0` gives
    that `∀ x ∉ B(x, ε₁/2), max f~ - f~(x) = max f~ - f(x) > max f~ - max f = δ`. -/
    obtain ⟨δ, δ_pos, hδ⟩ :
        ∃ δ > 0, ∀ x ∉ Metric.ball c (ε₁/2), dist (f_tilde x) (f_tilde x') > δ := by

      have x'_in_ball : x' ∈ Metric.ball c (ε₁/2) := by
        by_contra h_contra

        set fma := fmax hf
        set fmi := fmin hf

        have f_tilde_x'_lt_f_tilde_c : f_tilde x' < f_tilde c := by
          refine lt_of_le_of_lt ?_ (hf.max_f_lt_f_tilde_c c ε₁_pos)
          simp only [f_tilde, hf.f_tilde_apply_out c h_contra]
          exact compact_argmax_apply hfc x'

        have f_tilde_c_le_f_tilde_x' : f_tilde c ≤ f_tilde x' :=
          compact_argmax_apply hf_tildec c
        linarith

      set fma := fmax hf
      set fmi := fmin hf

      have f_tilde_max_gt_fma : 0 < f_tilde x' - fma := by
        suffices h : fma < f_tilde c by
          exact lt_of_le_of_lt'
            (tsub_le_tsub_right (compact_argmax_apply hf_tildec c) fma)
            (sub_pos.mpr h)
        simp only [f_tilde, hf.f_tilde_c c ε₁_pos]
        exact lt_add_of_pos_right fma (hf.pos_rhs_f_tilde_c c)

      have half_f_tilde_max_gt_fma := half_pos f_tilde_max_gt_fma

      refine ⟨(f_tilde x' - fma)/2, half_f_tilde_max_gt_fma, ?_⟩
      intro y hy
      rw [dist_comm]
      rw [show dist (f_tilde x') (f_tilde y) = |f_tilde x' - f_tilde y| by rfl]
      rw [abs_of_nonneg (sub_nonneg_of_le (compact_argmax_apply hf_tildec y))]
      simp only [f_tilde, hf.f_tilde_apply_out c hy]

      have fma_ge_fy : f_tilde x' - fma ≤ f_tilde x' - f y :=
        tsub_le_tsub_left (compact_argmax_apply hfc y) (f_tilde x')
      have half_distmax_lt_distmax : (f_tilde x' - fma) / 2 < f_tilde x' - fma :=
        div_two_lt_of_pos f_tilde_max_gt_fma

      exact lt_of_le_of_lt' fma_ge_fy half_distmax_lt_distmax

    /- We can now specialize the hypothesis, i.e., that the algorithm is consistent
    over continuous and non-constant functions, to `f~` and `δ`. -/

    specialize h hf_tilde δ_pos
    rw [←nstar_tendsto_iff_tendsto, ENNReal.tendsto_atTop_zero] at h
    obtain ⟨N, hN⟩ := h ((ε₂ / (2 * N₁)) / 2) (ENNReal.half_pos ratio_ε₂_pos)
    let N_succ : nstar := ⟨N.1 + 1, Nat.add_pos_left N.2 1⟩
    specialize hN N_succ (Nat.le_add_right N 1)
    specialize hc N_succ
    unfold measure_dist_max at hN

    /- Finally, if we succeed to show the following inequality, we will have that:
    1. `ε₂ / (2 * N₁)) / 2 < A.μ f (N+1) {u | ∀ i, u i ∉ Metric.ball c (ε₁/2)} ≤ A.μ f (N+1) {u | dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ}` (hc and subset hypothesis)

    2. `A.μ f (N+1) {u | dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ} ≤ ε₂ / (2 * N₁)) / 2` (hN) -/
    suffices h_suff : {(u : Fin N_succ → α) | ∀ i, u i ∉ Metric.ball c (ε₁/2)}
        ⊆ {u | dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ} by
      set B := {(u : Fin N_succ → α) | ∀ i, u i ∉ Metric.ball c (ε₁/2)}
      set C := {u | dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ}

      have measure_f_tilde_gt : (ε₂ / (2 * N₁)) / 2 < A.μ f_tilde N_succ C := by
        have mono : A.μ f_tilde N_succ B ≤ A.μ f_tilde N_succ C :=
          (A.μ f_tilde N_succ).mono h_suff

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

        /- We use the fact that, as `f and f~` are indistinguishable outside `B(c, ε₁/2)`,
        `A.μ f (N+1) {u | u ∉ B(c, ε₁/2)} = A.μ f~ (N+1) {u | u ∉ B(c, ε₁/2)}`
        (See `Algorithm.μ_eq_restrict` in `Algorithm.lean`). -/
        have measure_eq_f_set : A.μ f N_succ B = A.μ f_tilde N_succ B := by
          have μ_eq_restrict := by
            have f_eq_f_tilde : ∀ a ∈ (Metric.ball c (ε₁/2))ᶜ, f a = f_tilde a :=
              fun _ ha => (hf.f_tilde_apply_out c ha).symm
            exact A.μ_eq_restrict f_eq_f_tilde N_succ
          rwa [compl_compl] at μ_eq_restrict

        have measure_f_tilde_le : (ε₂ / (2 * N₁)) ≤ A.μ f_tilde N_succ B := by
          rwa [←measure_eq_f_set]
        exact lt_of_le_of_lt' mono (lt_of_le_of_lt' measure_f_tilde_le half_lt_ε₂)

      exact ENNReal.contra_ineq (measure_ne_top _ _) measure_f_tilde_gt hN

    -- This is given by the construction of `δ`.
    intro u hu
    obtain ⟨i, hi⟩ := tuple_argmax f_tilde N_succ.2 u
    show dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ
    rw [←hi]
    exact hδ (u i) (hu i)
