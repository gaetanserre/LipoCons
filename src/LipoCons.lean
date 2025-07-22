/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Utils.ECover
import LipoCons.Utils.ENNReal
import LipoCons.Utils.Finset
import LipoCons.Utils.Indistinguishable
import LipoCons.Utils.Metric
import LipoCons.Utils.Tendsto
import Mathlib.Analysis.RCLike.Basic

/-! Here, we prove that an iterative stochastic global optimization algorithm
is consistent over Lipschitz functions if and only if it, for any Lipschitz function,
it samples the whole space.
Please refer to
- `Algorithm` for the definition of an algorithm;
- `sample_whole_space` for the definition of sampling the whole space;
- `isConsistentOverLipschitz` for the definition of consistency over Lipschitz functions;
- `Lipschitz` for the definition of Lipschitz functions. -/

open Metric Tuple MeasureTheory Set ENNReal

variable {α : Type*} [MeasurableSpace α] [NormedAddCommGroup α] [NormedSpace ℝ α]
  [CompactSpace α] [Nonempty α]

theorem sample_iff_consistent (A : Algorithm α ℝ) :
    (∀ ⦃f : α → ℝ⦄, Lipschitz f → sample_whole_space A f)
    ↔
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → isConsistentOverLipschitz A hf) := by
  constructor
  · intro h f hf ε ε_pos
    have hfc := hf.continuous

    /- As we know by hypothesis that `(A.μ f n) {u | max_min_dist u > δ}` tends to `0`,
    it is enough to show that `set_dist_max hf ε` is a subset of `{u | max_min_dist u > δ}`
    and we conclude by using the squeeze theorem. -/
    suffices h' : ∃ δ > 0, ∀ n > 0, set_dist_max hf ε ⊆ {u : Fin n → α | max_min_dist u > δ} by
      obtain ⟨δ, hδ, h'⟩ := h'
      have μ_mono : ∀ n > 0, measure_dist_max A hf ε n ≤ (A.μ f n) {u | max_min_dist u > δ} :=
        fun n hn => (A.μ f n).mono (h' n hn)
      exact (h hf δ hδ).tendsto_zero_le_nat μ_mono

    /- We use the continuity of `f` to show that, there exists a `δ > 0`
    such that, for any `y`, `dist x' y ≤ δ → dist (f x') (f y) ≤ ε`. -/
    let x' := compact_argmax hfc
    obtain ⟨δ, hδ, hdist⟩ := continuous_iff_le.mp hfc x' ε ε_pos
    let B := closedBall x' δ
    refine ⟨δ, hδ, ?_⟩
    intro n n_pos

    /- We show that a sequence produced by `A` such that its maximum image by `f` is
    greater than `ε` has all its elements outside of the closed ball centered in `x'`
    of radius `δ`. Otherwise, by continuity of `f`, the maximum image of this sequence
    would be `ε`-close to `f x'`. -/
    have max_dist_ss_ball : set_dist_max hf ε ⊆ {u : Fin n → α | ∀ i, u i ∉ B} := by
      intro e (he : dist (Tuple.max (f ∘ e)) (fmax hf) > ε) i
      by_contra hcontra
      have le_lt_half : ∀ ⦃x⦄, x ≤ δ/2 → x < δ :=
          fun _ hx => lt_of_le_of_lt hx (div_two_lt_of_pos hδ)
      specialize hdist (e i) hcontra
      rw [dist_max_compact hfc (e i)] at hdist

      obtain ⟨j, hj⟩ := tuple_argmax f n_pos e
      rw [←hj] at he
      unfold fmax at he
      rw [dist_max_compact hfc (e j)] at he
      have : f (compact_argmax hfc) - f (e j) ≤ ε := by
        have ineq : f (e i) ≤ f (e j) := by
          rw [hj]
          exact le_max (f ∘ e) n_pos i
        exact le_trans (tsub_le_tsub_left ineq _) hdist
      linarith

    /- We know have that any sequence of `set_dist_max hf ε` has all its elements
    outside of `B`. It means that the max-min distance between any element of `α`
    and a sequence of `set_dist_max hf ε` is greater than `δ` as the minimum
    distance between `x'` and any element of such a sequence greater than `δ`. -/
    suffices h' : {u : (Fin n) → α | ∀ i, u i ∉ B} ⊆ {u | max_min_dist u > δ} from
      fun _ ha ↦ h' (max_dist_ss_ball ha)

    intro u hu
    replace hu : ∀ i, dist (u i) x' > δ := fun i => lt_of_not_ge (hu i)
    obtain ⟨i, hi⟩ := tuple_argmin (fun xi => dist xi x') n_pos u
    specialize hu i
    rw [hi] at hu
    have argmax_le : min_dist_x u x' ≤ max_min_dist u :=
      compact_argmax_apply (min_dist_x_continuous u) x'
    exact lt_of_le_of_lt' argmax_le hu

  · intro h f hf ε₁ ε₁_pos
    rw [←Filter.Tendsto.nstar_tendsto_iff_tendsto]
    set gε₁ := fun (n : ℕ₀) => A.μ f n {u | max_min_dist u > ε₁}
    /- We show that `gε₁` in order to change the goal to show that for any positive
    `ε`, it exists a `n : ℕ₀` such that `g ε₁ < ε`. -/
    rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone ?_]
    swap
    · /- The function `gε₁` is antitone as, for any `n ≤ m`, the set of sequence of size `m`
      such that their max-min distance between any element of `α` and their elements is greater
      than `ε₁` is included in the set of sequence of size `n` with the same property.
      We use `Algorithm.μ_mono` to show that this inclusion implies the inequality. -/
      intro n m hnm
      let S := fun n => {u : Fin n → α | max_min_dist u > ε₁}
      suffices h : {u : ℕ → α | toTuple m u ∈ S m} ⊆ {u | Tuple.toTuple n u ∈ S n}
        from A.μ_mono f h
      intro u (hu : max_min_dist (toTuple m u) > ε₁)
      unfold max_min_dist min_dist_x at hu
      set x' := compact_argmax (min_dist_x_continuous (toTuple m u))
      obtain ⟨i, hi⟩ :=
        tuple_argmin (f := (fun xi ↦ dist xi x')) m.2 (toTuple m u)
      rw [←hi] at hu
      obtain ⟨j, hj⟩ :=
        tuple_argmin (f := (fun xi ↦ dist xi x')) n.2 (toTuple n u)

      suffices h : dist (toTuple m u i) x' ≤ dist (toTuple n u j) x' from
        lt_of_le_of_lt'
        (compact_argmax_apply (min_dist_x_continuous (toTuple n u)) x')
        (lt_of_lt_of_eq (lt_of_le_of_lt' h hu) hj)
      have le_min :=
        Tuple.le_min (f := (fun xi ↦ dist xi x') ∘ (toTuple m u)) m.2 ⟨j, Fin.val_lt_of_le j hnm⟩
      rwa [←hi] at le_min

    /- We suppose by contradiction that there exists a `ε₂ > 0` such that the measure
    of `{u | max_min_dist u > ε₁}` is greater than `ε₂` for all `n`. That means that
    there exists a ball of radius `ε₁/2` such that, for any `n`, the measure of
    the set of sequences of size `n` such that all elements of the sequences belong
    to this ball is positive. -/
    by_contra not_sample_space
    push_neg at not_sample_space
    obtain ⟨ε₂, ε₂_pos, not_sample_space⟩ := not_sample_space

    -- Ball almost never hit by `A`. **RADIUS `ε₁/2` NOT `ε₁`!!!**

    -- To construct such a ball, we first select an arbitrary finite `ε₁`-cover of the universe.
    obtain ⟨t, t_card, h_cover⟩ := (ε_cover_ne α (half_pos ε₁_pos)).some_mem
    set N₁ := (ε_cover_ne α (half_pos ε₁_pos)).some

    /- We construct a ball for which the probability to never sample inside is
    strictly positive for all `n > 0`. -/
    obtain ⟨c, c_mem_t, hc⟩ : ∃ c ∈ t, ∀ (n : ℕ₀),
        ε₂/(2 * N₁) ≤ A.μ f n {u : Fin n → α | ∀ i, u i ∉ Metric.ball c (ε₁/2)} := by
      by_contra h_contra
      push_neg at h_contra

      /- We take the maximum image of the choice function `f : t → ℕ₀`. -/
      replace h_contra : ∃ (n : ℕ₀), ∀ c ∈ t,
          A.μ f n {u : Fin n → α | ∀ i, u i ∉ Metric.ball c (ε₁/2)} < ε₂/(2 * N₁) := by
        refine Finset.extract_mono (Finset.card_pos.mp ?_) _ h_contra ?_
        · rw [t_card]
          exact N₁.2
        · intro c c_mem n m hnm hn
          let S := fun n => {u : Fin n → α | ∀ i, u i ∉ Metric.ball c (ε₁/2)}
          suffices h : {u | toTuple m u ∈ S m} ⊆ {u | toTuple n u ∈ S n} from
            lt_of_le_of_lt (A.μ_mono f h) hn
          exact fun _ hu i => hu ⟨i.1, Fin.val_lt_of_le i hnm⟩

      obtain ⟨n_max, hn_max⟩ := h_contra
      suffices h : gε₁ n_max ≤ ε₂ / 2 from
        ENNReal.contra_ineq (not_sample_space n_max) (le_trans h ENNReal.half_le_self)

      set S := {u : Fin n_max → α | ∃ c ∈ t, ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁/2)}

      /- The set of iterations such that `max_x min_(u i) dist (u i) x > ε₁` is included
      in a set of iterations that are outside of a specific ball. As `t` is a
      `ε₁`-cover of the universe, it exists a `c ∈ t` such that the argmax `x'` of
      `max_x min_(u i) dist (u i) x` is in `B(c, ε₁/2)`. Then, for any sequence in
      the set `{u | max_min_dist u > ε₁}`, its elements are more than `ε₁` away
      from `x'`. This implies that its elements are not in `B(c, ε₁/2)`,
      since the distance between any points in `B(c, ε₁/2)` is at most `ε₁`. -/
      have le_μ_cover : gε₁ n_max ≤ A.μ f n_max S := by
        suffices h : {u : Fin n_max → α | max_min_dist u > ε₁} ⊆ S from (A.μ f n_max).mono h

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

        by_contra h
        suffices dist (u i) x' < ε₁ by
          have : ε₁ < dist (u i) x' :=
            suffices h : m ≤ dist (u i) x' from lt_of_le_of_lt' h hu
            Tuple.le_min ((fun xi ↦ dist xi x') ∘ u) n_max.2 i
          linarith
        calc _ ≤ dist (u i) c + dist c x' := dist_triangle (u i) c x'
          _ < ε₁/2 + dist c x' := (add_lt_add_iff_right _).mpr h
          _ = ε₁/2 + dist x' c := by rw [dist_comm c x']
          _ < ε₁/2 + ε₁/2 := (add_lt_add_iff_left _).mpr hc
          _ = ε₁ := by ring

      calc _ ≤ (A.μ f n_max) S := le_μ_cover
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
          rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt N₁.2))
            (natCast_ne_top ↑N₁), one_mul]
          rfl

    /- A useful result that we will need later. -/
    have ratio_ε₂_pos : ε₂ / (2 * N₁) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨(ne_of_lt ε₂_pos).symm, (not_eq_of_beq_eq_false rfl)⟩

    /- We now construct a function Lipschitz `f~` that is indistinguishable from `f`
    outside of `B(c, ε₁/2)` and that is maximized over this ball.
    Its maximum is greater than the maximum of `f`. The idea is to use the fact that
    probability of `A` not sampling in `Metric.ball c (ε₁/2)` is positive and therefore,
    the probability of `A` to not find a point arbitrarily close to the maximum of `f~`
    is also positive. This is a contradiction with the hypothesis that `A` is consistent
    over Lipschitz functions. -/

    have hfc := hf.continuous
    let f_tilde := hf.f_tilde c ε₁
    have hf_tilde : Lipschitz f_tilde := hf.f_tilde_lipschitz c ε₁_pos
    have hf_tildec := hf_tilde.continuous

    let x' := compact_argmax hf_tilde.continuous

    /- This construction of `f~` allows us to show that, as `max f < f~(c) ≤ max f~`,
    setting `δ := (max f~ - max f) / 2 > 0` gives that for any `x ∉ B(c, ε₁/2)`,
    `max f~ - f~(x) = max f~ - f(x) ≥ max f~ - max f = 2δ > δ`. This will be useful to
    that `A` is not consistent over `f~`. -/
    obtain ⟨δ, δ_pos, hδ⟩ :
        ∃ δ > 0, ∀ x ∉ Metric.ball c (ε₁/2), dist (f_tilde x) (f_tilde x') > δ := by

      /- As `max f < f~ c ≤ f~ x'`, `x'` must belong in `B(c, ε₁/2)`
      otherwise, `f~ x' = f x' ≤ max f` which is a contradiction. -/
      have x'_in_ball : x' ∈ Metric.ball c (ε₁/2) := by
        by_contra h_contra

        have f_tilde_x'_lt_f_tilde_c : f_tilde x' < f_tilde c := by
          refine lt_of_le_of_lt ?_ (hf.max_f_lt_f_tilde_c c ε₁_pos)
          simp only [f_tilde, hf.f_tilde_apply_out c h_contra]
          exact compact_argmax_apply hfc x'

        have f_tilde_c_le_f_tilde_x' : f_tilde c ≤ f_tilde x' :=
          compact_argmax_apply hf_tildec c
        linarith

      set fma := fmax hf
      have f_tilde_max_gt_fma : 0 < f_tilde x' - fma :=
        suffices fma < f_tilde x' from sub_pos.mpr this
        hf.max_f_lt_max_f_tilde c ε₁_pos

      refine ⟨(f_tilde x' - fma)/2, half_pos f_tilde_max_gt_fma, ?_⟩
      intro y hy
      rw [dist_comm]
      rw [show dist (f_tilde x') (f_tilde y) = |f_tilde x' - f_tilde y| by rfl]
      rw [abs_of_nonneg (sub_nonneg_of_le (compact_argmax_apply hf_tildec y))]
      simp only [f_tilde, hf.f_tilde_apply_out c hy]

      apply lt_of_le_of_lt' (b := f_tilde x' - fma)
      · exact tsub_le_tsub_left (compact_argmax_apply hfc y) (f_tilde x')
      · exact div_two_lt_of_pos f_tilde_max_gt_fma

    /- We can now specialize the hypothesis, i.e., that the algorithm is consistent
    over continuous and non-constant functions, to `f~` and `δ`. -/
    specialize h hf_tilde δ_pos
    rw [←Filter.Tendsto.nstar_tendsto_iff_tendsto, ENNReal.tendsto_atTop_zero] at h
    obtain ⟨N, hN⟩ := h ((ε₂ / (2 * N₁)) / 2) (ENNReal.half_pos ratio_ε₂_pos)
    let N_succ : ℕ₀ := ⟨N + 1, Nat.add_pos_left N.2 1⟩
    specialize hN N_succ (Nat.le_add_right N 1)
    specialize hc N_succ
    unfold measure_dist_max at hN

    set S := {u : Fin N_succ → α | ∀ i, u i ∉ Metric.ball c (ε₁/2)}
    set E := set_dist_max hf_tilde δ

    /- Finally, it is enough to show that any sequence that does not belong in `B(c, ε₁/2)`
    failed to approximate `x'` with a `delta` precision. Indeed, we know by consistency
    hypothesis that `(A.μ f~ ↑N_succ) C ≤ ε₂ / (4 * N₁)`. Moreover, we constructed
    the ball `B(c, ε₁/2)` such that the measure of the set of sequences generated by `A`
    over `f` that do not belong to this ball is greater or equal to `ε₂ / (2 * N₁)`,
    implying that it is smaller than `ε₂ / (4 * N₁)`. To summarize, we have
    1. `A.μ f~ N_succ E ≤ ε₂ / (4 * N₁)`
    2. `ε₂ / (4 * N₁) < (A.μ f N_succ) S`
    Using the fact that `f` and `f~` are indistinguishable outside of `B(c, ε₁/2)`,
    the inequality (2) becomes
    2. `ε₂ / (4 * N₁) < (A.μ f~ N_succ) S`.
    If we can show that `S` is included in `E`, we conclude that
    `ε₂ / (4 * N₁) < (A.μ f~ N_succ) S ≤ (A.μ f~ N_succ) E`,
    which contradicts the inequality (1). -/
    suffices h_suff : S ⊆ E by
      refine ENNReal.contra_ineq ?_ hN
      have mono : A.μ f_tilde N_succ S ≤ A.μ f_tilde N_succ E :=
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
      have measure_eq_f_set : A.μ f N_succ S = A.μ f_tilde N_succ S := by
        have μ_eq_restrict :=
          have f_eq_f_tilde : ∀ a ∈ (Metric.ball c (ε₁/2))ᶜ, f a = f_tilde a :=
            fun _ ha => (hf.f_tilde_apply_out c ha).symm
          A.μ_eq_restrict f_eq_f_tilde N_succ
        rwa [compl_compl] at μ_eq_restrict

      rw [measure_eq_f_set] at hc
      exact lt_of_le_of_lt' mono (lt_of_le_of_lt' hc half_lt_ε₂)

    -- This is given by the construction of `δ`.
    intro u hu
    obtain ⟨i, hi⟩ := tuple_argmax f_tilde N_succ.2 u
    show dist (Tuple.max (f_tilde ∘ u)) (fmax hf_tilde) > δ
    rw [←hi]
    exact hδ (u i) (hu i)

/-- Duplicate of `sample_iff_consistent` without the proof to include it in the Verso website. -/
-- ANCHOR: thm_sample_iff_consistent
theorem sample_iff_consistent' (A : Algorithm α ℝ) :
    (∀ ⦃f : α → ℝ⦄, Lipschitz f → sample_whole_space A f)
    ↔
    (∀ ⦃f : α → ℝ⦄, (hf : Lipschitz f) → isConsistentOverLipschitz A hf) := by
  sorry
-- ANCHOR_END: thm_sample_iff_consistent
