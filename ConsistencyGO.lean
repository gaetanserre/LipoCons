/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Defs.Consistency
import ConsistencyGO.Utils.Tendsto
import ConsistencyGO.Utils.Metric
import ConsistencyGO.Utils.ENNReal
import ConsistencyGO.Utils.Finset
import Mathlib

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
    obtain ⟨t, t_card, h_cover⟩ := (ε_cover_ne (half_pos ε₁_pos) α).some_mem
    set N₁ := (ε_cover_ne (half_pos ε₁_pos) α).some

    /- We construct a ball for which the probability to never sample inside is
    strictly positive for all `n > 0`. -/
    obtain ⟨c, c_in_t, hc⟩ : ∃ c ∈ t, ∀ (n : ℕ₀),
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
        ENNReal.contra_ineq (measure_ne_top _ _) (not_sample_space n_max)
          (le_trans h ENNReal.half_le_self)

      set S := {u : Fin n_max → α | ∃ c ∈ t, ∀ (i : Fin ↑n_max), u i ∉ Metric.ball c (ε₁/2)}

      /- The set of iterations such that `max_x min_(u i) dist (u i) x > ε₁` is included
      in a set of iterations that are outside of a specific ball. As `t` is a
      `ε₁`-cover of the universe, `∃ c ∈ t, max_x min_(u i) dist (u i) x > ε₁ ∈ B(c, ε₁)`
      and thus, any point outside `B(c, ε₁)` is at least at `ε₁` away from the argmax
      of the previous formula. -/
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
          rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt N₁.2))
            (natCast_ne_top ↑N₁), one_mul]
          rfl


    sorry
