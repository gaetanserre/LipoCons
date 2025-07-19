/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Defs.Consistency
import Mathlib

open Classical

namespace Lipschitz

variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompactSpace α]
  [Nonempty α] {f : α → ℝ} (hf : Lipschitz f) (c : α)

noncomputable def f_tilde (ε : ℝ) := fun x =>
  if x ∈ Metric.ball c (ε/2) then
    f x + 2 * ((1 - (dist x c) / (ε/2)) * (fmax hf - fmin hf + 1))
  else f x

omit [NormedSpace ℝ α] in
lemma f_tilde_apply_out {ε : ℝ} {x : α} (hx : x ∉ Metric.ball c (ε/2)) :
    hf.f_tilde c ε x = f x := by
  unfold f_tilde
  split
  · contradiction
  rfl

omit [NormedSpace ℝ α] in
lemma f_tilde_apply_in {ε : ℝ} {x : α} (hx : x ∈ Metric.ball c (ε/2)) :
    hf.f_tilde c ε x = f x + 2 * ((1 - (dist x c) / (ε/2)) * (fmax hf - fmin hf + 1)) := by
  unfold f_tilde
  split
  · rfl
  contradiction

omit [NormedSpace ℝ α] in
lemma f_tilde_c {ε : ℝ} (ε_pos : 0 < ε) :
    hf.f_tilde c ε c = fmax hf + ((f c - fmin hf) + (fmax hf - fmin hf) + 2) := by
  have c_in_ball : c ∈ Metric.ball c (ε/2) := Metric.mem_ball_self (half_pos ε_pos)
  rw [hf.f_tilde_apply_in c c_in_ball]
  rw [dist_self, zero_div]
  ring

omit [NormedSpace ℝ α] in
lemma pos_rhs_f_tilde_c : 0 < (f c - fmin hf) + (fmax hf - fmin hf) + 2 := by
  refine add_pos_of_nonneg_of_pos ?_ zero_lt_two
  exact Left.add_nonneg
    (sub_nonneg_of_le (compact_argmin_apply hf.continuous c))
    (compact_argmax_sub_argmin_pos hf.continuous)

omit [NormedSpace ℝ α] in
lemma max_f_lt_f_tilde_c {ε : ℝ} (ε_pos : 0 < ε) : fmax hf < hf.f_tilde c ε c := by
  rw [hf.f_tilde_c c ε_pos]
  exact lt_add_of_pos_right (fmax hf) (hf.pos_rhs_f_tilde_c c)

/- lemma f_tilde_continuous {ε : ℝ} (ε_pos : 0 < ε) : Continuous (hf.f_tilde c ε) := by
  refine Continuous.if ?_ ?_ hf
  · intro a (a_in_frontier : a ∈ frontier (Metric.ball c (ε/2)))
    have ne_zero : (ε/2) ≠ 0 := (ne_of_lt <| half_pos ε_pos).symm
    have := frontier_ball c ne_zero
    rw [frontier_ball c ne_zero] at a_in_frontier
    replace a_in_frontier : dist a c = (ε/2) := a_in_frontier
    rw [a_in_frontier]
    calc _ = f a + 2 * (1 - (ε / 2 / (ε/2))) * (fmax hf + 1 - (fmin hf - 1)) := by ring
    _ = f a + 2 * (1 - 1) * (fmax hf + 1 - (fmin hf - 1)) :=
      by rw [(div_eq_one_iff_eq ne_zero).mpr rfl]
    _ = f a + 2 * 0 * (fmax hf + 1 - (fmin hf - 1)) := by rw [sub_self 1]
    _ = f a := by ring
  fun_prop -/

open Set unitInterval

variable [PreconnectedSpace α]
lemma f_tilde_lipschitz {ε : ℝ} (ε_pos : 0 < ε) : Lipschitz (hf.f_tilde c ε) := by

  let w_dist := fun a => 2 * ((1 - (dist a c) / (ε/2)) * (fmax hf - fmin hf + 1))
  let g := f + w_dist

  have hw : Lipschitz w_dist := by
    refine const_mul ?_
    refine mul_const ?_
    refine sub lipschitz_const ?_
    exact div_const (dist_left c)

  let Kf := hf.isLipschitz.choose
  let Kw := hw.isLipschitz.choose

  have hg : LipschitzWith (Kf + Kw) g :=
    hf.isLipschitz.choose_spec.add hw.isLipschitz.choose_spec

  use (Kf + Kw)

  rw [lipschitzWith_iff_dist_le_mul]

  intro x y

  let p := fun x => x ∈ Metric.ball c (ε/2)

  by_cases h : ¬ p x ∧ ¬ p y
  · rw [hf.f_tilde_apply_out c h.1, hf.f_tilde_apply_out c h.2]
    have f_lipschitz := hf.isLipschitz.choose_spec
    rw [lipschitzWith_iff_dist_le_mul] at f_lipschitz
    specialize f_lipschitz x y
    suffices Kf * dist x y ≤ (Kf + Kw) * dist x y from le_trans f_lipschitz this
    have Kf_le_add : (Kf : ℝ) ≤ Kf + Kw := by
      show Kf ≤ Kf + Kw
      exact le_self_add
    refine mul_le_mul_of_nonneg Kf_le_add ?_ NNReal.zero_le_coe dist_nonneg
    rw [dist_comm]

  · by_cases h' : p x ∧ p y
    · rw [hf.f_tilde_apply_in c h'.1, hf.f_tilde_apply_in c h'.2]
      rw [lipschitzWith_iff_dist_le_mul] at hg
      exact hg x y
    · push_neg at h; push_neg at h'

      by_cases hx : ¬ p x
      · have hy := h hx
        rw [hf.f_tilde_apply_out c hx, hf.f_tilde_apply_in c hy]
        show |f x - g y| ≤ (Kf + Kw) * dist x y

        rw [abs_sub_comm]

        have : g y - f x = f y - f x + w_dist y := by
          simp only [Pi.add_apply, g]
          ring
        rw [this]

        have exists_btwn : ∃ e, e ∈ Metric.sphere c (ε/2) ∧ dist e y ≤ dist x y := by
          /- by_contra h_c
          push_neg at h_c -/
          by_cases x_mem_sphere : x ∈ Metric.sphere c (ε/2)
          · exact ⟨x, x_mem_sphere, le_refl _⟩
          · let ch := segment ℝ y x



            have : segment ℝ y x = segment ℝ x y := by exact segment_symm ℝ y x

            suffices ∃ e ∈ segment ℝ y x, e ∈ Metric.sphere c (ε/2) by
              obtain ⟨e, e_mem⟩ := this
              refine ⟨e, e_mem.2, ?_⟩
              rw [NormedAddGroup.dist_eq e y, NormedAddGroup.dist_eq x y]
              exact norm_sub_le_of_mem_segment e_mem.1

            let i := λ t : I => (1 - t.1) • y + t.1 • x

            have : Continuous (fun t => dist (i t) c) := by fun_prop

            have int := intermediate_value_univ 0 1 this

            have : dist (i 0) c = dist y c := by
              suffices i 0 = y by rw [this]
              simp only [Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero, i]

            rw [this] at int
            clear this

            have : dist (i 1) c = dist x c := by
              suffices i 1 = x by rw [this]
              simp only [Icc.coe_one, sub_self, zero_smul, one_smul, zero_add, i]
            rw [this] at int
            clear this

            have : (ε / 2) ∈ Icc (dist y c) (dist x c) := by
              suffices h : Icc (ε / 2) (ε / 2) ⊆ Icc (dist y c) (dist x c) by
                have : (ε / 2) ∈ Icc (ε / 2) (ε / 2) := ⟨le_refl _, le_refl _⟩
                exact h this
              refine Icc_subset_Icc ?_ ?_
              · exact le_of_lt hy
              simp only [Metric.mem_ball, gt_iff_lt, not_lt, p] at hx
              exact hx

            obtain ⟨t, ht⟩ := int this

            have ttt : {z | ∃ t ∈ Icc (0 : ℝ) 1, z = (1 - t) • y + t • x} ⊆ segment ℝ y x := by
              rintro z ⟨t, t_mem, ht⟩
              exact ⟨1 - t, t, sub_nonneg_of_le t_mem.2, t_mem.1, (by ring), ht.symm⟩

            refine ⟨i t, ?_, ?_⟩
            · exact ttt ⟨t, Subtype.coe_prop t, rfl⟩
            exact ht


        let e := exists_btwn.choose

        calc _ ≤ |f y - f x| + |w_dist y| := abs_add_le _ _
        _ ≤ Kf * dist y x + |w_dist y| := by
          have f_lipschitz := hf.isLipschitz.choose_spec
          rw [lipschitzWith_iff_dist_le_mul] at f_lipschitz
          exact add_le_add_right (f_lipschitz y x) _
        _ = Kf * dist x y + |w_dist y| := by rw [dist_comm]
        _ = Kf * dist x y + |w_dist y - w_dist e| := by
          have : dist e c = ε/2 := exists_btwn.choose_spec.1
          simp only [add_right_inj, w_dist]
          rw [this]
          have : ε / 2 / (ε / 2) = 1 :=
          CommGroupWithZero.mul_inv_cancel _ (ne_of_lt <| half_pos ε_pos).symm
          rw [this, sub_self]
          simp only [zero_mul, mul_zero, sub_zero]
        _ ≤ Kf * dist x y + Kw * dist y e := by
          have w_lipschitz := hw.isLipschitz.choose_spec
          rw [lipschitzWith_iff_dist_le_mul] at w_lipschitz
          exact add_le_add_left (w_lipschitz y e) (Kf * dist x y)
        _ ≤ ↑Kf * dist x y + ↑Kw * dist x y := by

          have : Kw * dist y e ≤ ↑Kw * dist x y := by
            rw [dist_comm]
            exact mul_le_mul_of_nonneg
              (le_refl _) exists_btwn.choose_spec.2 (NNReal.zero_le_coe) (dist_nonneg)
          exact (add_le_add_iff_left _).mpr this
        _ = (Kf + Kw) * dist x y := by ring

      · sorry

end Lipschitz
