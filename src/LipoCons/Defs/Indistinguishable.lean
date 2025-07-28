/-
 - Created in 2025 by Gaëtan Serré
-/

import LipoCons.Defs.Consistency

open Classical Metric

namespace Lipschitz

variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α] [CompactSpace α]
  [Nonempty α] {f : α → ℝ} (hf : Lipschitz f) (c : α)

/-- Given a `Lipschitz` function `f` over a `CompactSpace α`, construct a `Lipschitz`
function (see `Lipschitz.f_tilde_lipschitz`) that is indistinguishable from `f` outside
of a ball of radius `ε` such that the maximum of this new function is greater than the
maximum of `f` and is located in the ball. -/
-- ANCHOR: f_tilde
noncomputable def f_tilde (ε : ℝ) := fun x =>
  if x ∈ ball c (ε/2) then
    f x + 2 * ((1 - (dist x c) / (ε/2)) * (fmax hf - fmin hf + 1))
  else f x
-- ANCHOR_END: f_tilde

omit [NormedSpace ℝ α] in
lemma f_tilde_apply_out {ε : ℝ} {x : α} (hx : x ∉ ball c (ε/2)) :
    hf.f_tilde c ε x = f x := by
  simp only [f_tilde, if_neg hx]

omit [NormedSpace ℝ α] in
lemma f_tilde_apply_in {ε : ℝ} {x : α} (hx : x ∈ ball c (ε/2)) :
    hf.f_tilde c ε x = f x + 2 * ((1 - (dist x c) / (ε/2)) * (fmax hf - fmin hf + 1)) := by
  simp only [f_tilde, if_pos hx]

omit [NormedSpace ℝ α] in
lemma f_tilde_c {ε : ℝ} (ε_pos : 0 < ε) :
    hf.f_tilde c ε c = fmax hf + ((f c - fmin hf) + (fmax hf - fmin hf) + 2) := by
  have c_in_ball : c ∈ ball c (ε/2) := mem_ball_self (half_pos ε_pos)
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

open Set unitInterval

-- ANCHOR: f_tilde_lipschitz
lemma f_tilde_lipschitz {ε : ℝ} (ε_pos : 0 < ε) : Lipschitz (hf.f_tilde c ε) := by
  refine hf.if ?_ ?_
  · intro a ha
    rw [ha]
    suffices h : ε / 2 / (ε / 2) = 1 by
      rw [h]
      ring
    exact CommGroupWithZero.mul_inv_cancel _ ((ne_of_lt (half_pos ε_pos)).symm)
  · refine const_mul <| mul_const <| sub lipschitz_const ?_
    exact div_const (dist_left c)
-- ANCHOR_END: f_tilde_lipschitz

-- ANCHOR: max_f_lt_max_f_tilde
lemma max_f_lt_max_f_tilde {ε : ℝ} (ε_pos : 0 < ε) :
    fmax hf < fmax (hf.f_tilde_lipschitz c ε_pos) :=
  suffices h : fmax hf < hf.f_tilde c ε c from
    lt_of_le_of_lt' (compact_argmax_apply (hf.f_tilde_lipschitz c ε_pos).continuous c) h
  hf.max_f_lt_f_tilde_c c ε_pos
-- ANCHOR_END: max_f_lt_max_f_tilde

-- ANCHOR: max_f_tilde_in_ball
lemma max_f_tilde_in_ball {ε : ℝ} (ε_pos : 0 < ε) :
    compact_argmax (hf.f_tilde_lipschitz c ε_pos).continuous ∈ ball c (ε/2) := by
  set x' := compact_argmax (hf.f_tilde_lipschitz c ε_pos).continuous
  by_contra h_contra
  have : fmax (hf.f_tilde_lipschitz c ε_pos) ≤ fmax hf := by
    simp only [fmax, hf.f_tilde_apply_out c h_contra, x']
    exact compact_argmax_apply hf.continuous x'
  have := hf.max_f_lt_max_f_tilde c ε_pos
  linarith
-- ANCHOR_END: max_f_tilde_in_ball

end Lipschitz
