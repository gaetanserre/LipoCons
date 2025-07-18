/-
 - Created in 2025 by Gaëtan Serré
-/

import ConsistencyGO.Defs.Consistency
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.RCLike.Basic

open Classical

namespace Continuous

variable {α : Type*} [SeminormedAddCommGroup α] [NormedSpace ℝ α] [CompactSpace α] [Nonempty α]
  {f : α → ℝ} (hf : Continuous f) (c : α)

noncomputable def f_tilde (ε : ℝ) := fun x =>
  if x ∈ Metric.ball c (ε/2) then
    f x + 2 * (1 - (dist x c) / (ε/2)) * ((fmax hf + 1) - (fmin hf - 1))
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
    hf.f_tilde c ε x = f x + 2 * (1 - (dist x c) / (ε/2)) * ((fmax hf + 1) - (fmin hf - 1)) := by
  unfold f_tilde
  split
  · rfl
  contradiction

omit [NormedSpace ℝ α] in
lemma f_tilde_c {ε : ℝ} (ε_pos : 0 < ε) :
    hf.f_tilde c ε c = fmax hf + (1 + (f c - fmin hf + 1) + (fmax hf - fmin hf + 2)) := by
  have c_in_ball : c ∈ Metric.ball c (ε/2) := Metric.mem_ball_self (half_pos ε_pos)
  rw [hf.f_tilde_apply_in c c_in_ball]
  rw [dist_self, zero_div]
  ring

omit [NormedSpace ℝ α] in
lemma pos_rhs_f_tilde_c : 0 < 1 + (f c - fmin hf + 1) + (fmax hf - fmin hf + 2) := by
  refine add_pos_of_nonneg_of_pos (Left.add_nonneg (zero_le_one' ℝ) ?_) ?_
  · exact Left.add_nonneg (sub_nonneg_of_le (compact_argmin_apply hf c)) (zero_le_one' ℝ)
  have : 0 ≤ fmax hf - fmin hf := compact_argmax_sub_argmin_pos hf
  exact add_pos_of_nonneg_of_pos this zero_lt_two

omit [NormedSpace ℝ α] in
lemma max_f_lt_f_tilde_c {ε : ℝ} (ε_pos : 0 < ε) : fmax hf < hf.f_tilde c ε c := by
  rw [hf.f_tilde_c c ε_pos]
  exact lt_add_of_pos_right (fmax hf) (hf.pos_rhs_f_tilde_c c)

lemma f_tilde_continuous {ε : ℝ} (ε_pos : 0 < ε) : Continuous (hf.f_tilde c ε) := by
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

  refine hf.add ?_
  refine mul ?_ continuous_const
  refine mul continuous_const ?_
  refine sub continuous_const ?_
  refine div_const ?_ _
  exact .dist continuous_id continuous_const

end Continuous
