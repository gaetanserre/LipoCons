/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib

namespace List

def mk (n : ℕ) : List ℕ :=
   if n = 0 then nil
   else n :: (mk (n - 1))

variable (n : ℕ)

lemma mk_zero : mk 0 = nil := by
  simp only [mk, ↓reduceIte]

lemma mk_decomp {n : ℕ} (hn : n ≠ 0) : mk n = n :: (mk (n - 1)) := by
  rw [mk.eq_def]
  split
  · contradiction
  rfl

lemma mk_le {a : ℕ} : a ∈ mk n → a ≤ n := by
  intro ha
  induction n with
  | zero =>
    rw [mk_zero] at ha
    contradiction
  | succ m hm =>
    rw [mk_decomp (Nat.zero_ne_add_one m).symm] at ha
    cases mem_cons.mp ha with
    | inl ha =>
      exact Nat.le_of_eq ha
    | inr ha =>
      specialize hm ha
      exact Nat.le_add_right_of_le hm

lemma mk_nodup : (mk n).Nodup := by
  induction n with
  | zero =>
    rw [mk_zero]
    exact nodup_nil
  | succ m hm =>
    rw [mk_decomp (Nat.zero_ne_add_one m).symm]
    simp only [Nodup, pairwise_cons]
    refine ⟨?_, hm⟩
    intro a a_mem
    suffices a < m + 1 from (Nat.ne_of_lt this).symm
    exact Order.lt_add_one_iff.mpr (mk_le m a_mem)

lemma mk_length : (mk n).length = n := by
  induction n with
  | zero =>
    simp only [mk, ↓reduceIte, List.length_nil]
  | succ m hm =>
    rw [mk.eq_def]
    split
    · have : m + 1 ≠ 0 := (Nat.zero_ne_add_one m).symm
      contradiction
    · have : ((m + 1) :: mk (m + 1 - 1)).length = (mk (m + 1 - 1)).length + 1 := by
        exact rfl
      rw [this]
      have : m + 1 - 1 = m := rfl
      rw [this, hm]

end List
