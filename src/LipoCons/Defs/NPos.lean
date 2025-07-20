/-
 - Created in 2025 by Gaëtan Serré
-/

import Mathlib.Data.Nat.Notation

/-! The subtype of positive natural numbers. -/
abbrev nat_pos := {n : ℕ // 0 < n}
notation "ℕ₀" => nat_pos
