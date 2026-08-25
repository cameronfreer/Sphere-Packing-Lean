/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib

@[expose] public section

namespace Real

theorem exp_decay {k : ℝ} (hk : 0 ≤ k) : ∃ C : ℝ, ∀ x ≥ 0, |x| ^ k * |exp (-k * x)| ≤ C := by
  refine ⟨1, fun x hx => ?_⟩
  have hx' : (0:ℝ) ≤ exp (-x) := (exp_pos _).le
  rw [abs_of_nonneg hx, abs_of_pos (exp_pos _), show -k * x = -x * k by ring, exp_mul,
    ← mul_rpow hx hx']
  refine rpow_le_one (by positivity) ?_ hk
  calc x * exp (-x) ≤ exp x * exp (-x) := by
        gcongr
        linarith [add_one_le_exp x]
    _ = 1 := by rw [← exp_add]; simp

end Real
