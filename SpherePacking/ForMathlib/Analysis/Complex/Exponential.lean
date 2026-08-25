/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib

@[expose] public section

namespace Real

theorem exp_decay (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : x ^ k * rexp (-k * x) ≤ 1 := by
  rw [neg_mul_comm, exp_nat_mul, ← mul_pow x (rexp (-x)) k]
  refine pow_le_one₀ (by positivity) ?_
  calc x * rexp (-x)
    _ ≤ rexp x * rexp (-x) := by
      gcongr
      linarith [add_one_le_exp x]
    _ = 1 := by simp [← exp_add]

theorem exp_neg_mul_decay (k : ℕ) {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * rexp (-r * x) ≤ (k / r) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul, Nat.cast_zero]
    exact exp_le_one_iff.2 (by nlinarith)
  · have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    calc x ^ k * rexp (-r * x)
      _ = (k / r) ^ k * ((r * x / k) ^ k * rexp (-k * (r * x / k))) := by
          rw [← mul_assoc, ← mul_pow]
          congr 2
          · field_simp
          · field_simp
      _ ≤ (k / r) ^ k * 1 := by
          have := exp_decay k (x := r * x / k) (by positivity)
          gcongr (k / r) ^ k * ?_
      _ = (k / r) ^ k := mul_one _

end Real
