/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import Mathlib
public import SpherePacking.ForMathlib.Analysis.Complex.Exponential

namespace MagicFunction

open Real MeasureTheory Set Nat

theorem pow_mul_integral_le {r : ℝ} (hr : 0 ≤ r) {n : ℕ} :
    r ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s) ≤
      (n / π) ^ n * (n)! / (2 * π) ^ n := calc
  _ = ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * (r ^ n * rexp (-π * r / s)) := by
      simp only [← smul_eq_mul (a := r ^ n), ← integral_smul]
      grind [smul_eq_mul (a := r ^ n)]
  _ ≤ ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * ((n / π) ^ n * s ^ n) := by
      refine setIntegral_mono_of_nonneg ?_ ?_ ?_
      · intro _ hs
        rw [mem_Ici] at hs
        positivity
      · intro s hs
        rw [mem_Ici] at hs
        gcongr 1
        rw [← mul_inv_le_iff₀ (by positivity)]
        calc
        _ = r ^ n * (s ^ n)⁻¹ * rexp (-π * (r / s)) := by ring_nf
        _ = (r / s) ^ n * rexp (-π * (r / s)) := by
            rw [div_pow]
            congr
        _ ≤ _ := exp_neg_mul_decay n pi_pos (x := r / s) <| by positivity
      · sorry
  _ ≤ (n / π) ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * s ^ n := sorry
  _ ≤ (n / π) ^ n * ∫ s in Ici (0 : ℝ), rexp (-2 * π * s) * s ^ n := sorry
  _ = (n / π) ^ n * ∫ s in Ici (0 : ℝ), 1 / (2 * π) ^ (n + 1) * rexp (-2 * π * s) * (2 * π * s) ^ n
      := sorry
  _ = (n / π) ^ n * Gamma (n + 1) / (2 * π) ^ n := sorry
  _ = _ := sorry

end MagicFunction
