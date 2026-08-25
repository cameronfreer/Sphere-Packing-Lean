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
      (n / π) ^ n * (n)! / (2 * π) ^ n := by
  have hs : ∀ s ∈ Ici (1 : ℝ), 0 ≤ r / s := by
    intro _ hs
    rw [mem_Ici] at hs
    positivity
  have hexp : ∀ s ∈ Ici (1 : ℝ), _ := fun s' hs' ↦ exp_neg_mul_decay n pi_pos <| hs s' hs'

  -- now the proof structure

  calc
  _ = ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * (r ^ n * rexp (-π * r / s)) := by
      simp only [← smul_eq_mul (a := r ^ n), ← integral_smul]
      grind [smul_eq_mul (a := r ^ n)]
  _ ≤ ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * ((n / π) ^ n * s ^ n) := by
      refine setIntegral_mono_of_nonneg ?_ ?_ ?_
      · intro _ hx
        rw [mem_Ici] at hx
        positivity
      · intro s hs
        gcongr 1
        
        sorry
      · sorry
  _ ≤ (n / π) ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * s ^ n := sorry
  _ ≤ (n / π) ^ n * ∫ s in Ici (0 : ℝ), rexp (-2 * π * s) * s ^ n := sorry
  _ = (n / π) ^ n * ∫ s in Ici (0 : ℝ), 1 / (2 * π) ^ (n + 1) * rexp (-2 * π * s) * (2 * π * s) ^ n
      := sorry
  _ = (n / π) ^ n * Gamma (n + 1) / (2 * π) ^ n := sorry
  _ = _ := sorry

end MagicFunction
