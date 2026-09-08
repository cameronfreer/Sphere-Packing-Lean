/-
Copyright (c) 2026 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/
module

public import SpherePacking.ForMathlib.Analysis.Complex.Exponential
public import SpherePacking.MagicFunction.a.Integrability.RealDecay

/-!
# Bound on the integral with which we bound I₁, I₃, I₅, J₁, J₃, J₅ and their derivatives
-/

@[expose] public section

open Real MeasureTheory Set

namespace MagicFunction

open Nat

private lemma neg_two_pi_neg : -2 * π < 0 := mul_neg_of_neg_of_pos (by norm_num) pi_pos

theorem pow_mul_integral_le {r : ℝ} (hr : 0 ≤ r) {n : ℕ} :
    r ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * rexp (-π * r / s) ≤
      (n / π * rexp (-1)) ^ n * (n)! / (2 * π) ^ (n + 1) := calc
  _ = ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * (r ^ n * rexp (-π * r / s)) := by
      simp only [← smul_eq_mul (a := r ^ n), ← integral_smul]
      grind [smul_eq_mul (a := r ^ n)]
  _ ≤ ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * ((n / π * rexp (-1)) ^ n * s ^ n) := by
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
      · exact integrableOn_exp_mul_const_mul_pow_Ici zero_le_one neg_two_pi_neg _ n
  _ ≤ (n / π * rexp (-1)) ^ n * ∫ s in Ici (1 : ℝ), rexp (-2 * π * s) * s ^ n := by
      simp only [← smul_eq_mul (a := (n / π * rexp (-1)) ^ n), ← integral_smul]
      grind [smul_eq_mul (a := (n / π * rexp (-1)) ^ n)]
  _ ≤ (n / π * rexp (-1)) ^ n * ∫ s in Ici (0 : ℝ), rexp (-2 * π * s) * s ^ n := by
      gcongr 1
      refine setIntegral_mono_set ?_ (ae_restrict_of_forall_mem measurableSet_Ici ?_) ?_
      · simpa using integrableOn_exp_mul_const_mul_pow_Ici le_rfl neg_two_pi_neg 1 n
      · intro s hs
        rw [mem_Ici] at hs
        positivity
      · filter_upwards with x
        change x ∈ Set.Ici 1 → x ∈ Set.Ici 0
        grind
  _ = _ := by
    simpa only [neg_mul, mul_div_assoc] using
      congrArg (fun x : ℝ ↦ (n / π * rexp (-1)) ^ n * x)
        (integral_exp_mul_pow_Ici n (b := 2 * π) (by positivity))

/-- Exact integral of the vertical-tail bound, with `r` the squared-radius parameter. -/
theorem integral_majorant_vertical_eq (r C : ℝ) (hr : 0 ≤ r) :
    (∫ t in Ici (1 : ℝ), C * rexp (-2 * π * t) * rexp (-π * r * t)) =
      C * rexp (-π * (r + 2)) / (π * (r + 2)) := by
  have hneg : -π * (r + 2) < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos pi_pos) (by positivity)
  have heq : (fun t : ℝ ↦ C * rexp (-2 * π * t) * rexp (-π * r * t)) =
      fun t ↦ C * rexp ((-π * (r + 2)) * t) := by
    ext t
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hneg 1]
  simp only [mul_one, neg_mul, neg_div_neg_eq]
  ring

end MagicFunction
