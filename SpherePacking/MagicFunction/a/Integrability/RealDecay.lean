/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential Decay Integrability Lemmas (Tail Regime)

This file provides pure real analysis lemmas for integrability of exponentially
decaying functions in the tail regime (t → ∞), particularly polynomial × exponential
patterns.

These lemmas are designed to be reusable for contour integral analysis where:
- For r > 2, exponential decay beats polynomial growth in vertical ray integrands

## Main results

### Asymptotic behavior
- `tendsto_const_mul_rpow_mul_exp_neg_atTop`: C · t^n · exp(-a·t) → 0 as t → ∞ for a > 0

### Integrability
- `integrableOn_exp_mul_const_mul_pow_Ici`: polynomial times exponential on any
  nonnegative ray; the linear and quadratic lemmas below are special cases
- `integrableOn_exp_mul_Ici`: exp(c*t) is integrable on [1,∞) for c < 0
- `integrableOn_mul_exp_neg_Ici`: t * exp(-a*t) is integrable on [1,∞) for a > 0
- `integrableOn_sq_mul_exp_neg_Ici`: t² * exp(-a*t) is integrable on [1,∞) for a > 0

### Exact integrals
- `integral_exp_mul_pow_Ici`: the exponential moment `n! / b^(n+1)` on `[0, ∞)`

## References

These patterns appear in the magic function integrability proofs for sphere packing,
specifically for vertical ray integrands in ContourEndpoints.lean.
-/

@[expose] public section

open MeasureTheory Set Filter Real

noncomputable section

/-! ## Integrability Lemmas -/

section Integrability

/-- Exponential decay beats polynomial growth: for `c < 0` and `0 ≤ a`, the function
`s ↦ exp (c * s) * (d * s ^ n)` is integrable on the ray `[a, ∞)`.

This is the `p = 1`, natural-power case of `integrableOn_rpow_mul_exp_neg_mul_rpow`,
transported from `Ioi 0` to an arbitrary ray `Ici a` with `0 ≤ a`. -/
theorem integrableOn_exp_mul_const_mul_pow_Ici {a c : ℝ} (ha : 0 ≤ a) (hc : c < 0) (d : ℝ)
    (n : ℕ) : IntegrableOn (fun s : ℝ ↦ rexp (c * s) * (d * s ^ n)) (Ici a) volume := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine IntegrableOn.congr_fun (((integrableOn_rpow_mul_exp_neg_mul_rpow (s := n) (p := 1)
    (b := -c) (neg_one_lt_zero.trans_le n.cast_nonneg) le_rfl (neg_pos.2 hc)).mono_set
    (Ioi_subset_Ioi ha)).const_mul d) (fun s _ ↦ ?_) measurableSet_Ioi
  rw [rpow_one, rpow_natCast, neg_neg]
  ring

/-- exp(c*t) is integrable on [1,∞) for c < 0. -/
lemma integrableOn_exp_mul_Ici (c : ℝ) (hc : c < 0) :
    IntegrableOn (fun t ↦ exp (c * t)) (Ici 1) volume :=
  (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hc 1)

/-- `C · t^n · exp(-a·t) → 0` as `t → ∞` for `a > 0` and any real power `n`. -/
lemma tendsto_const_mul_rpow_mul_exp_neg_atTop (C a n : ℝ) (ha : 0 < a) :
    Tendsto (fun t ↦ C * t ^ n * exp (-a * t)) atTop (nhds 0) := by
  simpa [mul_assoc] using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n a ha).const_mul C

/-- t * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t ↦ t * exp (-a * t)) (Ici 1) volume := by
  simpa [mul_comm] using
    integrableOn_exp_mul_const_mul_pow_Ici zero_le_one (neg_neg_of_pos ha) 1 1

/-- t² * exp(-a*t) is integrable on [1,∞) for a > 0. -/
lemma integrableOn_sq_mul_exp_neg_Ici (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t ↦ t^2 * exp (-a * t)) (Ici 1) volume := by
  simpa [mul_comm] using
    integrableOn_exp_mul_const_mul_pow_Ici zero_le_one (neg_neg_of_pos ha) 1 2

/-- The exponential moment on the nonnegative half-line. -/
lemma integral_exp_mul_pow_Ici (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ s in Ici (0 : ℝ), exp (-b * s) * s ^ n) =
      (n.factorial : ℝ) / b ^ (n + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (by positivity) hb
  rw [Real.rpow_add (by positivity), Real.rpow_natCast, Real.rpow_one] at h
  simpa [Real.rpow_natCast, neg_mul, Real.Gamma_nat_eq_factorial,
    pow_succ, one_div, inv_pow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end Integrability

end
