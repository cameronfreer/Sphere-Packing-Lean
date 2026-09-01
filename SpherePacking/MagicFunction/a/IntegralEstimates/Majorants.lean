/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module


public import SpherePacking.MagicFunction.PolyFourierCoeffBound
public import SpherePacking.MagicFunction.a.Basic
public import SpherePacking.MagicFunction.a.Integrability.RealDecay

/-!
# Shared Majorants for the Contour Integrals `Iⱼ`

The six segments making up the contour defining `a` fall into three classes, and within each
class the analytic estimate is *the same*; only the parametrisation and a unit-modulus phase
differ. This file isolates the shared ingredients so that `I1.lean`–`I6.lean` and
`Integrability.lean` become thin specialisations.

## Main results

### The master bound on `φ₀''`

* `norm_φ₀''_le`: for `Im w > 1/2`, `‖φ₀'' w‖ ≤ C₀ * exp (-2π * Im w)`. This is
  `PolyFourierCoeffBound.norm_φ₀_le` transported from `ℍ` to `ℂ` once and for all.

Specialisations along the three families of parametrisations:

* `norm_φ₀''_I_mul_le` (vertical ray `w = I * s`, `s > 1/2`),
* `norm_φ₀''_neg_inv_I_mul_le` (cusp ray `w = -1/(I * t)`, `0 < t < 2`),
* `norm_φ₀''_neg_inv_add_I_le` (top edge `w = -1/(u + I)`, `u` real).

### Majorant integrability, by contour class

* `integrableOn_majorant_cusp`: `C₀ * exp (-2πs) * exp (-πr/s)` on `[1, ∞)`,
* `integrableOn_majorant_vertical`: `C₀ * exp (-2πt) * exp (-πrt)` on `[1, ∞)` for `r ≥ 0`.

### Segment majorants for the real integrands

* `Φ₁_eq_Φ₅_mul_phase`, `Φ₃_eq_Φ₅_mul_phase`: the cusp-touching integrands agree up to a
  unit-modulus phase, so a single estimate covers all three,
* `norm_Φ₅_le`, `norm_Φ₁_le`, `norm_Φ₃_le`: uniform bounds on `(0, 1]`,
* `integrableOn_of_norm_le_const`: a continuous function with a uniform bound on a set of
  finite measure is integrable there.
-/

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals
  MagicFunction.a.RadialFunctions MagicFunction.PolyFourierCoeffBound
  MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter
open scoped Function UpperHalfPlane

noncomputable section

namespace MagicFunction.a.Majorants

/-! ## The master bound on `φ₀''` -/

/-- The `PolyFourierCoeffBound` for `φ₀`, transported to `φ₀''` on the half-plane `Im w > 1/2`.

Every estimate on the six contour segments is a specialisation of this one bound; the
segments differ only in the parametrisation `t ↦ w t` fed into it. -/
theorem norm_φ₀''_le : ∃ C₀ > 0, ∀ w : ℂ, 1 / 2 < w.im → ‖φ₀'' w‖ ≤ C₀ * rexp (-2 * π * w.im) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀_le
  refine ⟨C₀, hC₀_pos, fun w hw ↦ ?_⟩
  have hpos : 0 < w.im := one_half_pos.trans hw
  exact (φ₀''_def hpos) ▸ hC₀ ⟨w, hpos⟩ hw

/-! ### Imaginary parts of the three families of parametrisations -/

@[simp]
lemma im_I_mul (s : ℝ) : (I * (s : ℂ)).im = s := by simp

/-- `-1 / (I * t) = I / t`, so the cusp ray is again a point of the imaginary axis. -/
lemma neg_one_div_I_mul (t : ℝ) : -1 / (I * (t : ℂ)) = I / (t : ℂ) := by
  rw [div_eq_mul_inv, mul_inv, Complex.inv_I, div_eq_mul_inv]
  ring

@[simp]
lemma im_neg_one_div_I_mul (t : ℝ) : (-1 / (I * (t : ℂ))).im = t⁻¹ := by
  rw [neg_one_div_I_mul]
  simp [Complex.div_ofReal_im]

/-- The top edge of the fundamental domain, parametrised by `u ↦ -1 / (u + I)`. -/
lemma im_neg_one_div_add_I (u : ℝ) : (-1 / ((u : ℂ) + I)).im = 1 / (u ^ 2 + 1) := by
  have hne : ((u : ℂ) + I) ≠ 0 := by
    simp only [ne_eq, Complex.ext_iff, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
      zero_re, zero_im, add_zero, zero_add]
    norm_num
  rw [div_im]
  simp only [neg_re, neg_im, one_re, one_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    add_zero, zero_add, neg_zero, zero_mul, zero_div, zero_sub, normSq_apply]
  ring_nf

/-! ### Specialisations of the master bound -/

/-- Vertical-ray class (`I₆`, and `I₁`, `I₃`, `I₅` after the change of variables `s = 1/t`). -/
theorem norm_φ₀''_I_mul_le :
    ∃ C₀ > 0, ∀ s : ℝ, 1 / 2 < s → ‖φ₀'' (I * (s : ℂ))‖ ≤ C₀ * rexp (-2 * π * s) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_le
  exact ⟨C₀, hC₀_pos, fun s hs ↦ by simpa using hC₀ (I * (s : ℂ)) (by simpa using hs)⟩

/-- Cusp-touching class (`I₁`, `I₃`, `I₅` in their original parametrisation): as `t → 0⁺` the
point `-1/(I t)` runs out to the cusp, and the bound decays like `exp (-2π/t)`. -/
theorem norm_φ₀''_neg_inv_I_mul_le : ∃ C₀ > 0, ∀ t : ℝ, 0 < t → t < 2 →
    ‖φ₀'' (-1 / (I * (t : ℂ)))‖ ≤ C₀ * rexp (-2 * π / t) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_le
  refine ⟨C₀, hC₀_pos, fun t ht ht' ↦ ?_⟩
  have him : 1 / 2 < (-1 / (I * (t : ℂ))).im := by
    rw [im_neg_one_div_I_mul]
    nlinarith [mul_inv_cancel₀ ht.ne', inv_pos.mpr ht]
  simpa only [im_neg_one_div_I_mul, ← div_eq_mul_inv] using hC₀ _ him

/-- Compact top-edge class (`I₂`, `I₄`): here `1/2 < Im (-1/(u + I)) ≤ 1`, so the master bound
degenerates to a constant, uniformly in `u`. -/
theorem norm_φ₀''_neg_inv_add_I_le :
    ∃ C₀ > 0, ∀ u : ℝ, |u| < 1 → ‖φ₀'' (-1 / ((u : ℂ) + I))‖ ≤ C₀ * rexp (-π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_le
  refine ⟨C₀, hC₀_pos, fun u hu ↦ ?_⟩
  have hu2 : u ^ 2 < 1 := by nlinarith [abs_nonneg u, sq_abs u]
  have hden : (0 : ℝ) < u ^ 2 + 1 := by positivity
  have him : 1 / 2 < (-1 / ((u : ℂ) + I)).im := by
    rw [im_neg_one_div_add_I, one_div, one_div, inv_lt_inv₀ two_pos hden]; linarith
  refine (hC₀ _ him).trans ?_
  have hle : -2 * π * (-1 / ((u : ℂ) + I)).im ≤ -π := by nlinarith [Real.pi_pos]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hC₀_pos.le

/-! ## Majorant integrability, by contour class -/

/-- Cusp class: after the change of variables `s = 1/t` the majorant is
`C₀ * exp (-2πs) * exp (-πr/s)` on `[1, ∞)`. The second factor is bounded there, so the
first factor carries the integrability. -/
theorem integrableOn_majorant_cusp (r C₀ : ℝ) :
    IntegrableOn (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s)) (Ici 1) volume := by
  set μ := volume.restrict (Ici (1 : ℝ))
  have h_g : Integrable (fun s ↦ C₀ * rexp (-2 * π * s)) μ :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (by linarith [pi_pos]) 1)).const_mul C₀
  have hφ : AEStronglyMeasurable (fun s ↦ rexp (-π * r / s)) μ :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_inv)).aestronglyMeasurable
  have hb : ∀ᵐ s ∂μ, ‖rexp (-π * r / s)‖ ≤ rexp (π * |r|) :=
    (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall fun s (hs : 1 ≤ s) ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
      refine exp_le_exp.mpr <| (le_abs_self _).trans ?_
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg pi_pos.le, abs_of_nonneg (by linarith : 0 ≤ s)]
      exact div_le_self (by positivity) hs
  change Integrable (fun s ↦ C₀ * rexp (-2 * π * s) * rexp (-π * r / s))
    (volume.restrict (Ici (1 : ℝ)))
  simpa [μ, mul_comm] using h_g.bdd_mul hφ hb

/-- Vertical class: the majorant `C₀ * exp (-2πt) * exp (-πrt)` on `[1, ∞)`, for `r ≥ 0`. -/
theorem integrableOn_majorant_vertical (r C₀ : ℝ) (hr : 0 ≤ r) :
    IntegrableOn (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) (Ici 1) volume := by
  have h_eq : (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * r * t))
      = fun t ↦ C₀ * rexp ((-2 * π - π * r) * t) := by
    ext t
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [h_eq]
  exact (integrableOn_exp_mul_Ici _ (by nlinarith [pi_pos])).const_mul C₀

/-! ## Uniform bounds give integrability on sets of finite measure -/

/-- A continuous function with a uniform norm bound on a measurable set of finite measure is
integrable there. This is the segment-integrability workhorse for `Φ₁`–`Φ₅`. -/
theorem integrableOn_of_norm_le_const {f : ℝ → ℂ} {s : Set ℝ} {C : ℝ}
    (hs : MeasurableSet s) (hs' : volume s ≠ ⊤) (hf : ContinuousOn f s)
    (hb : ∀ t ∈ s, ‖f t‖ ≤ C) : IntegrableOn f s volume := by
  have hconst : IntegrableOn (fun _ : ℝ ↦ C) s volume := integrableOn_const hs' ENNReal.coe_ne_top
  refine Integrable.mono' hconst (hf.aestronglyMeasurable hs) ?_
  rw [ae_restrict_iff' hs]
  exact ae_of_all _ hb

/-! ## Segment majorants for the real integrands `Φⱼ` -/

section RealIntegrands

variable {r t : ℝ}

/-- `π * I * r * (I * t) = -(π * r * t)`, the identity behind every cusp-class simplification. -/
lemma cexp_pi_I_mul_I (r t : ℝ) :
    cexp ((π : ℂ) * I * (r : ℂ) * (I * (t : ℂ))) = cexp (-((π : ℂ) * (r : ℂ) * (t : ℂ))) := by
  congr 1
  calc (π : ℂ) * I * r * (I * t) = (π : ℂ) * (I * I) * r * t := by ring
    _ = _ := by rw [I_mul_I]; ring

private lemma norm_cexp_pi_I_mul (c : ℝ) : ‖cexp ((c : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I c

/-- For `t ∈ (0, 1]`, `exp (-2π/t) * t² ≤ exp (-2π)`: the super-exponential decay at the cusp
swallows the quadratic factor coming from the parametrisation. -/
lemma exp_neg_two_pi_div_mul_sq_le (ht : 0 < t) (ht' : t ≤ 1) :
    rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) := by
  have h1 : rexp (-2 * π / t) ≤ rexp (-2 * π) := by
    rw [Real.exp_le_exp, neg_mul, neg_div, neg_le_neg_iff, le_div_iff₀ ht]
    nlinarith [Real.pi_pos]
  calc rexp (-2 * π / t) * t ^ 2 ≤ rexp (-2 * π) * t ^ 2 := by gcongr
    _ ≤ rexp (-2 * π) * 1 := by gcongr; nlinarith
    _ = rexp (-2 * π) := mul_one _

/-- `Φ₁` is `Φ₅` up to the unit-modulus phase `exp (-πIr)`: on `[0,1]`, `z₁' t + 1 = z₅' t`. -/
lemma Φ₁_eq_Φ₅_mul_phase (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ₁ r t = Φ₅ r t * cexp ((-(π * r) : ℝ) * I) := by
  simp only [Φ₁, Φ₅, Φ₁', Φ₅', z₁'_eq_of_mem ht, z₅'_eq_of_mem ht]
  have h_add : (-1 : ℂ) + I * (t : ℂ) + 1 = I * (t : ℂ) := by ring
  have h_exp : cexp ((π : ℂ) * I * (r : ℂ) * (-1 + I * (t : ℂ)))
      = cexp (((-(π * r) : ℝ) : ℂ) * I) * cexp (-((π : ℂ) * (r : ℂ) * (t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    calc (π : ℂ) * I * r * (-1 + I * t) = -(π * r) * I + π * (I * I) * r * t := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [h_add, h_exp, cexp_pi_I_mul_I]
  ring

/-- `Φ₃` is `Φ₅` up to the unit-modulus phase `exp (πIr)`: on `[0,1]`, `z₃' t - 1 = z₅' t`. -/
lemma Φ₃_eq_Φ₅_mul_phase (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ₃ r t = Φ₅ r t * cexp (((π * r) : ℝ) * I) := by
  simp only [Φ₃, Φ₅, Φ₃', Φ₅', z₃'_eq_of_mem ht, z₅'_eq_of_mem ht]
  have h_sub : (1 : ℂ) + I * (t : ℂ) - 1 = I * (t : ℂ) := by ring
  have h_exp : cexp ((π : ℂ) * I * (r : ℂ) * (1 + I * (t : ℂ)))
      = cexp ((((π * r) : ℝ) : ℂ) * I) * cexp (-((π : ℂ) * (r : ℂ) * (t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    calc (π : ℂ) * I * r * (1 + I * t) = (π * r) * I + π * (I * I) * r * t := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [h_sub, h_exp, cexp_pi_I_mul_I]
  ring

/-- Uniform bound for `Φ₅` on `(0, 1]`, for `r ≥ 0`.

Writing `Φ₅ r t = I * φ₀''(-1/(It)) * (It)² * exp (-πrt)`, the three factors are handled by
`norm_φ₀''_neg_inv_I_mul_le`, `exp_neg_two_pi_div_mul_sq_le` and `exp (-πrt) ≤ 1`. -/
lemma norm_Φ₅_le (hr : 0 ≤ r) :
    ∃ C₀ > 0, ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₅ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_φ₀''_neg_inv_I_mul_le
  refine ⟨C₀, hC₀_pos, fun t ht ↦ ?_⟩
  have ht' : t ∈ Icc (0 : ℝ) 1 := mem_Icc_of_Ioc ht
  simp only [Φ₅, Φ₅', z₅'_eq_of_mem ht']
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, mul_pow, I_sq, neg_one_mul,
    norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1,
    cexp_pi_I_mul_I, Complex.norm_exp]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have h_φ : ‖φ₀'' (-1 / (I * (t : ℂ)))‖ ≤ C₀ * rexp (-2 * π / t) :=
    hC₀ t ht.1 (lt_of_le_of_lt ht.2 one_lt_two)
  have h_exp_r : rexp (-(π * r * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos_of_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hr) ht.1.le)
  calc ‖φ₀'' (-1 / (I * (t : ℂ)))‖ * t ^ 2 * rexp (-(π * r * t))
      ≤ ‖φ₀'' (-1 / (I * (t : ℂ)))‖ * t ^ 2 := mul_le_of_le_one_right (by positivity) h_exp_r
    _ ≤ C₀ * rexp (-2 * π / t) * t ^ 2 := by gcongr
    _ = C₀ * (rexp (-2 * π / t) * t ^ 2) := by ring
    _ ≤ C₀ * rexp (-2 * π) := by gcongr; exact exp_neg_two_pi_div_mul_sq_le ht.1 ht.2

/-- Uniform bound for `Φ₁` on `(0, 1]`: it agrees with `Φ₅` up to a unit-modulus phase. -/
lemma norm_Φ₁_le (hr : 0 ≤ r) :
    ∃ C₀ > 0, ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₁ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_Φ₅_le hr
  refine ⟨C₀, hC₀_pos, fun t ht ↦ ?_⟩
  rw [Φ₁_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht), norm_mul, norm_cexp_pi_I_mul, mul_one]
  exact hC₀ t ht

/-- Uniform bound for `Φ₃` on `(0, 1]`: it agrees with `Φ₅` up to a unit-modulus phase. -/
lemma norm_Φ₃_le (hr : 0 ≤ r) :
    ∃ C₀ > 0, ∀ t ∈ Ioc (0 : ℝ) 1, ‖Φ₃ r t‖ ≤ C₀ * rexp (-2 * π) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_Φ₅_le hr
  refine ⟨C₀, hC₀_pos, fun t ht ↦ ?_⟩
  rw [Φ₃_eq_Φ₅_mul_phase (mem_Icc_of_Ioc ht), norm_mul, norm_cexp_pi_I_mul, mul_one]
  exact hC₀ t ht

end RealIntegrands

end MagicFunction.a.Majorants

end
