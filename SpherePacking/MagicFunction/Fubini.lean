/-
Copyright (c) 2025 The Sphere Packing Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere Packing Contributors
-/

import SpherePacking.MagicFunction.a.Integrability.ProductIntegrability

/-!
# Fubini Swap Lemmas for Contour Integrals

This file uses the integrability results from `ProductIntegrability.lean` to prove Fubini-type
swap lemmas: ∫_{ℝ⁸} ∫_{contour} = ∫_{contour} ∫_{ℝ⁸}.

## Main results

### Fubini swap lemmas
- `I₁_integral_swap` through `I₆_integral_swap`: Swap ∫_{ℝ⁸} and ∫_{contour}

### Basic integrability (corollaries)
- `I₁_integrable` through `I₆_integrable`: Each Iⱼ is integrable on ℝ⁸
- `a_integrable`: The magic function `a` is integrable on ℝ⁸
-/

open MeasureTheory Complex Real Set intervalIntegral

local notation "V" => EuclideanSpace ℝ (Fin 8)

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
open MagicFunction.a.RealIntegrands MagicFunction.a.ComplexIntegrands

noncomputable section

/-! ## Fubini Swap Lemmas

Once we have product integrability, Fubini's theorem allows swapping
the order of integration: ∫_{ℝ⁸} ∫_{contour} = ∫_{contour} ∫_{ℝ⁸}.
-/

section FubiniSwap

/-- Connection: I₁ x = ∫ t, I₁_integrand (x, t) -/
lemma I₁_eq_integral (x : V) :
    I₁ x = ∫ t in Ioc (0 : ℝ) 1, I₁_integrand (x, t) := by
  rw [I₁, I₁'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₁_integrand, Φ₁, Φ₁', z₁'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow]
  -- z₁' t + 1 = -1 + I*t + 1 = I*t, and (I*t)^2 = -t^2
  have h_add : (-1 : ℂ) + I * ↑t + 1 = I * ↑t := by ring
  have h_sq : (I * (t : ℂ)) ^ 2 = -(t : ℂ) ^ 2 := by rw [mul_pow, I_sq]; ring
  -- cexp(π*I*r*(-1 + I*t)) = cexp(-π*I*r) * cexp(-π*r*t)
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (-1 + I * ↑t)) =
      cexp (-↑π * I * r) * cexp (-↑π * r * ↑t) := fun r => by
    rw [← Complex.exp_add]; congr 1
    calc ↑π * I * r * (-1 + I * ↑t) = -↑π * I * r + ↑π * (I * I) * r * ↑t := by ring
      _ = -↑π * I * r + ↑π * (-1) * r * ↑t := by rw [I_mul_I]
      _ = -↑π * I * r + -↑π * r * ↑t := by ring
  simp only [h_add, h_sq, h_exp]; ring

/-- Connection: I₂ x = ∫ t, I₂_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₂_eq_integral (x : V) :
    I₂ x = ∫ t in Icc (0 : ℝ) 1, I₂_integrand (x, t) := by
  rw [I₂, I₂'_eq]
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₂_integrand, Φ₂, Φ₂', z₂'_eq_of_mem ht, ofReal_pow]
  -- z₂' t + 1 = -1 + t + I + 1 = t + I
  have h_add : (-1 : ℂ) + ↑t + I + 1 = ↑t + I := by ring
  -- cexp(π*I*r*(-1 + t + I)) = cexp(-π*I*r) * cexp(π*I*r*t) * cexp(-π*r)
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (-1 + ↑t + I)) =
      cexp (-↑π * I * r) * cexp (↑π * I * r * ↑t) * cexp (-↑π * r) := fun r => by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    calc ↑π * I * r * (-1 + ↑t + I)
        = -↑π * I * r + ↑π * I * r * ↑t + ↑π * (I * I) * r := by ring
      _ = -↑π * I * r + ↑π * I * r * ↑t + ↑π * (-1) * r := by rw [I_mul_I]
      _ = -↑π * I * r + ↑π * I * r * ↑t + -↑π * r := by ring
  simp only [h_add, h_exp]; ring

/-- Connection: I₃ x = ∫ t, I₃_integrand (x, t) -/
lemma I₃_eq_integral (x : V) :
    I₃ x = ∫ t in Ioc (0 : ℝ) 1, I₃_integrand (x, t) := by
  rw [I₃, I₃'_eq_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₃_integrand, Φ₃, Φ₃', z₃'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow]
  -- z₃' t - 1 = 1 + I*t - 1 = I*t, and (I*t)^2 = -t^2
  have h_sub : (1 : ℂ) + I * ↑t - 1 = I * ↑t := by ring
  have h_sq : (I * (t : ℂ)) ^ 2 = -(t : ℂ) ^ 2 := by rw [mul_pow, I_sq]; ring
  -- cexp(π*I*r*(1 + I*t)) = cexp(π*I*r) * cexp(-π*r*t)
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (1 + I * ↑t)) =
      cexp (↑π * I * r) * cexp (-↑π * r * ↑t) := fun r => by
    rw [← Complex.exp_add]; congr 1
    calc ↑π * I * r * (1 + I * ↑t) = ↑π * I * r + ↑π * (I * I) * r * ↑t := by ring
      _ = ↑π * I * r + ↑π * (-1) * r * ↑t := by rw [I_mul_I]
      _ = ↑π * I * r + -↑π * r * ↑t := by ring
  simp only [h_sub, h_sq, h_exp]; ring

/-- Connection: I₄ x = ∫ t, I₄_integrand (x, t) over [0,1].
Note: Uses Icc because the integrand is continuous (no singularity at 0). -/
lemma I₄_eq_integral (x : V) :
    I₄ x = ∫ t in Icc (0 : ℝ) 1, I₄_integrand (x, t) := by
  rw [I₄, I₄'_eq]
  rw [intervalIntegral_eq_integral_uIoc, if_pos (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), one_smul]
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Icc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₄_integrand, Φ₄, Φ₄', z₄'_eq_of_mem ht, ofReal_pow]
  -- z₄' t - 1 = 1 - t + I - 1 = -t + I
  have h_sub : (1 : ℂ) - ↑t + I - 1 = -↑t + I := by ring
  -- cexp(π*I*r*(1 - t + I)) = cexp(π*I*r) * cexp(-π*I*r*t) * cexp(-π*r)
  have h_exp : ∀ r : ℂ, cexp (↑π * I * r * (1 - ↑t + I)) =
      cexp (↑π * I * r) * cexp (-↑π * I * r * ↑t) * cexp (-↑π * r) := fun r => by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1
    calc ↑π * I * r * (1 - ↑t + I)
        = ↑π * I * r - ↑π * I * r * ↑t + ↑π * (I * I) * r := by ring
      _ = ↑π * I * r - ↑π * I * r * ↑t + ↑π * (-1) * r := by rw [I_mul_I]
      _ = ↑π * I * r + -↑π * I * r * ↑t + -↑π * r := by ring
  simp only [h_sub, h_exp]; ring

/-- Connection: I₅ x = -2 * ∫ t, I₅_integrand (x, t) -/
lemma I₅_eq_integral (x : V) :
    I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, I₅_integrand (x, t) := by
  rw [I₅, I₅'_eq_Ioc]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ioc
  refine ae_of_all _ fun t ht => ?_
  simp only [I₅_integrand, Φ₅, Φ₅', z₅'_eq_of_mem (mem_Icc_of_Ioc ht), ofReal_pow]
  -- (I*t)^2 = -t^2 and cexp(π*I*r*(I*t)) = cexp(-π*r*t)
  have h1 : (I * (t : ℂ)) ^ 2 = -(t : ℂ) ^ 2 := by rw [mul_pow, I_sq]; ring
  have h2 : ∀ r : ℂ, cexp (↑π * I * r * (I * ↑t)) = cexp (-↑π * r * ↑t) := fun r => by
    congr 1
    calc ↑π * I * r * (I * ↑t) = ↑π * (I * I) * r * ↑t := by ring
      _ = ↑π * (-1) * r * ↑t := by rw [I_mul_I]
      _ = -↑π * r * ↑t := by ring
  simp only [h1, h2]; ring

/-- Connection: I₆ x = 2 * ∫ t, I₆_integrand (x, t) -/
lemma I₆_eq_integral (x : V) :
    I₆ x = 2 * ∫ t in Ici (1 : ℝ), I₆_integrand (x, t) := by
  rw [I₆, I₆'_eq]
  congr 1
  apply MeasureTheory.setIntegral_congr_ae₀ nullMeasurableSet_Ici
  refine ae_of_all _ fun t ht => ?_
  simp only [I₆_integrand, Φ₆, Φ₆', z₆'_eq_of_mem ht, ofReal_pow]
  -- cexp(π*I*r*(I*t)) = cexp(-π*r*t)
  have h : ∀ r : ℂ, cexp (↑π * I * r * (I * ↑t)) = cexp (-↑π * r * ↑t) := fun r => by
    congr 1
    calc ↑π * I * r * (I * ↑t) = ↑π * (I * I) * r * ↑t := by ring
      _ = ↑π * (-1) * r * ↑t := by rw [I_mul_I]
      _ = -↑π * r * ↑t := by ring
  simp only [h]; ring

/-- Fubini for I₁: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₁_integral_swap :
    ∫ x : V, I₁ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₁_integrand (x, t) := by
  simp_rw [I₁_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₁_prod_integrable

/-- Fubini for I₂: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₂_integral_swap :
    ∫ x : V, I₂ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₂_integrand (x, t) := by
  simp_rw [I₂_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₂_prod_integrable

/-- Fubini for I₃: swap ∫_{ℝ⁸} and ∫_{(0,1]} -/
theorem I₃_integral_swap :
    ∫ x : V, I₃ x = ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₃_integrand (x, t) := by
  simp_rw [I₃_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₃_prod_integrable

/-- Fubini for I₄: swap ∫_{ℝ⁸} and ∫_{[0,1]} -/
theorem I₄_integral_swap :
    ∫ x : V, I₄ x = ∫ t in Icc (0 : ℝ) 1, ∫ x : V, I₄_integrand (x, t) := by
  simp_rw [I₄_eq_integral]
  exact MeasureTheory.integral_integral_swap Φ₄_prod_integrable

/-- Fubini for I₅: swap ∫_{ℝ⁸} and ∫_{(0,1]}
Note: includes factor of -2 from I₅ definition. -/
theorem I₅_integral_swap :
    ∫ x : V, I₅ x = -2 * ∫ t in Ioc (0 : ℝ) 1, ∫ x : V, I₅_integrand (x, t) := by
  simp_rw [I₅_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap Φ₅_prod_integrable

/-- Fubini for I₆: swap ∫_{ℝ⁸} and ∫_{[1,∞)}
Note: includes factor of 2 from I₆ definition. -/
theorem I₆_integral_swap :
    ∫ x : V, I₆ x = 2 * ∫ t in Ici (1 : ℝ), ∫ x : V, I₆_integrand (x, t) := by
  simp_rw [I₆_eq_integral]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.integral_integral_swap Φ₆_prod_integrable

end FubiniSwap

/-! ## Basic Integrability

Each Iⱼ is integrable over ℝ⁸ (from Schwartz structure).
-/

section BasicIntegrability

/-- I₁ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₁_integrable : Integrable (I₁ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₁.integrable

/-- I₂ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₂_integrable : Integrable (I₂ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₂.integrable

/-- I₃ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₃_integrable : Integrable (I₃ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₃.integrable

/-- I₄ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₄_integrable : Integrable (I₄ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₄.integrable

/-- I₅ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₅_integrable : Integrable (I₅ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₅.integrable

/-- I₆ is integrable over ℝ⁸ (from Schwartz structure). -/
theorem I₆_integrable : Integrable (I₆ : V → ℂ) :=
  MagicFunction.a.SchwartzIntegrals.I₆.integrable

/-- The magic function `a` is integrable over ℝ⁸. -/
theorem a_integrable : Integrable (a : V → ℂ) := by
  have h : a = I₁ + I₂ + I₃ + I₄ + I₅ + I₆ := by
    ext x
    simp only [Pi.add_apply]
    exact a_eq x
  rw [h]
  exact ((((I₁_integrable.add I₂_integrable).add I₃_integrable).add I₄_integrable).add
    I₅_integrable).add I₆_integrable

end BasicIntegrability

end

