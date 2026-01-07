/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan
-/

import SpherePacking.MagicFunction.a.IntegralEstimates.I1
import SpherePacking.MagicFunction.a.IntegralEstimates.I2
import SpherePacking.MagicFunction.a.IntegralEstimates.I3
import SpherePacking.MagicFunction.a.IntegralEstimates.I4
import SpherePacking.MagicFunction.a.IntegralEstimates.I5
import SpherePacking.MagicFunction.a.IntegralEstimates.I6
import SpherePacking.MagicFunction.a.Integrability.RealIntegrands

/-! # Integrability

In this file, we prove that the integrands `Φⱼ` are integrable.
-/

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions
  MagicFunction.PolyFourierCoeffBound MagicFunction.a.RealIntegrands
  MagicFunction.a.ComplexIntegrands MagicFunction.a.IntegralEstimates.I₆
open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral
open scoped Function UpperHalfPlane

namespace MagicFunction.a.Integrability

/-- For t ∈ [1, ∞), the real integrand Φ₆ r t equals the g function from IntegralEstimates.I₆. -/
lemma Φ₆_eq_I₆_g (r : ℝ) (t : ℝ) (ht : t ∈ Ici 1) : Φ₆ r t = g r t := by
  unfold Φ₆ Φ₆' g
  simp only [z₆'_eq_of_mem ht]
  have h : (π : ℂ) * I * ↑r * (I * ↑t) = -((π : ℂ) * ↑r * ↑t) := by
    ring_nf
    simp only [I_sq]
    ring
  rw [h]
  ring

/-- Φ₁ is integrable on (0, 1].

The proof strategy (not yet formalized):
1. Show `Φ₁ r t = |f' t| • (g r (f t))` where f, f', g are from IntegralEstimates.I₁
2. Use change of variables: integrability of g on Ici 1 implies integrability of
   |f'| • (g ∘ f) on Ioc 0 1
3. The bound `norm_φ₀_le` gives `‖φ₀''(I/t)‖ ≤ C₀ * exp(-2π/t)` for t ∈ (0,1]
4. The factor `exp(-2π/t) * t²` is bounded on (0,1] (super-exponential decay dominates)

See IntegralEstimates.I₁ for the bounds and change of variables infrastructure.
-/
theorem Φ₁_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₁ r)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₁_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  -- TODO: Use bounds from IntegralEstimates.I₁ via change of variables
  sorry

theorem Φ₂_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₂ r)
    (Icc (0 : ℝ) 1) volume :=
  Φ₂_contDiffOn.continuousOn.integrableOn_Icc

/-- Φ₃ is integrable on (0, 1]. Same proof strategy as Φ₁_integrableOn.
See IntegralEstimates.I₃ for the bounds and change of variables infrastructure. -/
theorem Φ₃_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₃ r)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₃_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  -- TODO: Use bounds from IntegralEstimates.I₃ via change of variables
  sorry

theorem Φ₄_integrableOn {r : ℝ} (_hr : r ≥ 0) : IntegrableOn (Φ₄ r)
    (Icc (0 : ℝ) 1) volume :=
  Φ₄_contDiffOn.continuousOn.integrableOn_Icc

/-- Φ₅ is integrable on (0, 1]. Same proof strategy as Φ₁_integrableOn.
See IntegralEstimates.I₅ for the bounds and change of variables infrastructure. -/
theorem Φ₅_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₅ r)
    (Ioc (0 : ℝ) 1) volume := by
  refine ⟨ContinuousOn.aestronglyMeasurable Φ₅_contDiffOn.continuousOn measurableSet_Ioc, ?_⟩
  -- TODO: Use bounds from IntegralEstimates.I₅ via change of variables
  sorry

theorem Φ₆_integrableOn {r : ℝ} (hr : r ≥ 0) : IntegrableOn (Φ₆ r)
    (Ici (1 : ℝ)) volume := by
  -- Get the bound and its integrability from IntegralEstimates.I₆
  obtain ⟨C₀, _, hC₀_bound⟩ := I₆'_bounding_aux_2 r
  have h_bound_int : IntegrableOn
      (fun t ↦ C₀ * rexp (-2 * π * t) * rexp (-π * r * t)) (Ici 1) volume :=
    Bound_integrableOn r C₀ hr
  -- Use Integrable.mono' with the bound
  refine Integrable.mono' h_bound_int ?_ ?_
  · exact ContinuousOn.aestronglyMeasurable Φ₆_contDiffOn.continuousOn measurableSet_Ici
  · rw [ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ fun t ht ↦ (Φ₆_eq_I₆_g r t ht).symm ▸ hC₀_bound t ht

end MagicFunction.a.Integrability
