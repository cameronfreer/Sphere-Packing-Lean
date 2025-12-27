import SpherePacking.ModularForms.Derivative
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy Estimates for Modular Forms

This file provides the infrastructure for using Cauchy estimates to bound derivatives
of holomorphic functions on the upper half plane.

## Main results

* `diffContOnCl_comp_ofComplex_of_mdifferentiable`: Bridge from `MDifferentiable` on ℍ
  to `DiffContOnCl` on disks in ℂ contained in the upper half plane.
* `closedBall_iMul_subset_upperHalfPlane`: Geometric lemma showing `closedBall (I*y) (y/2)`
  is contained in the upper half plane.
* `norm_D_le_of_sphere_bound`: Cauchy estimate for D-derivative: if f is holomorphic on a
  disk and bounded by M on the sphere, then `‖D f z‖ ≤ M / (2πr)`.
* `D_isBoundedAtImInfty_of_bounded`: D-derivative is bounded at infinity for bounded
  holomorphic functions.

-/

open UpperHalfPlane hiding I
open Real Complex Filter Metric
open scoped Topology Manifold

noncomputable section

/-! ## Bridge Lemma: MDifferentiable to DiffContOnCl -/

/-- If `f : ℍ → ℂ` is `MDifferentiable` and a closed disk in `ℂ` lies in the upper half-plane,
then `f ∘ ofComplex` is `DiffContOnCl` on the corresponding open disk. -/
lemma diffContOnCl_comp_ofComplex_of_mdifferentiable
    {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {c : ℂ} {R : ℝ}
    (hclosed : Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball c R) := by
  constructor
  · -- DifferentiableOn on the open ball
    intro z hz
    have hz_closed : z ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hz
    have hz_im : 0 < z.im := hclosed hz_closed
    exact (MDifferentiableAt_DifferentiableAt (hf ⟨z, hz_im⟩)).differentiableWithinAt
  · -- ContinuousOn on closure(ball c R)
    intro z hz
    have hz_closed : z ∈ Metric.closedBall c R :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hz
    have hz_im : 0 < z.im := hclosed hz_closed
    exact (MDifferentiableAt_DifferentiableAt (hf ⟨z, hz_im⟩)).continuousAt.continuousWithinAt

/-! ## Disk Geometry -/

/-- A closed ball centered at `I * y` with radius `y/2` is contained in the upper half plane. -/
lemma closedBall_iMul_subset_upperHalfPlane {y : ℝ} (hy : 0 < y) :
    Metric.closedBall (I * y) (y / 2) ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz_dist : dist z (I * y) ≤ y / 2 := Metric.mem_closedBall.mp hz
  -- |z.im - y| ≤ dist z (I*y) ≤ y/2  (from abs_im_le_norm)
  have him_Iy : (I * ↑y).im = y := by simp
  have habs : |z.im - y| ≤ y / 2 := by
    calc |z.im - y|
      _ = |z.im - (I * y).im| := by rw [him_Iy]
      _ = |(z - I * y).im| := by simp [Complex.sub_im]
      _ ≤ ‖z - I * y‖ := abs_im_le_norm _
      _ = dist z (I * y) := (dist_eq_norm _ _).symm
      _ ≤ y / 2 := hz_dist
  -- z.im ≥ y - y/2 = y/2 > 0
  have hlower : y / 2 ≤ z.im := by
    have h1 : -(y / 2) ≤ z.im - y := (abs_le.mp habs).1
    linarith
  have hyhalf_pos : 0 < y / 2 := by linarith
  exact lt_of_lt_of_le hyhalf_pos hlower

/-- Variant: closed ball centered at z with radius z.im/2 is in upper half plane. -/
lemma closedBall_center_subset_upperHalfPlane (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hdist : dist w z ≤ z.im / 2 := Metric.mem_closedBall.mp hw
  have habs : |w.im - z.im| ≤ z.im / 2 := by
    calc |w.im - z.im|
      _ = |(w - z).im| := by simp [Complex.sub_im]
      _ ≤ ‖w - z‖ := abs_im_le_norm _
      _ = dist w z := (dist_eq_norm _ _).symm
      _ ≤ z.im / 2 := hdist
  have hlower : z.im / 2 ≤ w.im := by
    have h1 : -(z.im / 2) ≤ w.im - z.im := (abs_le.mp habs).1
    linarith
  have hz_im_pos : 0 < z.im := z.im_pos
  exact lt_of_lt_of_le (by linarith : 0 < z.im / 2) hlower

/-! ## Cauchy Estimates -/

/-- Cauchy estimate for the D-derivative: if `f ∘ ofComplex` is holomorphic on a disk of radius `r`
around `z` and bounded by `M` on the boundary sphere, then `‖D f z‖ ≤ M / (2πr)`.

This is the core estimate used by `D_isBoundedAtImInfty_of_bounded`. -/
lemma norm_D_le_of_sphere_bound {f : ℍ → ℂ} {z : ℍ} {r M : ℝ}
    (hr : 0 < r)
    (hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (ball (z : ℂ) r))
    (hbdd : ∀ w ∈ sphere (z : ℂ) r, ‖(f ∘ ofComplex) w‖ ≤ M) :
    ‖D f z‖ ≤ M / (2 * π * r) := by
  have hderiv_bound : ‖deriv (f ∘ ofComplex) z‖ ≤ M / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDiff hbdd
  have h2piI_norm : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc ‖D f z‖
    _ = ‖(2 * π * I)⁻¹ * deriv (f ∘ ofComplex) z‖ := rfl
    _ = ‖(2 * π * I)⁻¹‖ * ‖deriv (f ∘ ofComplex) z‖ := norm_mul _ _
    _ = (2 * π)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by rw [h2piI_norm]
    _ ≤ (2 * π)⁻¹ * (M / r) := by
        apply mul_le_mul_of_nonneg_left hderiv_bound (inv_nonneg.mpr (by positivity))
    _ = M / (2 * π * r) := by ring

/-- The D-derivative is bounded at infinity for bounded holomorphic functions.

For y large (y ≥ 2*max(A,0) + 1), we use a ball of radius z.im/2 around z.
The ball lies in the upper half plane, f is bounded by M on it, and
`norm_D_le_of_sphere_bound` gives ‖D f z‖ ≤ M/(π·z.im) ≤ M/π. -/
lemma D_isBoundedAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (D f) := by
  rw [isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  use M / π, 2 * max A 0 + 1
  intro z hz
  have hz_large : z.im > 2 * max A 0 := by linarith
  have hz_half_gt_A : z.im / 2 > max A 0 := by linarith
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  -- Build DiffContOnCl on ball(z, z.im/2)
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  -- f is bounded by M on the sphere (all points have Im > A)
  have hf_bdd_sphere : ∀ w ∈ sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im := hclosed (sphere_subset_closedBall hw)
    have hdist : dist w z = z.im / 2 := mem_sphere.mp hw
    have habs : |w.im - z.im| ≤ z.im / 2 := by
      calc |w.im - z.im| = |(w - z).im| := by simp [Complex.sub_im]
        _ ≤ ‖w - z‖ := abs_im_le_norm _
        _ = dist w z := (dist_eq_norm _ _).symm
        _ = z.im / 2 := hdist
    have hw_im_ge_A : A ≤ w.im := by
      have hlower : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
      linarith [le_max_left A 0]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw_im_pos]
    exact hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  -- Apply Cauchy estimate and bound by M/π
  have hD_bound := norm_D_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
  have hz_im_ge_1 : 1 ≤ z.im := by linarith [le_max_right A 0]
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) (hMA z (by linarith [le_max_left A 0]))
  calc ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) := hD_bound
    _ = M / (π * z.im) := by ring
    _ ≤ M / (π * 1) := by
        apply div_le_div_of_nonneg_left hM_nonneg (by positivity)
        exact mul_le_mul_of_nonneg_left hz_im_ge_1 (le_of_lt Real.pi_pos)
    _ = M / π := by ring

end
