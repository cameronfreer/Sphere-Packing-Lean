import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.Derivative_Cauchy

/-!
# Slash Invariance of Serre Derivative of E₂

This file proves that the Serre derivative `serre_D 1 E₂` is weight-4 slash-invariant
under SL(2,ℤ), despite E₂ itself not being modular.

## Main results

* `D_D₂` : Derivative of the anomaly function D₂: `D(D₂ γ) z = -c²/denom²`
* `MDifferentiable_D₂` : D₂ γ is MDifferentiable
* `serre_D_E₂_slash_invariant` : serre_D 1 E₂ is weight-4 slash-invariant

## Strategy

The key insight is that under the slash action:
- `E₂ ∣[2] γ = E₂ - α * D₂ γ` where `α = 3/π²`
- `D(D₂ γ) = -c²/denom²` where `c = γ₁₀`
- The anomaly terms cancel because `α - α² * π²/3 = 0` when `α = 3/π²`
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-! ## Helper lemmas for derivative of anomaly function D₂ -/

/-- The D-derivative of the anomaly function D₂.
    D₂ γ z = 2πi · (γ₁₀ / denom γ z), so
    D(D₂ γ) = (2πi)⁻¹ · d/dz[2πi · c / denom] = -c² / denom² -/
lemma D_D₂ (γ : SL(2, ℤ)) (z : ℍ) :
    D (D₂ γ) z = - (γ 1 0 : ℂ)^2 / (denom γ z)^2 := by
  unfold D
  set c : ℂ := (γ 1 0 : ℂ) with hc_def
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hcomp : deriv ((D₂ γ) ∘ ofComplex) z =
      deriv (fun w => (2 * π * I * c) / (denom γ w)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, D₂, coe_mk_subtype, ← hc_def]
  rw [hcomp]
  have hdiv_eq : (fun w => (2 * π * I * c) / (denom γ w)) =
      (fun w => (2 * π * I * c) * (denom γ w)^(-1 : ℤ)) := by
    ext w
    simp only [zpow_neg_one, div_eq_mul_inv]
  rw [hdiv_eq]
  have hdiff_denom_inv : DifferentiableAt ℂ (fun w => (denom γ w)^(-1 : ℤ)) z := by
    apply DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl hz_denom_ne)
  have hderiv_const_mul : deriv (fun w => (2 * π * I * c) * (denom γ w)^(-1 : ℤ)) z =
      (2 * π * I * c) * deriv (fun w => (denom γ w)^(-1 : ℤ)) z := by
    exact deriv_const_mul (2 * π * I * c) hdiff_denom_inv
  rw [hderiv_const_mul]
  have hderiv_zpow := deriv_denom_zpow γ 1 (z : ℂ) hz_denom_ne
  -- The simp args neg_neg and zpow_one normalize the expression for subsequent rw
  set_option linter.unusedSimpArgs false in
  simp only [Int.reduceNeg, neg_neg, zpow_one] at hderiv_zpow
  rw [hderiv_zpow]
  have h2piI_ne : (2 * π * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero,
      or_self, not_false_eq_true]
  simp only [Int.reduceNeg, Int.reduceSub, hc_def]
  field_simp
  ring

/-! ## MDifferentiable infrastructure for D₂ -/

/-- D₂ γ is MDifferentiable: it's a constant divided by a linear polynomial. -/
lemma MDifferentiable_D₂ (γ : SL(2, ℤ)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (D₂ γ) := by
  intro z
  set G : ℂ → ℂ := fun w => (2 * π * I * (γ 1 0 : ℂ)) / denom γ w with hG_def
  have heq : D₂ γ = G ∘ (↑) := by ext w; rfl
  rw [heq]
  apply DifferentiableAt_MDifferentiableAt
  apply DifferentiableAt.div (differentiableAt_const _) (differentiableAt_denom γ z)
  exact UpperHalfPlane.denom_ne_zero γ z

/-! ## Slash invariance of serre_D 1 E₂

This is the hard part: E₂ is NOT modular, so we cannot use `serre_D_slash_invariant`.
We must prove directly that the non-modular terms cancel. -/

/-- The Serre derivative of E₂ is weight-4 slash-invariant.
This requires explicit computation since E₂ is not modular.

**Proof strategy:**
Write serre_D 1 E₂ = serre_D 2 E₂ + (1/12) E₂². Then:
- (serre_D 2 E₂) ∣[4] γ = serre_D 2 (E₂ ∣[2] γ) by serre_D_slash_equivariant
- E₂ ∣[2] γ = E₂ - α D₂ γ where α = 1/(2ζ(2)) = 3/π²
- (E₂²) ∣[4] γ = (E₂ ∣[2] γ)²

After expansion, the anomaly terms involving D₂ γ and D(D₂ γ) cancel using:
- D(D₂ γ) = -c²/denom² (from D_D₂)
- The identity α = α² π²/3 (from ζ(2) = π²/6)
-/
lemma serre_D_E₂_slash_invariant (γ : SL(2, ℤ)) :
    (serre_D 1 E₂) ∣[(4 : ℤ)] γ = serre_D 1 E₂ := by
  have hserre12 : serre_D 1 E₂ = serre_D 2 E₂ + (1 / 12 : ℂ) • (E₂ * E₂) := by
    ext z; simp only [serre_D, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  have hequiv := serre_D_slash_equivariant 2 E₂ E₂_holo' γ
  have hE₂slash := E₂_slash_transform γ
  have hprod := ModularForm.mul_slash_SL2 (2 : ℤ) (2 : ℤ) γ E₂ E₂
  ext z
  rw [hserre12]
  simp only [SlashAction.add_slash, Pi.add_apply]
  have hsmul := ModularForm.SL_smul_slash (4 : ℤ) γ (E₂ * E₂) (1 / 12 : ℂ)
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hequiv_z : (serre_D 2 E₂ ∣[(4 : ℤ)] γ) z = serre_D 2 (E₂ ∣[(2 : ℤ)] γ) z := by
    have h := congrFun hequiv z
    simp only [Int.reduceAdd] at h
    exact h
  rw [hequiv_z]
  have hprod_z : ((E₂ * E₂) ∣[(4 : ℤ)] γ) z = (E₂ ∣[(2 : ℤ)] γ) z * (E₂ ∣[(2 : ℤ)] γ) z := by
    have h := congrFun hprod z
    simp only [Pi.mul_apply, Int.reduceAdd] at h
    exact h
  rw [hprod_z]
  set α := (1 : ℂ) / (2 * riemannZeta 2) with hα_def
  have hE₂slash_z : (E₂ ∣[(2 : ℤ)] γ) z = E₂ z - α * D₂ γ z := by
    have h := congrFun hE₂slash z
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hE₂slash_fun : (E₂ ∣[(2 : ℤ)] γ) = E₂ - α • D₂ γ := by
    ext w
    have h := congrFun hE₂slash w
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  rw [hE₂slash_fun]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hD_lin : D (E₂ - α • D₂ γ) z = D E₂ z - α * D (D₂ γ) z := by
    have hαD₂ := (MDifferentiable_D₂ γ).const_smul α
    simp only [D_sub E₂ _ E₂_holo' hαD₂, D_smul α _ (MDifferentiable_D₂ γ),
               Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hDd : D (D₂ γ) z = -(γ 1 0 : ℂ)^2 / (denom γ z)^2 := D_D₂ γ z
  have hd_sq : D₂ γ z * D₂ γ z = -4 * π^2 * (γ 1 0 : ℂ)^2 / (denom γ z)^2 := by
    have hden_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
    have hI_sq : (I : ℂ)^2 = -1 := Complex.I_sq
    simp only [D₂]
    field_simp [hden_ne]
    ring_nf
    simp only [hI_sq]
    ring
  simp only [serre_D, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [hD_lin, hDd]
  have hα_val : α = 3 / π^2 := by
    simp only [hα_def]
    rw [riemannZeta_two]
    have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi_ne]
    ring
  have hden_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hpi_ne : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hD₂_eq : D₂ γ z = (2 * π * I * (γ 1 0 : ℂ)) / denom γ z := rfl
  rw [hD₂_eq, hα_val]
  field_simp [hden_ne, hpi_ne]
  have hI_sq : (I : ℂ)^2 = -1 := Complex.I_sq
  ring_nf
  simp only [hI_sq]
  ring
