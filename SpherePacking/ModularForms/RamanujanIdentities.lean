import SpherePacking.ModularForms.EisensteinAsymptotics

/-!
# Ramanujan's Identities for Eisenstein Series

This file contains the Ramanujan identities for Eisenstein series (Blueprint Theorem 6.50).

## Main results

* `ramanujan_E₂'` : `serre_D 1 E₂ = -E₄/12` (requires explicit computation since E₂ is not modular)
* `ramanujan_E₄'` : `serre_D 4 E₄ = -E₆/3` (uses dimension formula for weight-6 forms)
* `ramanujan_E₆'` : `serre_D 6 E₆ = -E₄²/2` (uses dimension formula for weight-8 forms)

## Derived identities

* `ramanujan_E₂` : `D E₂ = (E₂² - E₄)/12`
* `ramanujan_E₄` : `D E₄ = (E₂·E₄ - E₆)/3`
* `ramanujan_E₆` : `D E₆ = (E₂·E₆ - E₄²)/2`

## MLDE for F

* `MLDE_F` : The modular linear differential equation satisfied by F
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-! ## The Ramanujan Identities

These are the main theorems. The primed versions are in terms of serre_D,
the non-primed versions are in terms of D. -/

/-- Determine scalar coefficient from limits: if `f = c * g` pointwise,
`f(iy) → L`, and `g(iy) → 1` as `y → ∞`, then `c = L`.

This captures the "uniqueness of limits" argument used in dimension-1 proofs. -/
lemma scalar_eq_of_tendsto {f g : ℍ → ℂ} {c L : ℂ}
    (hfun : ∀ z, f z = c * g z)
    (hf_lim : Filter.Tendsto (f ∘ iMulPosReal) (Filter.comap Subtype.val Filter.atTop) (nhds L))
    (hg_lim : Filter.Tendsto (g ∘ iMulPosReal) (Filter.comap Subtype.val Filter.atTop) (nhds 1)) :
    c = L := by
  have hlim_c : Filter.Tendsto (fun y => c * g (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds c) := by
    simpa using tendsto_const_nhds.mul hg_lim
  have hlim_eq : Filter.Tendsto (f ∘ iMulPosReal)
      (Filter.comap Subtype.val Filter.atTop) (nhds c) := by
    convert hlim_c using 1; ext y; exact hfun (iMulPosReal y)
  exact (tendsto_nhds_unique hf_lim hlim_eq).symm

/--
Serre derivative of E₂: `serre_D 1 E₂ = - 12⁻¹ * E₄`.

This is the hardest identity because E₂ is not modular.
The proof uses:
1. `serre_D_E₂_slash_invariant`: serre_D 1 E₂ is weight-4 slash-invariant
2. Bounded at infinity: serre_D 1 E₂ = D E₂ - (1/12) E₂², both terms bounded
3. Dimension formula: weight-4 forms are 1-dimensional, spanned by E₄
4. Constant term: serre_D 1 E₂(iy) → -1/12 as y → ∞
-/
theorem ramanujan_E₂' : serre_D 1 E₂ = - 12⁻¹ * E₄.toFun := by
  -- Use dimension argument
  have hrank : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) 4) = 1 :=
    weight_four_one_dimensional
  -- Apply finrank_eq_one_iff_of_nonzero' to get that serre_D_E₂_ModularForm = c * E₄
  have hE₄_ne : E₄ ≠ 0 := E4_ne_zero
  rw [Module.rank_eq_one_iff_finrank_eq_one] at hrank
  have := (finrank_eq_one_iff_of_nonzero' E₄ hE₄_ne).mp hrank serre_D_E₂_ModularForm
  obtain ⟨c, hc⟩ := this
  -- hc : c • E₄ = serre_D_E₂_ModularForm, so serre_D_E₂_ModularForm = c • E₄
  -- We need to show c = -1/12
  -- First establish that serre_D 1 E₂ equals c * E₄ as functions
  have hcoe : (serre_D_E₂_ModularForm : ℍ → ℂ) = serre_D 1 E₂ := rfl
  -- From hc : c • E₄ = serre_D_E₂_ModularForm, we get the function equality
  have hfun : ∀ z, serre_D 1 E₂ z = c * E₄.toFun z := by
    intro z
    rw [← hcoe]
    have := congrFun (congrArg (↑· : ModularForm _ _ → ℍ → ℂ) hc.symm) z
    -- Args needed for normalization even if linter says unused
    set_option linter.unusedSimpArgs false in
    simp only [ModularForm.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    exact this
  -- Determine c = -1/12 using limit uniqueness
  have hc_val : c = -(1/12 : ℂ) :=
    scalar_eq_of_tendsto hfun serre_D_E₂_tendsto_at_infinity E₄_tendsto_one_at_infinity
  -- Now substitute c = -1/12
  ext z
  rw [hfun z, hc_val]
  -- Simplify Pi.mul_apply and constant function coercion
  simp only [Pi.mul_apply]
  -- Goal: -(1 / 12) * E₄.toFun z = (-12⁻¹) z * E₄.toFun z
  -- The (-12⁻¹) z is a constant function evaluated at z, which equals -12⁻¹
  congr 1
  norm_num

/-- Serre derivative of E₄: `serre_D 4 E₄ = - 3⁻¹ * E₆`.

Uses the dimension argument:
1. serre_D 4 E₄ is weight-6 slash-invariant (by serre_D_slash_invariant)
2. serre_D 4 E₄ is bounded at infinity (serre_D_E₄_isBoundedAtImInfty)
3. Weight-6 modular forms are 1-dimensional (weight_six_one_dimensional)
4. Constant term is -1/3 (from D E₄ → 0, E₂ → 1, E₄ → 1)
-/
theorem ramanujan_E₄' : serre_D 4 E₄.toFun = - 3⁻¹ * E₆.toFun := by
  -- Use the dimension argument
  -- serre_D_E₄_ModularForm gives us a ModularForm Γ(1) 6
  -- weight_six_one_dimensional says the space is 1-dimensional, spanned by E₆
  -- So serre_D 4 E₄ = c * E₆ for some c
  -- serre_D_E₄_tendsto_at_infinity gives c = -1/3
  have hrank : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) 6) = 1 :=
    weight_six_one_dimensional
  -- Apply finrank_eq_one_iff_of_nonzero' to get that serre_D_E₄_ModularForm = c * E₆
  have hE₆_ne : E₆ ≠ 0 := E6_ne_zero
  rw [Module.rank_eq_one_iff_finrank_eq_one] at hrank
  have := (finrank_eq_one_iff_of_nonzero' E₆ hE₆_ne).mp hrank serre_D_E₄_ModularForm
  obtain ⟨c, hc⟩ := this
  -- hc : c • E₆ = serre_D_E₄_ModularForm, so serre_D_E₄_ModularForm = c • E₆
  -- We need to show c = -1/3
  -- First establish that serre_D 4 E₄ equals c * E₆ as functions
  have hcoe : (serre_D_E₄_ModularForm : ℍ → ℂ) = serre_D 4 E₄.toFun := rfl
  -- From hc : c • E₆ = serre_D_E₄_ModularForm, we get the function equality
  have hfun : ∀ z, serre_D 4 E₄.toFun z = c * E₆.toFun z := by
    intro z
    rw [← hcoe]
    have := congrFun (congrArg (↑· : ModularForm _ _ → ℍ → ℂ) hc.symm) z
    -- Args needed for normalization even if linter says unused
    set_option linter.unusedSimpArgs false in
    simp only [ModularForm.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    exact this
  -- Determine c = -1/3 using limit uniqueness
  have hc_val : c = -(1/3 : ℂ) :=
    scalar_eq_of_tendsto hfun serre_D_E₄_tendsto_at_infinity E₆_tendsto_one_at_infinity
  ext z
  rw [hfun z, hc_val]
  -- Simplify Pi.mul_apply and constant function coercion
  simp only [Pi.mul_apply]
  -- Goal: -(1 / 3) * E₆.toFun z = (-3⁻¹) z * E₆.toFun z
  -- The (-3⁻¹) z is a constant function evaluated at z, which equals -3⁻¹
  -- Convert to same form
  congr 1
  norm_num

/-- Serre derivative of E₆: `serre_D 6 E₆ = - 2⁻¹ * E₄²`.

Uses the dimension argument:
1. serre_D 6 E₆ is weight-8 slash-invariant (by serre_D_slash_invariant)
2. Weight-8 modular forms are 1-dimensional, spanned by E₄²
3. Constant term is -1/2 (from D E₆ → 0, E₂ → 1, E₆ → 1)
-/
theorem ramanujan_E₆' : serre_D 6 E₆.toFun = - 2⁻¹ * E₄.toFun * E₄.toFun := by
  -- Similar to ramanujan_E₄' but for weight 8
  -- E₄² is a weight-8 modular form via ModularForm.mul
  let E₄_sq : ModularForm (CongruenceSubgroup.Gamma 1) 8 :=
    have h : (4 : ℤ) + 4 = 8 := by norm_num
    h ▸ ModularForm.mul E₄ E₄
  -- Weight-8 is 1-dimensional
  have hrank : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) 8) = 1 :=
    weight_eight_one_dimensional 8 (by norm_num : (3 : ℤ) ≤ 8) ⟨4, rfl⟩ (by norm_num : 8 < 12)
  -- E₄² is nonzero
  have hE₄_sq_ne : E₄_sq ≠ 0 := by
    simp only [ne_eq, E₄_sq]
    intro h
    -- If E₄ * E₄ = 0 as modular form, then E₄ = 0
    have hE₄_ne := E4_ne_zero
    -- h : (4 + 4 = 8) ▸ (E₄.mul E₄) = 0
    -- Extract that E₄ * E₄ = 0 as functions
    have h' : (E₄.mul E₄ : ℍ → ℂ) = 0 := by
      ext z
      have := congrFun (congrArg (↑· : ModularForm _ _ → ℍ → ℂ) h) z
      simp only [ModularForm.coe_mul, Pi.mul_apply, ModularForm.coe_zero, Pi.zero_apply] at this
      exact this
    -- E₄ z * E₄ z = 0 for all z, so E₄ z = 0 for all z
    have h'' : ∀ z : ℍ, E₄.toFun z = 0 := fun z => by
      have := congrFun h' z
      simp only [ModularForm.coe_mul, Pi.mul_apply, Pi.zero_apply] at this
      exact mul_self_eq_zero.mp this
    -- This means E₄ = 0 as a function, contradicting E4_ne_zero
    apply hE₄_ne
    ext z
    simp only [ModularForm.coe_zero, Pi.zero_apply]
    exact h'' z
  rw [Module.rank_eq_one_iff_finrank_eq_one] at hrank
  have := (finrank_eq_one_iff_of_nonzero' E₄_sq hE₄_sq_ne).mp hrank serre_D_E₆_ModularForm
  obtain ⟨c, hc⟩ := this
  -- hc : c • E₄_sq = serre_D_E₆_ModularForm
  -- So serre_D_E₆_ModularForm = c * E₄²
  have hcoe : (serre_D_E₆_ModularForm : ℍ → ℂ) = serre_D 6 E₆.toFun := rfl
  have hfun : ∀ z, serre_D 6 E₆.toFun z = c * (E₄.toFun z * E₄.toFun z) := by
    intro z
    rw [← hcoe]
    have := congrFun (congrArg (↑· : ModularForm _ _ → ℍ → ℂ) hc.symm) z
    -- Args needed for normalization even if linter says unused
    set_option linter.unusedSimpArgs false in
    simp only [ModularForm.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    -- Need to relate E₄_sq to E₄.toFun * E₄.toFun
    -- E₄_sq = (4 + 4 = 8) ▸ (E₄.mul E₄), so the underlying function is E₄ * E₄
    -- The ▸ cast preserves function values
    convert this using 2
  -- Determine c = -1/2 using limit uniqueness (E₄² → 1² = 1)
  have hc_val : c = -(1/2 : ℂ) := by
    have hlim_E₄_sq : Filter.Tendsto ((fun z => E₄.toFun z * E₄.toFun z) ∘ iMulPosReal)
        (Filter.comap Subtype.val Filter.atTop) (nhds 1) := by
      simpa using E₄_tendsto_one_at_infinity.mul E₄_tendsto_one_at_infinity
    exact scalar_eq_of_tendsto hfun serre_D_E₆_tendsto_at_infinity hlim_E₄_sq
  ext z
  rw [hfun z, hc_val]
  simp only [Pi.mul_apply]
  -- Goal: -(1/2) * (E₄.toFun z * E₄.toFun z) = (-2⁻¹) z * E₄.toFun z * E₄.toFun z
  -- The (-2⁻¹) z is a constant function evaluated at z, which equals -2⁻¹
  ring_nf
  congr 1
  norm_num

/-! ## Derived Ramanujan identities (D instead of serre_D) -/

@[simp]
theorem ramanujan_E₂ : D E₂ = 12⁻¹ * (E₂ * E₂ - E₄.toFun) := by
  -- From ramanujan_E₂': serre_D 1 E₂ = -12⁻¹ * E₄
  -- serre_D 1 E₂ = D E₂ - (1/12) * E₂ * E₂
  -- So: D E₂ - (1/12) * E₂² = -12⁻¹ * E₄
  -- Hence: D E₂ = (1/12) * E₂² - (1/12) * E₄ = (1/12) * (E₂² - E₄)
  have h := ramanujan_E₂'
  ext z
  unfold serre_D at h
  have hz := congrFun h z
  simp only [Pi.mul_apply] at hz
  -- Simplify constant function: (-12⁻¹) z = -12⁻¹
  have hconst : (-12⁻¹ : ℍ → ℂ) z = -12⁻¹ := rfl
  rw [hconst] at hz
  -- hz : D E₂ z - 1 * 12⁻¹ * E₂ z * E₂ z = -12⁻¹ * E₄.toFun z
  have step1 : D E₂ z = 1 * 12⁻¹ * E₂ z * E₂ z - 12⁻¹ * E₄.toFun z := by
    calc D E₂ z
        = (D E₂ z - 1 * 12⁻¹ * E₂ z * E₂ z) + 1 * 12⁻¹ * E₂ z * E₂ z := by ring
      _ = -12⁻¹ * E₄.toFun z + 1 * 12⁻¹ * E₂ z * E₂ z := by rw [hz]
      _ = 1 * 12⁻¹ * E₂ z * E₂ z - 12⁻¹ * E₄.toFun z := by ring
  -- Simplify 1 * 12⁻¹ = 12⁻¹
  simp only [one_mul] at step1
  rw [step1]
  -- Simplify the goal - Pi args normalize constant functions
  set_option linter.unusedSimpArgs false in
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.inv_apply, Pi.ofNat_apply]
  ring

@[simp]
theorem ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun) := by
  -- From ramanujan_E₄': serre_D 4 E₄ = -1/3 * E₆
  -- serre_D 4 E₄ = D E₄ - (4/12) * E₂ * E₄ = D E₄ - (1/3) * E₂ * E₄
  -- So: D E₄ - (1/3) * E₂ * E₄ = -1/3 * E₆
  -- Hence: D E₄ = (1/3) * E₂ * E₄ - (1/3) * E₆ = (1/3) * (E₂ * E₄ - E₆)
  have h := ramanujan_E₄'
  ext z
  unfold serre_D at h
  have hz := congrFun h z
  simp only [Pi.mul_apply] at hz
  -- Simplify constant function: (-3⁻¹) z = -3⁻¹
  have hconst : (-3⁻¹ : ℍ → ℂ) z = -3⁻¹ := rfl
  rw [hconst] at hz
  -- hz : D E₄.toFun z - 4 * 12⁻¹ * E₂ z * E₄.toFun z = -3⁻¹ * E₆.toFun z
  have step1 : D E₄.toFun z = 4 * 12⁻¹ * E₂ z * E₄.toFun z - 3⁻¹ * E₆.toFun z := by
    calc D E₄.toFun z
        = (D E₄.toFun z - 4 * 12⁻¹ * E₂ z * E₄.toFun z) + 4 * 12⁻¹ * E₂ z * E₄.toFun z := by ring
      _ = -3⁻¹ * E₆.toFun z + 4 * 12⁻¹ * E₂ z * E₄.toFun z := by rw [hz]
      _ = 4 * 12⁻¹ * E₂ z * E₄.toFun z - 3⁻¹ * E₆.toFun z := by ring
  -- 4/12 = 1/3
  have h412 : (4 : ℂ) * 12⁻¹ = 3⁻¹ := by norm_num
  rw [h412] at step1
  rw [step1]
  -- Simplify the goal - Pi args normalize constant functions
  set_option linter.unusedSimpArgs false in
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.inv_apply, Pi.ofNat_apply]
  ring

@[simp]
theorem ramanujan_E₆ : D E₆.toFun = 2⁻¹ * (E₂ * E₆.toFun - E₄.toFun * E₄.toFun) := by
  -- From ramanujan_E₆': serre_D 6 E₆ = -1/2 * E₄²
  -- serre_D 6 E₆ = D E₆ - (6/12) * E₂ * E₆ = D E₆ - (1/2) * E₂ * E₆
  -- So: D E₆ - (1/2) * E₂ * E₆ = -1/2 * E₄²
  -- Hence: D E₆ = (1/2) * E₂ * E₆ - (1/2) * E₄² = (1/2) * (E₂ * E₆ - E₄²)
  have h := ramanujan_E₆'
  ext z
  unfold serre_D at h
  have hz := congrFun h z
  simp only [Pi.mul_apply] at hz
  -- hz has (-2⁻¹) z which is the constant function evaluated at z, equal to -2⁻¹
  -- Need to simplify constant functions
  have hconst : (-2⁻¹ : ℍ → ℂ) z = -2⁻¹ := rfl
  rw [hconst] at hz
  -- hz : D E₆.toFun z - 6 * 12⁻¹ * E₂ z * E₆.toFun z = -2⁻¹ * E₄.toFun z * E₄.toFun z
  have step1 : D E₆.toFun z = 6 * 12⁻¹ * E₂ z * E₆.toFun z - 2⁻¹ * E₄.toFun z * E₄.toFun z := by
    calc D E₆.toFun z
        = (D E₆.toFun z - 6 * 12⁻¹ * E₂ z * E₆.toFun z) + 6 * 12⁻¹ * E₂ z * E₆.toFun z := by ring
      _ = -2⁻¹ * E₄.toFun z * E₄.toFun z + 6 * 12⁻¹ * E₂ z * E₆.toFun z := by rw [hz]
      _ = 6 * 12⁻¹ * E₂ z * E₆.toFun z - 2⁻¹ * E₄.toFun z * E₄.toFun z := by ring
  -- 6/12 = 1/2
  have h612 : (6 : ℂ) * 12⁻¹ = 2⁻¹ := by norm_num
  rw [h612] at step1
  rw [step1]
  -- Simplify the goal - Pi args normalize constant functions
  set_option linter.unusedSimpArgs false in
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.inv_apply, Pi.ofNat_apply]
  ring

/-! ## Applications of Ramanujan identities -/

section Ramanujan_qExpansion

open scoped ArithmeticFunction.sigma

/--
Helper: D applied to exp(2πinz) gives n * exp(2πinz).
This follows from: d/dz[exp(2πinz)] = 2πin * exp(2πinz),
so D[exp(2πinz)] = (2πi)⁻¹ * 2πin * exp(2πinz) = n * exp(2πinz).
-/
lemma D_exp_eq_n_mul (n : ℕ) (z : ℍ) :
    D (fun w : ℍ => cexp (2 * π * I * n * w)) z = n * cexp (2 * π * I * n * z) := by
  unfold D
  -- The key: (f ∘ ofComplex) agrees with f on the upper half-plane
  -- So their derivatives agree at points in ℍ
  have hcomp : deriv ((fun w : ℍ => cexp (2 * π * I * n * w)) ∘ ofComplex) z =
      deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rfl
  rw [hcomp]
  -- deriv of exp(c*z) is c*exp(c*z)
  have hderiv : deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z =
      (2 * π * I * n) * cexp (2 * π * I * n * z) := by
    -- Use the derivative chain rule lemma directly
    have hdiff_lin : DifferentiableAt ℂ (fun w => 2 * π * I * n * w) (z : ℂ) := by fun_prop
    have hderiv_lin : deriv (fun w : ℂ => 2 * π * I * n * w) (z : ℂ) = 2 * π * I * n := by
      rw [deriv_const_mul _ differentiableAt_id]
      simp only [deriv_id'', mul_one]
    calc deriv (fun w : ℂ => cexp (2 * π * I * n * w)) z
        = cexp (2 * π * I * n * z) * deriv (fun w => 2 * π * I * n * w) z := by
            exact deriv_cexp hdiff_lin
      _ = cexp (2 * π * I * n * z) * (2 * π * I * n) := by rw [hderiv_lin]
      _ = (2 * π * I * n) * cexp (2 * π * I * n * z) := by ring
  rw [hderiv]
  -- Simplify (2πi)⁻¹ * (2πin) = n
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  field_simp

/--
Key identity: The double sum ∑' (c,d), c * d^(k+1) * exp(2πi*z*cd) equals
∑' n, n * σ_k(n) * exp(2πi*n*z).
This follows from σ_k(n) = ∑_{d|n} d^k and n * σ_k(n) = ∑_{cd=n} c * d^(k+1).

The proof uses `tsum_sigma_eqn` and differentiation multiplies by the exponent factor.
-/
lemma tsum_sigma_deriv_eq {k : ℕ} (z : ℍ) :
    ∑' c : ℕ+ × ℕ+, (c.1 : ℂ) * (c.2 : ℂ) ^ (k + 1) * cexp (2 * π * I * z * c.1 * c.2) =
    ∑' n : ℕ+, (n : ℂ) * (σ k n : ℂ) * cexp (2 * π * I * n * z) := by
  -- The key identity: for each n, ∑_{cd=n} c * d^(k+1) = n * σ_k(n)
  -- Proof: ∑_{cd=n} c * d^(k+1) = ∑_{d|n} (n/d) * d^(k+1) = ∑_{d|n} n * d^k = n * σ_k(n)
  --
  -- Use sigmaAntidiagonalEquivProd to convert pairs (c,d) to divisor sums
  rw [← sigmaAntidiagonalEquivProd.tsum_eq]
  simp only [sigmaAntidiagonalEquivProd, mapdiv, PNat.mk_coe, Equiv.coe_fn_mk]
  -- Use summability to convert tsum over sigma to tsum over ℕ+
  have hsumm : Summable (fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
      (↑(c.snd.val.1) : ℂ) * ↑(c.snd.val.2) ^ (k + 1) *
      cexp (2 * π * I * z * c.snd.val.1 * c.snd.val.2)) := by
    -- Summability follows from bounds adapting summable_auxil_1:
    -- For (a,b) ∈ divisorsAntidiagonal n: a * b = n, so
    --   a * b^(k+1) = n * b^k ≤ n^(k+1) (since b | n implies b ≤ n)
    --   |exp(2πi*z*ab)| = |exp(2πi*n*z)| (exponential decay)
    -- Sum over divisors: card(divisors) * n^(k+1) * |exp| ≤ n^(k+2) * |exp|
    -- Outer sum converges by hsum (k+2) z
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg]
    constructor
    · -- Each inner sum over divisorsAntidiagonal is finite
      intro n
      exact (hasSum_fintype _).summable
    · -- Outer sum of norms converges
      simp only [Complex.norm_mul, norm_pow, RCLike.norm_natCast, tsum_fintype,
        Finset.univ_eq_attach]
      have H (n : ℕ+) := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
        (x.1 : ℝ) * (x.2 : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * x.1 * x.2)‖)
      have H2 (n : ℕ+) := Nat.sum_divisorsAntidiagonal ((fun (x : ℕ) => fun (y : ℕ) =>
        (x : ℝ) * (y : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * x * y)‖)) (n := n)
      conv =>
        enter [1]
        ext b
        simp
        rw [H b]
        rw [H2 b]
      -- Bound each divisor sum by n^(k+1) * |exp(2πi*n*z)| * card(divisors)
      have hsum_bound := hsum (k + 1) z
      apply Summable.of_nonneg_of_le _ _ hsum_bound
      · intro b
        apply Finset.sum_nonneg
        intro i _
        apply mul_nonneg (mul_nonneg _ _) (norm_nonneg _)
        · exact Nat.cast_nonneg _
        · exact pow_nonneg (Nat.cast_nonneg _) _
      · intro b
        apply Finset.sum_le_sum
        intro i hi
        simp only [Nat.mem_divisors, ne_eq, PNat.ne_zero, not_false_eq_true, and_true] at hi
        -- After Nat.sum_divisorsAntidiagonal: term is i * (b/i)^(k+1) * ‖exp(...)‖
        -- For i | b: i * (b/i) = b
        have hdvd : i ∣ (b : ℕ) := hi
        have hi_pos : 0 < i := Nat.pos_of_ne_zero (fun h => by simp [h] at hdvd)
        have hquot_le_b : (b : ℕ) / i ≤ (b : ℕ) := Nat.div_le_self _ _
        have hprod : i * ((b : ℕ) / i) = (b : ℕ) := Nat.mul_div_cancel' hdvd
        -- Bound: i * (b/i)^(k+1) = i * (b/i) * (b/i)^k = b * (b/i)^k ≤ b * b^k = b^(k+1)
        -- Let q = (b : ℕ) / i for clarity
        set q := (b : ℕ) / i with hq_def
        have hcoeff_le : (i : ℝ) * (q : ℝ) ^ (k + 1) ≤ (b : ℝ) ^ (k + 1) := by
          calc (i : ℝ) * (q : ℝ) ^ (k + 1)
              = (i : ℝ) * (q : ℝ) * (q : ℝ) ^ k := by ring
            _ = ((i * q : ℕ) : ℝ) * (q : ℝ) ^ k := by rw [← Nat.cast_mul]
            _ = (b : ℝ) * (q : ℝ) ^ k := by rw [hq_def, hprod]
            _ ≤ (b : ℝ) * (b : ℝ) ^ k := by gcongr
            _ = (b : ℝ) ^ (k + 1) := by ring
        -- Exponential: i * q = b, so exp(2πi*z*i*q) = exp(2πi*z*b)
        have hexp_eq : ‖cexp (2 * π * I * z * i * q)‖ = ‖cexp (2 * π * I * z * b)‖ := by
          congr 1
          congr 1
          calc (2 : ℂ) * π * I * z * i * q
              = 2 * π * I * z * ((i * q : ℕ) : ℂ) := by simp only [Nat.cast_mul]; ring
            _ = 2 * π * I * z * (b : ℕ) := by rw [hq_def, hprod]
            _ = 2 * π * I * z * ↑↑b := by simp
        calc (i : ℝ) * (q : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * i * q)‖
            = (i : ℝ) * (q : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * b)‖ := by rw [hexp_eq]
          _ ≤ (b : ℝ) ^ (k + 1) * ‖cexp (2 * π * I * z * b)‖ := by gcongr
    · intro _
      exact norm_nonneg _
  rw [hsumm.tsum_sigma]
  apply tsum_congr
  intro n
  rw [tsum_fintype, Finset.univ_eq_attach]
  -- For each n, show ∑_{(c,d) with cd=n} c * d^(k+1) = n * σ_k(n)
  have hdiv := @Nat.sum_divisorsAntidiagonal' ℂ _ (fun (x : ℕ) => fun (y : ℕ) =>
    (x : ℂ) * (y : ℂ) ^ (k + 1) * cexp (2 * π * I * z * x * y)) n
  simp only at hdiv
  have H := Finset.sum_attach ((n : ℕ).divisorsAntidiagonal) (fun (x : ℕ × ℕ) =>
    (x.1 : ℂ) * (x.2 : ℂ) ^ (k + 1) * cexp (2 * π * I * z * x.1 * x.2))
  simp only at H
  rw [H, hdiv]
  -- Now show: ∑_{i|n} ↑(n/i) * i^(k+1) * exp(2πi * z * ↑(n/i) * i) = n * σ_k(n) * exp(2πinz)
  -- Note: Nat.sum_divisorsAntidiagonal' produces ↑(↑n / i) which is ℕ division cast to ℂ
  --
  -- Key identity for i | n: ↑((n/i : ℕ) * i : ℕ) = ↑n via Nat.div_mul_cancel
  -- This gives: ↑(n/i) * ↑i = ↑n (using ← Nat.cast_mul)
  -- Then: ↑(n/i) * i^(k+1) = ↑(n/i) * i * i^k = n * i^k
  -- And: exp(2πi*z*↑(n/i)*i) = exp(2πi*n*z) since ↑(n/i)*i = n
  --
  -- Convert each term using ← Nat.cast_mul and Nat.div_mul_cancel
  have hterm_eq : ∀ i ∈ (n : ℕ).divisors,
      (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1) *
        cexp (2 * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) =
      (n : ℂ) * (i : ℂ) ^ k * cexp (2 * π * I * n * z) := by
    intro i hi
    have hdvd : i ∣ (n : ℕ) := Nat.dvd_of_mem_divisors hi
    -- Key: ↑((n/i) * i : ℕ) = ↑n, so ↑(n/i) * ↑i = ↑n
    have hprod : (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) = (n : ℂ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    -- Coefficient: ↑(n/i) * i^(k+1) = ↑(n/i) * i * i^k = n * i^k
    have hcoeff : (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1) = (n : ℂ) * (i : ℂ) ^ k := by
      calc (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) ^ (k + 1)
          = (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) * (i : ℂ) ^ k := by ring
        _ = (n : ℂ) * (i : ℂ) ^ k := by rw [hprod]
    -- Exponential: ↑(n/i) * i = n, so exp(...) = exp(2πi*n*z)
    -- Note: ((n : ℕ) / i) is ℕ division, which gets coerced to ℂ in this context
    have hexp : cexp (2 * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) =
        cexp (2 * π * I * n * z) := by
      congr 1
      -- Rearrange to use hprod: ↑(↑n/i) * ↑i = ↑↑n (without using push_cast)
      have hrearr : (2 : ℂ) * π * I * z * (((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ) =
          2 * π * I * z * ((((n : ℕ) / i : ℕ) : ℂ) * (i : ℂ)) := by ring
      rw [hrearr, hprod]
      ring
    rw [hcoeff, hexp]
  -- Apply the term rewrite to the sum using direct rewrites
  rw [Finset.sum_congr rfl hterm_eq, ← Finset.sum_mul, ← Finset.mul_sum]
  -- Now show: ∑ i ∈ n.divisors, (i : ℂ)^k = (σ k n : ℂ) using sigma_apply
  have hsigma_cast : ∑ i ∈ ((n : ℕ)).divisors, ((i : ℂ)) ^ k = ((σ k n) : ℂ) := by
    rw [ArithmeticFunction.sigma_apply]
    simp only [Nat.cast_sum, Nat.cast_pow]
  rw [hsigma_cast]

/--
The normalized derivative D multiplies q-expansion coefficients by n.
Since E₄ = 1 + 240·Σσ₃(n)·qⁿ, we have D(E₄) = 240·Σn·σ₃(n)·qⁿ.
-/
lemma D_E4_qexp (z : ℍ) :
    D E₄.toFun z = 240 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z) := by
  -- Step 1: Express E₄ using q-expansion
  -- E₄(z) = 1 + 240 * ∑' n : ℕ+, σ₃(n) * exp(2πi·z·n) from E_k_q_expansion
  have hE4 : ∀ w : ℍ, E₄.toFun w = 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n) := by
    intro w
    -- E₄.toFun = E₄ by coercion, and E₄ = E 4 by definition
    have hE : E₄.toFun w = E 4 (by norm_num) w := by rfl
    have hqexp := E_k_q_expansion 4 (by norm_num) (by exact Nat.even_iff.mpr rfl) w
    -- hqexp uses ↑4 while target uses 4; they are equal
    simp only [Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub, tsub_zero] at hqexp
    rw [hE, hqexp]
    -- Now goal is: 1 + (1/riemannZeta 4) * ((-2πi)^4 / 3!) * ∑'... = 1 + 240 * ...
    -- Need to show coefficient = 240
    -- Using riemannZeta_four : riemannZeta 4 = π^4 / 90
    congr 1
    have hzeta : riemannZeta 4 = (π : ℂ) ^ 4 / 90 := by
      simp only [riemannZeta_four]
    -- Coefficient = (1/(π^4/90)) * ((-2πi)^4 / 6) = (90/π^4) * (16π^4) / 6 = 240
    have hcoeff : (1 / riemannZeta 4) * ((-2 * π * I) ^ 4 / Nat.factorial 3) = (240 : ℂ) := by
      rw [hzeta]
      -- (-2πi)^4 = 16π^4 since I^4 = 1
      have hI4 : I ^ 4 = (1 : ℂ) := by norm_num [pow_succ, I_sq]
      have h1 : (-2 * (π : ℂ) * I) ^ 4 = 16 * (π : ℂ) ^ 4 := by
        have : (-2 * (π : ℂ) * I) ^ 4 = (-2) ^ 4 * (π : ℂ) ^ 4 * I ^ 4 := by ring
        rw [this, hI4]
        norm_num
      rw [h1]
      simp only [Nat.factorial_succ, Nat.reduceAdd]
      have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp
      ring
    convert mul_comm _ _ using 1
    rw [hcoeff]
    ring
  -- Step 2: Use deriv-tsum interchange
  unfold D
  have hz' : 0 < (z : ℂ).im := z.im_pos
  -- The composition E₄.toFun ∘ ofComplex agrees with the q-expansion on ℍ'
  have hE4' : ∀ w : ℂ, 0 < w.im →
      (E₄.toFun ∘ ofComplex) w = 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n) := by
    intro w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    exact hE4 ⟨w, hw⟩
  -- Replace deriv of E₄ with deriv of q-expansion form
  have hderiv_eq : deriv (E₄.toFun ∘ ofComplex) (z : ℂ) =
      deriv (fun w => 1 + 240 * ∑' (n : ℕ+), (σ 3 n) * cexp (2 * π * I * w * n)) (z : ℂ) := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz'] with w hw
    exact hE4' w hw
  rw [hderiv_eq]
  -- Now we need to interchange deriv with tsum
  -- Using hasDerivAt_tsum_fun from tsumderivWithin.lean
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  -- Define f n w := (σ 3 n) * cexp (2 * π * I * w * n)
  let f : ℕ+ → ℂ → ℂ := fun n w => (σ 3 n) * cexp (2 * π * I * w * n)
  -- Summability at each point
  have hf_summ : ∀ y : ℂ, 0 < y.im → Summable (fun n : ℕ+ => f n y) := by
    intro y hy
    -- |f n y| = |σ 3 n| * |exp(2πiny)| ≤ n^4 * r^n where r < 1
    -- This is summable as polynomial times geometric
    simp only [f]
    apply Summable.of_norm
    -- Use sigma_bound: σ 3 n ≤ n^4
    have hsigma_bound : ∀ n : ℕ+, (σ 3 n : ℝ) ≤ (n : ℕ) ^ 4 := fun n => by
      exact_mod_cast sigma_bound 3 n
    -- Construct UpperHalfPlane element
    let y_uhp : ℍ := ⟨y, hy⟩
    -- Use a33 with k=4 and e=1 for the bound
    have ha33 := a33 4 1 y_uhp
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_norm_iff.mpr ha33)
    intro n
    simp only [Complex.norm_mul, norm_pow]
    -- |σ 3 n| * |exp(...)| ≤ n^4 * |exp(...)|
    have hσ_norm : ‖(σ 3 n : ℂ)‖ ≤ (n : ℝ) ^ 4 := by
      rw [Complex.norm_natCast]
      exact hsigma_bound n
    have hy_coe : (y_uhp : ℂ) = y := rfl
    -- After simp, goal is: (σ 3 n : ℝ) * ‖exp(...)‖ ≤ ‖n‖^4 * ‖exp(...)‖
    -- (because simp uses Complex.norm_natCast on ‖σ 3 n‖)
    -- Rewrite exponent argument to match ha33 form
    have harg : cexp (2 * π * I * y * n) = cexp (2 * π * I * (1 : ℕ+) * (y_uhp : ℂ) * n) := by
      congr 1
      -- Args needed for expression normalization even if linter says unused
      set_option linter.unusedSimpArgs false in
      simp only [hy_coe, PNat.one_coe, Nat.cast_one, Complex.ofReal_one, mul_one]
    rw [harg]
    -- Goal: (σ 3 n : ℝ) * ‖exp(...)‖ ≤ ‖n‖^4 * ‖exp(...)‖
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    -- Goal: (σ 3 n : ℝ) ≤ ‖n‖^4 = (n : ℝ)^4
    rw [Complex.norm_natCast]
    exact_mod_cast hsigma_bound n
  -- Uniform derivative bound on compact sets
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ+ → ℝ, Summable u ∧
        ∀ (n : ℕ+) (k : K), ‖derivWithin (f n) {w | 0 < w.im} k‖ ≤ u n := by
    intro K hK hKc
    -- |deriv (f n)| = |σ 3 n| * |2πn| * |exp(...)| ≤ n^4 * 2πn * |exp(...)|
    -- Since n^4 * 2πn = n^5 * 2π ≤ (2πn)^5 (for n ≥ 1, 2π > 1)
    -- Use iter_deriv_comp_bound3 with k=5
    obtain ⟨u', hu'_sum, hu'_bound⟩ := iter_deriv_comp_bound3 K hK hKc 5
    use fun n => u' n
    constructor
    · exact hu'_sum.subtype _
    · intro n k
      rw [derivWithin_of_isOpen hopen (hK k.2)]
      simp only [f]
      have hderiv_fn : deriv (fun w => (σ 3 n : ℂ) * cexp (2 * π * I * w * n)) k =
          (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * k * n) := by
        rw [deriv_const_mul_field]
        have h_inner_fun : (fun w : ℂ => 2 * π * I * w * n) = (fun w => (2 * π * I * n) * w) := by
          ext w; ring
        have h_deriv_inner : deriv (fun w : ℂ => 2 * π * I * w * n) k = 2 * π * I * n := by
          rw [h_inner_fun, deriv_const_mul_field, deriv_id'', mul_one]
        rw [deriv_cexp (by fun_prop : DifferentiableAt ℂ (fun w => 2 * π * I * w * n) k)]
        rw [h_deriv_inner]
        ring
      rw [hderiv_fn]
      have hσ : ‖(σ 3 n : ℂ)‖ ≤ (n : ℝ) ^ 4 := by
        rw [Complex.norm_natCast]
        exact_mod_cast sigma_bound 3 n
      have h2pin : ‖(2 * π * I * n : ℂ)‖ = 2 * |π| * n := by
        simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_I, mul_one, Complex.norm_natCast]
      have hargswap : cexp (2 * π * I * k * n) = cexp (2 * π * I * n * k) := by
        congr 1; ring
      -- n^4 * 2πn ≤ (2πn)^5 since 2π ≥ 1 and n ≥ 1
      have hbound : (n : ℝ) ^ 4 * (2 * |π| * n) ≤ (2 * |π| * n) ^ 5 := by
        have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.one_le
        have hpi : 1 ≤ 2 * |π| := by
          have : (0 : ℝ) < π := Real.pi_pos
          simp only [abs_of_pos this]
          linarith [Real.pi_gt_three]
        calc (n : ℝ) ^ 4 * (2 * |π| * n)
            = (2 * |π|) * n ^ 5 := by ring
          _ ≤ (2 * |π|) ^ 5 * n ^ 5 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc (2 * |π|) = (2 * |π|) ^ 1 := by ring
                _ ≤ (2 * |π|) ^ 5 := pow_le_pow_right₀ hpi (by omega : 1 ≤ 5)
          _ = (2 * |π| * n) ^ 5 := by ring
      calc ‖(σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * k * n)‖
          = ‖(σ 3 n : ℂ)‖ * ‖(2 * π * I * n : ℂ)‖ * ‖cexp (2 * π * I * k * n)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ (n : ℝ) ^ 4 * (2 * |π| * n) * ‖cexp (2 * π * I * k * n)‖ := by
            rw [h2pin]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            apply mul_le_mul_of_nonneg_right hσ; positivity
        _ ≤ (2 * |π| * n) ^ 5 * ‖cexp (2 * π * I * n * k)‖ := by
            rw [hargswap]
            apply mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
        _ ≤ u' n := hu'_bound n k
  -- Each term is differentiable
  have hf_diff : ∀ (n : ℕ+) (r : {w : ℂ | 0 < w.im}), DifferentiableAt ℂ (f n) r := by
    intro n r
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.cexp
    fun_prop
  -- Apply hasDerivAt_tsum_fun
  have hderiv_tsum : HasDerivAt (fun w => ∑' n : ℕ+, f n w)
      (∑' n : ℕ+, derivWithin (f n) {w | 0 < w.im} z) (z : ℂ) :=
    hasDerivAt_tsum_fun f hopen (z : ℂ) hz' hf_summ hu hf_diff
  -- deriv (1 + 240 * tsum) = 240 * deriv(tsum)
  -- First rewrite to (240 * tsum + 1) form for deriv_add_const
  have hfun_eq : (fun w => 1 + 240 * ∑' (n : ℕ+), f n w) =
      (fun w => 240 * ∑' (n : ℕ+), f n w + 1) := by ext w; ring
  have hdiff_tsum : DifferentiableAt ℂ (fun w => ∑' (n : ℕ+), f n w) z :=
    hderiv_tsum.differentiableAt
  have hderiv_add : deriv (fun w => 1 + 240 * ∑' (n : ℕ+), f n w) (z : ℂ) =
      240 * deriv (fun w => ∑' (n : ℕ+), f n w) (z : ℂ) := by
    rw [hfun_eq, deriv_add_const, deriv_const_mul _ hdiff_tsum]
  rw [hderiv_add]
  -- Extract the deriv from HasDerivAt
  have hderiv_tsum_eq : deriv (fun w => ∑' n : ℕ+, f n w) (z : ℂ) =
      ∑' n : ℕ+, derivWithin (f n) {w | 0 < w.im} z := hderiv_tsum.deriv
  rw [hderiv_tsum_eq]
  -- Compute derivWithin of each term
  have hderiv_term : ∀ n : ℕ+, derivWithin (f n) {w | 0 < w.im} z =
      (σ 3 n) * (2 * π * I * n) * cexp (2 * π * I * z * n) := by
    intro n
    rw [derivWithin_of_isOpen hopen hz']
    -- Derivative of 2πI * w * n is 2πI * n
    have hlin_deriv : deriv (fun w : ℂ => 2 * π * I * w * n) z = 2 * π * I * n := by
      have : (fun w : ℂ => 2 * π * I * w * n) = fun w => (2 * π * I * n) * w := by ext; ring
      rw [this, deriv_const_mul, deriv_id'', mul_one]
      exact differentiableAt_id
    have hderiv_exp : deriv (fun w => cexp (2 * π * I * w * n)) z =
        (2 * π * I * n) * cexp (2 * π * I * z * n) := by
      rw [deriv_cexp (by fun_prop : DifferentiableAt ℂ (fun w => 2 * π * I * w * n) z)]
      rw [hlin_deriv]
      ring
    simp only [f]
    rw [deriv_const_mul_field, hderiv_exp]
    ring
  -- First rewrite the tsum using hderiv_term
  have htsum_eq : ∑' n : ℕ+, derivWithin (f n) {w | 0 < w.im} z =
      ∑' n : ℕ+, (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * z * n) :=
    tsum_congr hderiv_term
  rw [htsum_eq]
  -- Simplify: (2πi)⁻¹ * 240 * ∑ (σ 3 n) * (2πin) * exp(...) = 240 * ∑ n * (σ 3 n) * exp(...)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  -- Rewrite each term: (σ 3 n) * (2πIn) * exp(...) = (2πI) * n * (σ 3 n) * exp(...)
  have hterm_eq : ∀ n : ℕ+, (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * (z : ℂ) * n) =
      (2 * π * I) * (n * (σ 3 n) * cexp (2 * π * I * n * z)) := by
    intro n
    have hexp_eq : cexp (2 * π * I * (z : ℂ) * n) = cexp (2 * π * I * n * z) := by ring_nf
    rw [hexp_eq]
    ring
  have htsum_eq2 : ∑' n : ℕ+, (σ 3 n : ℂ) * (2 * π * I * n) * cexp (2 * π * I * (z : ℂ) * n) =
      (2 * π * I) * ∑' n : ℕ+, n * (σ 3 n) * cexp (2 * π * I * n * z) := by
    rw [tsum_congr hterm_eq, tsum_mul_left]
  rw [htsum_eq2]
  -- Goal: (2πI)⁻¹ * (240 * ((2πI) * ∑ (...))) = 240 * ∑ (...)
  -- Use calc to handle the algebra step by step
  let T := ∑' n : ℕ+, (n : ℂ) * (σ 3 n) * cexp (2 * π * I * n * z)
  -- Unfold to reveal T in goal
  change (2 * π * I)⁻¹ * (240 * ((2 * π * I) * T)) = 240 * T
  calc (2 * π * I)⁻¹ * (240 * ((2 * π * I) * T))
      = (2 * π * I)⁻¹ * (2 * π * I) * (240 * T) := by ring
    _ = 1 * (240 * T) := by rw [inv_mul_cancel₀ h2pi]
    _ = 240 * T := by ring

/--
The q-expansion identity E₂E₄ - E₆ = 720·Σn·σ₃(n)·qⁿ.
This follows from Ramanujan's formula: E₂E₄ - E₆ = 3·D(E₄),
combined with D(E₄) = 240·Σn·σ₃(n)·qⁿ (since D multiplies q-coefficients by n).
-/
theorem E₂_mul_E₄_sub_E₆ (z : ℍ) :
    (E₂ z) * (E₄ z) - (E₆ z) = 720 * ∑' (n : ℕ+), n * (σ 3 n) * cexp (2 * π * Complex.I * n * z)
    := by
  -- From ramanujan_E₄: D E₄ = (1/3) * (E₂ * E₄ - E₆)
  -- So: E₂ * E₄ - E₆ = 3 * D E₄
  have hRam : (E₂ z) * (E₄ z) - (E₆ z) = 3 * D E₄.toFun z := by
    -- ramanujan_E₄ : D E₄.toFun = 3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)
    -- Evaluating at z and rearranging gives the result
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    have h := congrFun ramanujan_E₄ z
    -- h : D E₄.toFun z = (3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)) z
    -- Instead of simp, unfold Pi.mul directly
    -- (c * f) z where c : ℂ and f : ℍ → ℂ evaluates to c * f z
    -- But the * here might be Pi.mul with c as constant function
    -- Let's work around by computing the value directly
    calc E₂ z * E₄ z - E₆ z
        = E₂ z * E₄.toFun z - E₆.toFun z := by rfl
      _ = 3 * (3⁻¹ * (E₂ z * E₄.toFun z - E₆.toFun z)) := by field_simp
      _ = 3 * D E₄.toFun z := by
          congr 1
          -- The RHS of h is (3⁻¹ * (E₂ * E₄.toFun - E₆.toFun)) z
          -- We need to show this equals 3⁻¹ * (E₂ z * E₄.toFun z - E₆.toFun z)
          -- This follows from how Pi multiplication works
          simp only [Pi.mul_apply, Pi.sub_apply] at h
          exact h.symm
  -- Substitute D(E₄) = 240 * ∑' n, n * σ₃(n) * q^n
  rw [hRam, D_E4_qexp]
  ring

end Ramanujan_qExpansion

/--
Prove modular linear differential equation satisfied by $F$.
-/
noncomputable def X₄₂ := 288⁻¹ * (E₄.toFun - E₂ * E₂)

noncomputable def Δ_fun := 1728⁻¹ * (E₄.toFun ^ 3 - E₆.toFun ^ 2)

noncomputable def F := (E₂ * E₄.toFun - E₆.toFun) ^ 2

theorem F_aux : D F = 5 * 6⁻¹ * E₂ ^ 3 * E₄.toFun ^ 2 - 5 * 2⁻¹ * E₂ ^ 2 * E₄.toFun * E₆.toFun
    + 5 * 6⁻¹ * E₂ * E₄.toFun ^ 3 + 5 * 3⁻¹ * E₂ * E₆.toFun ^ 2 - 5 * 6⁻¹ * E₄.toFun^2 * E₆.toFun
    := by
  rw [F, D_sq, D_sub, D_mul]
  · ring_nf
    rw [ramanujan_E₂, ramanujan_E₄, ramanujan_E₆]
    ext z
    simp
    ring_nf
  -- Holomorphicity of the terms
  · exact E₂_holo'
  · exact E₄.holo'
  · exact MDifferentiable.mul E₂_holo' E₄.holo'
  · exact E₆.holo'
  have h24 := MDifferentiable.mul E₂_holo' E₄.holo'
  exact MDifferentiable.sub h24 E₆.holo'


/-- Holomorphicity of F. -/
lemma F_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
  have hE₂E₄ := MDifferentiable.mul E₂_holo' E₄.holo'
  have hE₂E₄_sub_E₆ := MDifferentiable.sub hE₂E₄ E₆.holo'
  simp only [F, sq]; exact MDifferentiable.mul hE₂E₄_sub_E₆ hE₂E₄_sub_E₆

/-- Helper: serre_D 10 F expanded. -/
lemma serre_D_10_F : serre_D 10 F = D F - 5 * 6⁻¹ * E₂ * F := by
  ext z
  simp only [serre_D, Pi.sub_apply, Pi.mul_apply]
  -- 10 * 12⁻¹ = 5 * 6⁻¹
  norm_num

/-- Helper: Holomorphicity of D F. -/
lemma DF_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (D F) := D_differentiable F_holo'

/-- Helper: Holomorphicity of serre_D 10 F. -/
lemma serre_D_10_F_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (serre_D 10 F) :=
  serre_D_differentiable F_holo'

/-- Helper: MDifferentiable for E₂^2 -/
lemma E₂sq_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ ^ 2) := by
  have h : E₂ ^ 2 = E₂ * E₂ := sq E₂
  rw [h]; exact MDifferentiable.mul E₂_holo' E₂_holo'

/-- Helper: MDifferentiable for E₂^3 -/
lemma E₂cu_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ ^ 3) := by
  have h : E₂ ^ 3 = E₂ * E₂ ^ 2 := by ring
  rw [h]; exact MDifferentiable.mul E₂_holo' E₂sq_holo'

/-- Helper: MDifferentiable for E₄^2 -/
lemma E₄sq_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄.toFun ^ 2) := by
  have h : E₄.toFun ^ 2 = E₄.toFun * E₄.toFun := sq E₄.toFun
  rw [h]; exact MDifferentiable.mul E₄.holo' E₄.holo'

/-- Helper: MDifferentiable for E₄^3 -/
lemma E₄cu_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄.toFun ^ 3) := by
  have h : E₄.toFun ^ 3 = E₄.toFun * E₄.toFun ^ 2 := by ring
  rw [h]; exact MDifferentiable.mul E₄.holo' E₄sq_holo'

/-- Helper: MDifferentiable for E₆^2 -/
lemma E₆sq_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₆.toFun ^ 2) := by
  have h : E₆.toFun ^ 2 = E₆.toFun * E₆.toFun := sq E₆.toFun
  rw [h]; exact MDifferentiable.mul E₆.holo' E₆.holo'

/-- D(E₂³ * E₄²) expanded using product rule. -/
lemma D_E2cu_E4sq : D (E₂ ^ 3 * E₄.toFun ^ 2) =
    3 * E₂ ^ 2 * D E₂ * E₄.toFun ^ 2 + E₂ ^ 3 * 2 * E₄.toFun * D E₄.toFun := by
  rw [D_mul (E₂ ^ 3) (E₄.toFun ^ 2) E₂cu_holo' E₄sq_holo',
      D_cube E₂ E₂_holo', D_sq E₄.toFun E₄.holo']
  ring_nf

/-- D(E₂² * E₄ * E₆) expanded using product rule. -/
lemma D_E2sq_E4_E6 : D (E₂ ^ 2 * E₄.toFun * E₆.toFun) =
    2 * E₂ * D E₂ * E₄.toFun * E₆.toFun + E₂ ^ 2 * D E₄.toFun * E₆.toFun +
    E₂ ^ 2 * E₄.toFun * D E₆.toFun := by
  have hE₂sqE₄ := MDifferentiable.mul E₂sq_holo' E₄.holo'
  -- D(E₂² * E₄ * E₆) = D((E₂² * E₄) * E₆)
  have heq : E₂ ^ 2 * E₄.toFun * E₆.toFun = (E₂ ^ 2 * E₄.toFun) * E₆.toFun := by funext z; ring
  rw [heq, D_mul (E₂ ^ 2 * E₄.toFun) E₆.toFun hE₂sqE₄ E₆.holo',
      D_mul (E₂ ^ 2) E₄.toFun E₂sq_holo' E₄.holo', D_sq E₂ E₂_holo']
  ring_nf

/-- D(E₂ * E₄³) expanded using product rule. -/
lemma D_E2_E4cu : D (E₂ * E₄.toFun ^ 3) =
    D E₂ * E₄.toFun ^ 3 + E₂ * 3 * E₄.toFun ^ 2 * D E₄.toFun := by
  rw [D_mul E₂ (E₄.toFun ^ 3) E₂_holo' E₄cu_holo', D_cube E₄.toFun E₄.holo']
  ring_nf

/-- D(E₂ * E₆²) expanded using product rule. -/
lemma D_E2_E6sq : D (E₂ * E₆.toFun ^ 2) =
    D E₂ * E₆.toFun ^ 2 + E₂ * 2 * E₆.toFun * D E₆.toFun := by
  rw [D_mul E₂ (E₆.toFun ^ 2) E₂_holo' E₆sq_holo', D_sq E₆.toFun E₆.holo']
  ring_nf

/-- D(E₄² * E₆) expanded using product rule. -/
lemma D_E4sq_E6 : D (E₄.toFun ^ 2 * E₆.toFun) =
    2 * E₄.toFun * D E₄.toFun * E₆.toFun + E₄.toFun ^ 2 * D E₆.toFun := by
  rw [D_mul (E₄.toFun ^ 2) E₆.toFun E₄sq_holo' E₆.holo', D_sq E₄.toFun E₄.holo']
  ring_nf

/-- D(D F) expanded as polynomial in E₂, E₄, E₆. -/
lemma DDF_aux : D (D F) = D (5 * 6⁻¹ * E₂ ^ 3 * E₄.toFun ^ 2
    - 5 * 2⁻¹ * E₂ ^ 2 * E₄.toFun * E₆.toFun
    + 5 * 6⁻¹ * E₂ * E₄.toFun ^ 3
    + 5 * 3⁻¹ * E₂ * E₆.toFun ^ 2
    - 5 * 6⁻¹ * E₄.toFun^2 * E₆.toFun) := by rw [F_aux]

/-- Holomorphicity of E₂³ E₄². -/
lemma E2cu_E4sq_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ ^ 3 * E₄.toFun ^ 2) :=
  MDifferentiable.mul E₂cu_holo' E₄sq_holo'

/-- Holomorphicity of E₂² E₄ E₆. -/
lemma E2sq_E4_E6_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ ^ 2 * E₄.toFun * E₆.toFun) := by
  have h1 := MDifferentiable.mul E₂sq_holo' E₄.holo'
  exact MDifferentiable.mul h1 E₆.holo'

/-- Holomorphicity of E₂ E₄³. -/
lemma E2_E4cu_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₄.toFun ^ 3) :=
  MDifferentiable.mul E₂_holo' E₄cu_holo'

/-- Holomorphicity of E₂ E₆². -/
lemma E2_E6sq_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₂ * E₆.toFun ^ 2) :=
  MDifferentiable.mul E₂_holo' E₆sq_holo'

/-- Holomorphicity of E₄² E₆. -/
lemma E4sq_E6_holo' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (E₄.toFun ^ 2 * E₆.toFun) :=
  MDifferentiable.mul E₄sq_holo' E₆.holo'

-- MLDE_F involves complex algebraic manipulations where simp args are needed
-- for normalization even if the linter says they're unused
set_option linter.unusedSimpArgs false in
/-- Modular linear differential equation satisfied by `F`. -/
theorem MLDE_F : serre_D 12 (serre_D 10 F) = 5 * 6⁻¹ * E₄.toFun * F + 172800 * Δ_fun * X₄₂ := by
  -- Holomorphicity setup
  have hE₂ := E₂_holo'
  have hE₄ := E₄.holo'
  have hE₆ := E₆.holo'
  have hE₂E₄ := MDifferentiable.mul hE₂ hE₄
  have hE₂E₆ := MDifferentiable.mul hE₂ hE₆
  have hE₄E₆ := MDifferentiable.mul hE₄ hE₆
  have hE₄sq := MDifferentiable.mul hE₄ hE₄
  have hE₆sq := MDifferentiable.mul hE₆ hE₆
  have hE₂sq := MDifferentiable.mul hE₂ hE₂
  have hE₂cu := MDifferentiable.mul hE₂ hE₂sq
  have hE₄cu := MDifferentiable.mul hE₄ hE₄sq
  have hE₂E₄_sub_E₆ := MDifferentiable.sub hE₂E₄ hE₆
  have hF := F_holo'
  have hDF := DF_holo'
  -- serre_D 12 (serre_D 10 F) = D(serre_D 10 F) - E₂ * serre_D 10 F
  -- = D(D F - 5/6 * E₂ * F) - E₂ * (D F - 5/6 * E₂ * F)
  -- Work at the function level to apply D-rules
  rw [serre_D_10_F]
  unfold serre_D
  -- Now LHS = D(D F - 5/6 * E₂ * F) - E₂ * (D F - 5/6 * E₂ * F)
  -- Step 1: Expand D(D F - 5/6 * E₂ * F) using D_sub and D_smul
  have h56 : (5 : ℂ) * 6⁻¹ ≠ 0 := by norm_num
  have hE₂F := MDifferentiable.mul hE₂ hF
  -- c * f is MDifferentiable via smul: c • f where c • f = c * f for ℂ
  have hcE₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((5 * 6⁻¹ : ℂ) • E₂) := hE₂.const_smul (5 * 6⁻¹)
  have hcE₂_eq : (5 * 6⁻¹ : ℂ) • E₂ = 5 * 6⁻¹ * E₂ := by ext z; simp [smul_eq_mul]
  have h56E₂F : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * 6⁻¹ * E₂ * F) := by
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * 6⁻¹ * E₂) := by rwa [← hcE₂_eq]
    exact MDifferentiable.mul h1 hF
  have hD_outer : D (D F - 5 * 6⁻¹ * E₂ * F) = D (D F) - D (5 * 6⁻¹ * E₂ * F) := by
    have hcE₂F : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * 6⁻¹ * E₂ * F) := h56E₂F
    rw [D_sub (D F) (5 * 6⁻¹ * E₂ * F) hDF hcE₂F]
  -- Step 2: Expand D(5/6 * E₂ * F) using D_mul (twice)
  have hD_E₂F : D (E₂ * F) = E₂ * D F + D E₂ * F := D_mul E₂ F hE₂ hF
  have hD_cE₂F : D (5 * 6⁻¹ * E₂ * F) = 5 * 6⁻¹ * (E₂ * D F + D E₂ * F) := by
    have hcE₂' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (5 * 6⁻¹ * E₂) := by rwa [← hcE₂_eq]
    calc D (5 * 6⁻¹ * E₂ * F)
        = D ((5 * 6⁻¹ * E₂) * F) := by ring_nf
      _ = (5 * 6⁻¹ * E₂) * D F + D (5 * 6⁻¹ * E₂) * F := D_mul (5 * 6⁻¹ * E₂) F hcE₂' hF
      _ = (5 * 6⁻¹ * E₂) * D F + (5 * 6⁻¹ * D E₂) * F := by
          congr 1
          have : D (5 * 6⁻¹ * E₂) = 5 * 6⁻¹ * D E₂ := by
            rw [← hcE₂_eq, D_smul (5 * 6⁻¹) E₂ hE₂]
            ext z; simp [smul_eq_mul]
          rw [this]
      _ = 5 * 6⁻¹ * (E₂ * D F + D E₂ * F) := by ring_nf
  -- Step 3: Substitute ramanujan_E₂
  rw [ramanujan_E₂] at hD_cE₂F
  -- Now we have D(D F - 5/6 * E₂ * F) - E₂ * (D F - 5/6 * E₂ * F)
  -- = D(D F) - 5/6 * (E₂ * D F + 1/12 * (E₂² - E₄) * F) - E₂ * D F + 5/6 * E₂² * F
  -- Step 4: The proof reduces to algebraic identity
  -- D(D F) is a polynomial in E₂, E₄, E₆ after applying D-rules and Ramanujan identities
  -- This is a complex algebraic calculation that matches the RHS 5/6 * E₄ * F + 172800 * Δ * X₄₂
  -- The coefficients are:
  --   172800 = 600 * 288 and Δ = 1728⁻¹(E₄³ - E₆²), X₄₂ = 288⁻¹(E₄ - E₂²)
  --   So 172800 * 1728⁻¹ * 288⁻¹ = 600/1728 = 25/72
  -- Work at function level first, then go pointwise
  ext z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul]
  -- Evaluate function-level identities at z
  -- The Ramanujan identities give D E₂ = 12⁻¹ * (E₂² - E₄) etc.
  -- At point z: D E₂ z = (12⁻¹ : ℂ) * (E₂ z² - E₄ z)
  -- Note: The `ring` after `convert h using 2 <;>` handles associativity goals that `convert`
  have hR2 : D E₂ z = (12 : ℂ)⁻¹ * (E₂ z * E₂ z - E₄.toFun z) := by
    have h := congrFun ramanujan_E₂ z
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at h
    convert h using 2
  have hR4 : D E₄.toFun z = (3 : ℂ)⁻¹ * (E₂ z * E₄.toFun z - E₆.toFun z) := by
    have h := congrFun ramanujan_E₄ z
    simp only [Pi.mul_apply, Pi.sub_apply] at h
    convert h using 2
  have hR6 : D E₆.toFun z = (2 : ℂ)⁻¹ * (E₂ z * E₆.toFun z - E₄.toFun z * E₄.toFun z) := by
    have h := congrFun ramanujan_E₆ z
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at h
    convert h using 2
  -- Get hD_outer and hD_cE₂F at point z (these still have F unexpanded)
  have hO := congrFun hD_outer z
  have hC := congrFun hD_cE₂F z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul] at hO hC
  -- Expand D F using F_aux
  have hDF_z := congrFun F_aux z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul] at hDF_z
  -- Expand D(D F) z using the helper lemmas
  -- First get the D-rules for each monomial in F_aux at point z
  have hD1 := congrFun D_E2cu_E4sq z
  have hD2 := congrFun D_E2sq_E4_E6 z
  have hD3 := congrFun D_E2_E4cu z
  have hD4 := congrFun D_E2_E6sq z
  have hD5 := congrFun D_E4sq_E6 z
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at hD1 hD2 hD3 hD4 hD5
  -- D(D F) = D(F_aux) and F_aux is a linear combination of the monomials
  -- Set up smul-mul conversions
  have hsmul1 : (5 * 6⁻¹ : ℂ) • (E₂ ^ 3 * E₄.toFun ^ 2) = 5 * 6⁻¹ * E₂ ^ 3 * E₄.toFun ^ 2 := by
    ext w; simp [smul_eq_mul]; ring
  have hsmul2 : (5 * 2⁻¹ : ℂ) • (E₂ ^ 2 * E₄.toFun * E₆.toFun) =
      5 * 2⁻¹ * E₂ ^ 2 * E₄.toFun * E₆.toFun := by ext w; simp [smul_eq_mul]; ring
  have hsmul3 : (5 * 6⁻¹ : ℂ) • (E₂ * E₄.toFun ^ 3) = 5 * 6⁻¹ * E₂ * E₄.toFun ^ 3 := by
    ext w; simp [smul_eq_mul]; ring
  have hsmul4 : (5 * 3⁻¹ : ℂ) • (E₂ * E₆.toFun ^ 2) = 5 * 3⁻¹ * E₂ * E₆.toFun ^ 2 := by
    ext w; simp [smul_eq_mul]; ring
  have hsmul5 : (5 * 6⁻¹ : ℂ) • (E₄.toFun ^ 2 * E₆.toFun) = 5 * 6⁻¹ * E₄.toFun ^ 2 * E₆.toFun := by
    ext w; simp [smul_eq_mul]; ring
  have hs1 := E2cu_E4sq_holo'.const_smul (5 * 6⁻¹ : ℂ)
  have hs2 := E2sq_E4_E6_holo'.const_smul (5 * 2⁻¹ : ℂ)
  have hs3 := E2_E4cu_holo'.const_smul (5 * 6⁻¹ : ℂ)
  have hs4 := E2_E6sq_holo'.const_smul (5 * 3⁻¹ : ℂ)
  have hs5 := E4sq_E6_holo'.const_smul (5 * 6⁻¹ : ℂ)
  have hDDF_eq : D (D F) = (5 * 6⁻¹ : ℂ) • D (E₂ ^ 3 * E₄.toFun ^ 2)
      - (5 * 2⁻¹ : ℂ) • D (E₂ ^ 2 * E₄.toFun * E₆.toFun)
      + (5 * 6⁻¹ : ℂ) • D (E₂ * E₄.toFun ^ 3)
      + (5 * 3⁻¹ : ℂ) • D (E₂ * E₆.toFun ^ 2)
      - (5 * 6⁻¹ : ℂ) • D (E₄.toFun ^ 2 * E₆.toFun) := by
    rw [F_aux, ← hsmul1, ← hsmul2, ← hsmul3, ← hsmul4, ← hsmul5]
    simp only [D_sub _ _ (MDifferentiable.add (MDifferentiable.add
        (MDifferentiable.sub hs1 hs2) hs3) hs4) hs5,
      D_add _ _ (MDifferentiable.add (MDifferentiable.sub hs1 hs2) hs3) hs4,
      D_add _ _ (MDifferentiable.sub hs1 hs2) hs3,
      D_sub _ _ hs1 hs2,
      D_smul _ _ E2cu_E4sq_holo', D_smul _ _ E2sq_E4_E6_holo',
      D_smul _ _ E2_E4cu_holo', D_smul _ _ E2_E6sq_holo', D_smul _ _ E4sq_E6_holo']
  have hDDF_z := congrFun hDDF_eq z
  simp only [Pi.add_apply, Pi.sub_apply, smul_eq_mul] at hDDF_z
  -- Rewrite goal using hO and hC first, before any simplification
  rw [hO, hC]
  -- Expand smul applications: (c • f) z = c * f z
  simp only [Pi.smul_apply, smul_eq_mul] at hDDF_z ⊢
  -- Now substitute all D terms
  simp only [hDDF_z, hD1, hD2, hD3, hD4, hD5, hDF_z, hR2, hR4, hR6]
  -- Expand F, Δ_fun, X₄₂
  simp only [F, Δ_fun, X₄₂, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
  -- The goal now has terms like "5 z" which are just "5" (constant function applied to z)
  -- Use simp to normalize numeric constants
  simp only [show (5 : ℍ → ℂ) z = 5 from rfl, show (2 : ℍ → ℂ) z = 2 from rfl,
             show (3 : ℍ → ℂ) z = 3 from rfl, show (6 : ℍ → ℂ) z = 6 from rfl,
             show (12 : ℍ → ℂ) z = 12 from rfl, show (72 : ℍ → ℂ) z = 72 from rfl,
             show (288 : ℍ → ℂ) z = 288 from rfl, show (1728 : ℍ → ℂ) z = 1728 from rfl,
             show (172800 : ℍ → ℂ) z = 172800 from rfl,
             show (2⁻¹ : ℍ → ℂ) z = 2⁻¹ from rfl, show (3⁻¹ : ℍ → ℂ) z = 3⁻¹ from rfl,
             show (6⁻¹ : ℍ → ℂ) z = 6⁻¹ from rfl, show (12⁻¹ : ℍ → ℂ) z = 12⁻¹ from rfl,
             show (72⁻¹ : ℍ → ℂ) z = 72⁻¹ from rfl, show (288⁻¹ : ℍ → ℂ) z = 288⁻¹ from rfl,
             show (1728⁻¹ : ℍ → ℂ) z = 1728⁻¹ from rfl]
  -- Use "name the atoms" trick to help ring
  set e2 := E₂ z with he2
  set e4 := E₄.toFun z with he4
  set e6 := E₆.toFun z with he6
  -- Clear denominators and verify polynomial identity
  have h2    : (2    : ℂ) ≠ 0 := by norm_num
  have h3    : (3    : ℂ) ≠ 0 := by norm_num
  have h6    : (6    : ℂ) ≠ 0 := by norm_num
  have h12   : (12   : ℂ) ≠ 0 := by norm_num
  have h72   : (72   : ℂ) ≠ 0 := by norm_num
  have h288  : (288  : ℂ) ≠ 0 := by norm_num
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  field_simp [h2, h3, h6, h12, h72, h288, h1728]
  ring

example : D (E₄.toFun * E₄.toFun) = 2 * 3⁻¹ * E₄.toFun * (E₂ * E₄.toFun - E₆.toFun) :=
  by
  rw [D_mul E₄.toFun E₄.toFun]
  · simp only [ramanujan_E₄]
    ring_nf
  · exact E₄.holo'
  · exact E₄.holo'

end
