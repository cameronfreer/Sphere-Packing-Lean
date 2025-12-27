import SpherePacking.ModularForms.SerreDerivativeSlash
import SpherePacking.ModularForms.DimensionFormulas
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Asymptotic Behavior of Eisenstein Series

This file establishes the asymptotic behavior of Eisenstein series as z → i∞,
and constructs the ModularForm structures for Serre derivatives.

## Main definitions

* `PosReal` : Subtype of positive reals for limit statements
* `iMulPosReal` : Constructs an upper half plane point from a positive real
* `serre_D_E₄_ModularForm`, `serre_D_E₆_ModularForm`, `serre_D_E₂_ModularForm` :
  Package serre derivatives as modular forms

## Main results

* `D_tendsto_zero_of_tendsto_const` : Cauchy estimate: D f → 0 if f → const
* `E₂_tendsto_one_at_infinity`, `E₄_tendsto_one_at_infinity`, `E₆_tendsto_one_at_infinity` :
  Limits of Eisenstein series at infinity
* `serre_D_E₄_tendsto_at_infinity`, `serre_D_E₆_tendsto_at_infinity`,
  `serre_D_E₂_tendsto_at_infinity` : Limits of serre derivatives (for determining scalars)
-/

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open ModularForm EisensteinSeries TopologicalSpace Set MeasureTheory
open Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped ModularForm MatrixGroups Manifold Interval Real NNReal ENNReal Topology BigOperators

noncomputable section

/-! ## Cauchy estimates and limits at infinity -/

/-- Subtype of positive reals for limit statements -/
abbrev PosReal := {y : ℝ // 0 < y}

/-- The filter comap of Subtype.val on PosReal at atTop is NeBot. -/
lemma PosReal_comap_atTop_neBot :
    (Filter.comap Subtype.val (Filter.atTop : Filter ℝ)).NeBot (α := PosReal) := by
  rw [Filter.comap_neBot_iff]
  intro s hs
  rw [Filter.mem_atTop_sets] at hs
  obtain ⟨a, ha⟩ := hs
  exact ⟨⟨max a 1, lt_max_of_lt_right one_pos⟩, ha (max a 1) (le_max_left a 1)⟩

/-- Helper to construct an upper half plane point from a positive real. -/
def iMulPosReal (y : PosReal) : ℍ := ⟨I * y.val, by simp [y.2]⟩

/-- The imaginary part of iMulPosReal y equals y. -/
@[simp]
lemma im_iMulPosReal (y : PosReal) : (iMulPosReal y).im = y.val := by
  change (I * ↑↑y).im = y.val
  simp [Complex.mul_im]

/-- If f is holomorphic and bounded, with f(iy) → L as y → ∞, then D f(iy) → 0.

**Proof via Cauchy estimates:**
For z = iy with y large, consider the ball B(z, y/2) in ℂ.
- Ball is contained in upper half plane: all points have Im > y/2 > 0
- f ∘ ofComplex is holomorphic on the ball (from MDifferentiable)
- f is bounded by M for Im ≥ A (from IsBoundedAtImInfty)
- By Cauchy: |deriv(f ∘ ofComplex)(z)| ≤ M / (y/2) = 2M/y
- D f = (2πi)⁻¹ * deriv(...), so |D f(z)| ≤ M/(πy) → 0 -/
lemma D_tendsto_zero_of_tendsto_const {f : ℍ → ℂ} {L : ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : IsBoundedAtImInfty f)
    (_hlim : Filter.Tendsto (fun y : PosReal => f (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds L)) :
    Filter.Tendsto (fun y : PosReal => D f (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds 0) := by
  rw [isBoundedAtImInfty_iff] at hbdd
  obtain ⟨M, A, hMA⟩ := hbdd
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpi : 0 < π := Real.pi_pos
  rw [Filter.Eventually, Filter.mem_comap]
  use Set.Ici (max (2 * max A 0 + 1) (|M| / (π * ε) + 1))
  constructor
  · exact Filter.mem_atTop _
  · intro y hy
    simp only [Set.mem_preimage, Set.mem_Ici] at hy
    have hy_pos : 0 < y.val := y.2
    have hy_ge_A : y.val / 2 > max A 0 := by
      have h1 : y.val ≥ 2 * max A 0 + 1 := le_trans (le_max_left _ _) hy
      linarith
    have hy_ge_bound : y.val > |M| / (π * ε) := by
      have h1 : y.val ≥ |M| / (π * ε) + 1 := le_trans (le_max_right _ _) hy
      linarith
    let z : ℍ := iMulPosReal y
    have hz_im : z.im = y.val := im_iMulPosReal y
    have hclosed := closedBall_center_subset_upperHalfPlane z
    have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) (z.im / 2)) :=
      diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
    have hz_im_pos : 0 < z.im := z.im_pos
    have hR_pos : 0 < z.im / 2 := by linarith
    have hmax_nonneg : 0 ≤ max A 0 := le_max_right _ _
    have hA_le_max : A ≤ max A 0 := le_max_left _ _
    have hf_bdd_sphere : ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
      intro w hw
      have hw_mem_closed : w ∈ Metric.closedBall (z : ℂ) (z.im / 2) :=
        Metric.sphere_subset_closedBall hw
      have hw_im_pos : 0 < w.im := hclosed hw_mem_closed
      have hw_im_ge_A : A ≤ w.im := by
        have hdist : dist w z = z.im / 2 := Metric.mem_sphere.mp hw
        have habs : |w.im - z.im| ≤ z.im / 2 := by
          calc |w.im - z.im|
            _ = |(w - z).im| := by simp [Complex.sub_im]
            _ ≤ ‖w - z‖ := abs_im_le_norm _
            _ = dist w z := (dist_eq_norm _ _).symm
            _ = z.im / 2 := hdist
        have hlower : z.im / 2 ≤ w.im := by linarith [(abs_le.mp habs).1]
        have hA_lt : A < w.im := calc A ≤ max A 0 := hA_le_max
          _ < z.im / 2 := by rw [hz_im]; exact hy_ge_A
          _ ≤ w.im := hlower
        linarith
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw_im_pos]
      exact hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
    have hderiv_bound : ‖deriv (f ∘ ofComplex) z‖ ≤ M / (z.im / 2) :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR_pos hDiff hf_bdd_sphere
    have hD_eq : D f z = (2 * π * I)⁻¹ * deriv (f ∘ ofComplex) z := rfl
    have h2piI_norm : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hM_nonneg : 0 ≤ M := by
      have hA_le_z : A ≤ z.im := by rw [hz_im]; linarith [hA_le_max, hmax_nonneg, hy_ge_A]
      exact le_trans (norm_nonneg _) (hMA z hA_le_z)
    have hDf_bound : ‖D f z‖ ≤ M / (π * z.im) := by
      calc ‖D f z‖
        _ = ‖(2 * π * I)⁻¹ * deriv (f ∘ ofComplex) z‖ := by rw [hD_eq]
        _ = ‖(2 * π * I)⁻¹‖ * ‖deriv (f ∘ ofComplex) z‖ := norm_mul _ _
        _ = (2 * π)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by rw [h2piI_norm]
        _ ≤ (2 * π)⁻¹ * (M / (z.im / 2)) := by
            apply mul_le_mul_of_nonneg_left hderiv_bound
            exact inv_nonneg.mpr (by positivity)
        _ = (2 * π)⁻¹ * (2 * M / z.im) := by ring_nf
        _ = M / (π * z.im) := by ring
    simp only [dist_zero_right]
    by_cases hM_zero : M = 0
    · calc ‖D f z‖
        _ ≤ M / (π * z.im) := hDf_bound
        _ = 0 := by simp [hM_zero]
        _ < ε := hε
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nonneg (Ne.symm hM_zero)
      have habs_M_pos : 0 < |M| := abs_pos.mpr hM_zero
      calc ‖D f z‖
        _ ≤ M / (π * z.im) := hDf_bound
        _ = |M| / (π * z.im) := by rw [abs_of_pos hM_pos]
        _ < |M| / (π * (|M| / (π * ε))) := by
            apply div_lt_div_of_pos_left habs_M_pos
            · positivity
            · apply mul_lt_mul_of_pos_left _ Real.pi_pos
              rw [hz_im]; exact hy_ge_bound
        _ = ε := by field_simp

/-! ## Limits of Eisenstein series at infinity -/

/-- iMulPosReal sends the comap filter to atImInfty. -/
lemma tendsto_iMulPosReal_atImInfty :
    Filter.Tendsto iMulPosReal (Filter.comap Subtype.val Filter.atTop) atImInfty := by
  rw [atImInfty]
  simp only [Filter.tendsto_comap_iff, Function.comp_def]
  have h : ∀ y : PosReal, (iMulPosReal y).im = y.val := im_iMulPosReal
  simp_rw [h]
  exact Filter.tendsto_comap

/-- exp(-c * y) → 0 as y → +∞ (for c > 0). -/
lemma tendsto_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => Real.exp (-c * y)) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun y => -c * y) Filter.atTop Filter.atBot := by
    simpa using Filter.tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc)
  exact Real.tendsto_exp_atBot.comp this

/-- If f = O(exp(-c * Im z)) as z → i∞ for c > 0, then f → 0 at i∞. -/
lemma tendsto_zero_of_exp_decay {f : ℍ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : f =O[atImInfty] fun τ => Real.exp (-c * τ.im)) :
    Filter.Tendsto f atImInfty (nhds 0) := by
  apply Asymptotics.IsBigO.trans_tendsto hO
  rw [atImInfty]
  exact (tendsto_exp_neg_mul_atTop hc).comp Filter.tendsto_comap

/-- A modular form tends to its value at infinity as z → i∞. -/
lemma modular_form_tendsto_atImInfty {k : ℤ} (f : ModularForm (Gamma 1) k) :
    Filter.Tendsto f.toFun atImInfty (nhds ((qExpansion 1 f).coeff 0)) := by
  have hdecay := ModularFormClass.exp_decay_sub_atImInfty' f
  obtain ⟨c, hc, hO⟩ := hdecay
  have hval := qExpansion_coeff_zero f (by norm_num : (0 : ℝ) < 1) one_mem_strictPeriods_SL2Z
  rw [hval]
  have htend : Filter.Tendsto (fun z => f z - valueAtInfty f.toFun) atImInfty (nhds 0) :=
    tendsto_zero_of_exp_decay hc hO
  simpa using htend.add_const (valueAtInfty f.toFun)

/-- E₂ - 1 = O(exp(-2π·Im z)) at infinity. -/
lemma E₂_sub_one_isBigO_exp : (fun z : ℍ => E₂ z - 1) =O[atImInfty]
    fun z => Real.exp (-(2 * π) * z.im) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨192, ?_⟩
  rw [Filter.eventually_atImInfty]
  refine ⟨1, fun z hz => ?_⟩
  have hE₂_eq := E₂_eq z
  have hsub : E₂ z - 1 = -24 * ∑' (n : ℕ+), ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z)) := by
    rw [hE₂_eq]; ring
  rw [hsub]
  have h24 : ‖(-24 : ℂ)‖ = 24 := by simp [norm_neg]
  rw [norm_mul, h24, Real.norm_of_nonneg (Real.exp_pos _).le]
  set q : ℂ := cexp (2 * π * Complex.I * z) with hq_def
  have hq_norm : ‖q‖ < 1 := norm_exp_two_pi_I_lt_one z
  have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hone_sub_q_pos : 0 < 1 - ‖q‖ := by linarith
  have hq_bound : ‖q‖ ≤ Real.exp (-2 * π) := by
    have h1 : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
      rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
      simp [Complex.I_re, Complex.I_im, mul_comm]
    rw [hq_def, Complex.norm_exp, h1, Real.exp_le_exp]
    nlinarith [Real.pi_pos, z.im_pos]
  have hexp_lt_half : Real.exp (-2 * π) < 1 / 2 := by
    have hexp1_gt_2 : 2 < Real.exp 1 := by
      have h1 : (1 : ℝ) ≠ 0 := by norm_num
      have := Real.add_one_lt_exp h1
      linarith
    have hexp_neg1_lt : Real.exp (-1 : ℝ) < 1 / 2 := by
      rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
      simp only [one_div, inv_inv]
      exact hexp1_gt_2
    have h2pi_gt_1 : 1 < 2 * π := by
      have hpi_gt_3 : 3 < π := pi_gt_three
      linarith
    have hneg : -2 * π < -1 := by linarith
    calc Real.exp (-2 * π) < Real.exp (-1) := Real.exp_strictMono hneg
      _ < 1 / 2 := hexp_neg1_lt
  have hq_lt_half : ‖q‖ < 1 / 2 := lt_of_le_of_lt hq_bound hexp_lt_half
  have hone_sub_q_gt_half : 1 / 2 < 1 - ‖q‖ := by linarith
  have hexp_pow : ∀ n : ℕ, cexp (2 * π * Complex.I * n * z) = q ^ n := fun n => by
    rw [hq_def, ← Complex.exp_nat_mul]; congr 1; ring
  have hsum_eq : (fun n : ℕ+ => ↑n * cexp (2 * π * Complex.I * ↑n * ↑z) /
      (1 - cexp (2 * π * Complex.I * ↑n * ↑z))) =
      (fun n : ℕ+ => ↑n * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) := by
    ext n; simp only [hexp_pow]
  rw [hsum_eq]
  set r : ℝ := ‖q‖ with hr_def
  have hr_pos : 0 < r := hq_pos
  have hr_lt_one : r < 1 := hq_norm
  have hr_lt_half : r < 1 / 2 := hq_lt_half
  have hone_sub_r_pos : 0 < 1 - r := hone_sub_q_pos
  have hone_sub_r_gt_half : 1 / 2 < 1 - r := hone_sub_q_gt_half
  have hr_norm_lt_one : ‖r‖ < 1 := by simp [Real.norm_eq_abs, abs_of_nonneg hr_pos.le, hr_lt_one]
  have hterm_bound : ∀ n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      n * r ^ (n : ℕ) / (1 - r) := fun n => by
    have hqn_lt : ‖q ^ (n : ℕ)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hr_lt_one n.ne_zero
    have hdenom_ne : 1 - q ^ (n : ℕ) ≠ 0 := by
      intro h; simp only [sub_eq_zero] at h
      have : ‖q ^ (n : ℕ)‖ = 1 := by rw [← h]; exact norm_one
      linarith
    rw [norm_div, norm_mul, Complex.norm_natCast]
    have hdenom_lower : 1 - r ≤ ‖1 - q ^ (n : ℕ)‖ := by
      have h1 : 1 - ‖q ^ (n : ℕ)‖ ≤ ‖1 - q ^ (n : ℕ)‖ := by
        have := norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ))
        simp only [norm_one] at this; linarith
      have h2 : r ^ (n : ℕ) ≤ r := by
        have := pow_le_pow_of_le_one (norm_nonneg _) hr_lt_one.le n.one_le
        simp at this; exact this
      calc 1 - r ≤ 1 - r ^ (n : ℕ) := by linarith
        _ = 1 - ‖q ^ (n : ℕ)‖ := by rw [norm_pow, hr_def]
        _ ≤ _ := h1
    calc ↑n * ‖q ^ (n : ℕ)‖ / ‖1 - q ^ (n : ℕ)‖
        ≤ ↑n * ‖q ^ (n : ℕ)‖ / (1 - r) := by
          apply div_le_div_of_nonneg_left _ hone_sub_r_pos hdenom_lower
          exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      _ = ↑n * r ^ (n : ℕ) / (1 - r) := by rw [norm_pow, hr_def]
  have hsumm_nat : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 hr_norm_lt_one
    simp only [pow_one] at this; exact this
  have hsumm_pnat : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ)) := by
    have h0 : (fun n : ℕ => (n : ℝ) * r ^ n) 0 = 0 := by simp
    exact (nat_pos_tsum2 _ h0).mpr hsumm_nat
  have hsumm_majorant : Summable (fun n : ℕ+ => (n : ℝ) * r ^ (n : ℕ) / (1 - r)) := by
    simpa [div_eq_mul_inv] using hsumm_pnat.mul_right (1 - r)⁻¹
  have hsumm_norms : Summable (fun n : ℕ+ => ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsumm_majorant
    convert hterm_bound n using 2
  have htsum_le : ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
      ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) := by
    calc ‖∑' n : ℕ+, (n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
        ≤ ∑' n : ℕ+, ‖(n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ :=
          norm_tsum_le_tsum_norm hsumm_norms
      _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) :=
          Summable.tsum_le_tsum (fun n => by convert hterm_bound n using 2)
            hsumm_norms hsumm_majorant
  have hsum_nat_val : (∑' n : ℕ, (n : ℝ) * r ^ n) = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hr_norm_lt_one
  have hsum_pnat : (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ)) = r / (1 - r) ^ 2 := by
    have heq := tsum_pnat_eq_tsum_succ4 (fun n => (n : ℝ) * r ^ n) hsumm_nat
    simp only [Nat.cast_zero, zero_mul, zero_add] at heq
    rw [← hsum_nat_val]; exact heq
  have hsum_majorant_eq : (∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r)) = r / (1 - r) ^ 3 := by
    rw [tsum_div_const, hsum_pnat]; field_simp
  have hsum_le_8r : r / (1 - r) ^ 3 ≤ 8 * r := by
    have h1 : (1 / 2 : ℝ) ^ 3 ≤ (1 - r) ^ 3 := by
      apply pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ) / 2)
      linarith
    have h2 : (1 / 2 : ℝ) ^ 3 = 1 / 8 := by norm_num
    rw [h2] at h1
    calc r / (1 - r) ^ 3 ≤ r / (1 / 8) := by
          apply div_le_div_of_nonneg_left hr_pos.le (by positivity : 0 < (1 : ℝ) / 8) h1
      _ = 8 * r := by ring
  have hq_eq_exp : r = Real.exp (-2 * π * z.im) := by
    rw [hr_def, hq_def]
    have hre : (2 * ↑π * Complex.I * (z : ℂ)).re = -2 * π * z.im := by
      rw [show (2 : ℂ) * ↑π * Complex.I * z = Complex.I * (2 * π * z) by ring]
      simp [Complex.I_re, Complex.I_im, mul_comm]
    rw [Complex.norm_exp, hre]
  calc 24 * ‖∑' n : ℕ+, ↑n * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ 24 * (r / (1 - r) ^ 3) := by
        gcongr; calc _ ≤ ∑' n : ℕ+, (n : ℝ) * r ^ (n : ℕ) / (1 - r) := htsum_le
          _ = r / (1 - r) ^ 3 := hsum_majorant_eq
    _ ≤ 24 * (8 * r) := by gcongr
    _ = 192 * r := by ring
    _ = 192 * Real.exp (-2 * π * z.im) := by rw [hq_eq_exp]
    _ = 192 * Real.exp (-(2 * π) * z.im) := by ring_nf

/-- E₂ → 1 at i∞. -/
lemma E₂_tendsto_one_atImInfty : Filter.Tendsto E₂ atImInfty (nhds 1) := by
  suffices h : Filter.Tendsto (fun z : ℍ => E₂ z - 1) atImInfty (nhds 0) by
    simpa using h.add_const 1
  exact tendsto_zero_of_exp_decay (by positivity : 0 < 2 * π) E₂_sub_one_isBigO_exp

/-- E₂(iy) → 1 as y → +∞. -/
lemma E₂_tendsto_one_at_infinity :
    Filter.Tendsto (fun y : PosReal => E₂ (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds 1) :=
  E₂_tendsto_one_atImInfty.comp tendsto_iMulPosReal_atImInfty

/-- E₄(iy) → 1 as y → +∞. -/
lemma E₄_tendsto_one_at_infinity :
    Filter.Tendsto (fun y : PosReal => E₄.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds 1) := by
  have h := modular_form_tendsto_atImInfty E₄
  rw [E4_q_exp_zero] at h
  exact h.comp tendsto_iMulPosReal_atImInfty

/-- E₆(iy) → 1 as y → +∞. -/
lemma E₆_tendsto_one_at_infinity :
    Filter.Tendsto (fun y : PosReal => E₆.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds 1) := by
  have h := modular_form_tendsto_atImInfty E₆
  rw [E6_q_exp_zero] at h
  exact h.comp tendsto_iMulPosReal_atImInfty

/-! ## Boundedness lemmas -/

/-- E₆ is bounded at infinity (as a modular form). -/
lemma E₆_isBoundedAtImInfty : IsBoundedAtImInfty E₆.toFun :=
  ModularFormClass.bdd_at_infty E₆

/-- serre_D 1 E₂ is bounded at infinity. -/
lemma serre_D_E₂_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 1 E₂) := by
  have hserre : serre_D 1 E₂ = D E₂ - (fun z => 1 * 12⁻¹ * E₂ z * E₂ z) := rfl
  rw [hserre]
  have hDE₂ : IsBoundedAtImInfty (D E₂) :=
    D_isBoundedAtImInfty_of_bounded E₂_holo' E₂_isBoundedAtImInfty
  have hE₂sq : IsBoundedAtImInfty (fun z => E₂ z * E₂ z) :=
    E₂_isBoundedAtImInfty.mul E₂_isBoundedAtImInfty
  have h12E₂sq : IsBoundedAtImInfty (fun z => 1 * 12⁻¹ * E₂ z * E₂ z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => (1 : ℂ) * 12⁻¹) :=
      Filter.const_boundedAtFilter _ _
    have := hconst.mul hE₂sq
    convert this using 1
    ext z; simp only [Pi.mul_apply]; ring
  exact hDE₂.sub h12E₂sq

/-! ## Construction of ModularForm from serre_D -/

/-- serre_D 4 E₄ is a weight-6 modular form. -/
def serre_D_E₄_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 6 where
  toSlashInvariantForm := {
    toFun := serre_D 4 E₄.toFun
    slash_action_eq' := fun γ hγ => by
      rw [Subgroup.mem_map] at hγ
      obtain ⟨γ', _, hγ'_eq⟩ := hγ
      have hE₄_slash : E₄.toFun ∣[(4 : ℤ)] γ' = E₄.toFun := by
        have := E₄.slash_action_eq' γ ⟨γ', mem_Gamma_one γ', hγ'_eq⟩
        rw [← hγ'_eq] at this
        exact this
      have h := serre_D_slash_invariant 4 E₄.toFun E₄.holo' γ' hE₄_slash
      change serre_D 4 E₄.toFun ∣[(6 : ℤ)] γ = serre_D 4 E₄.toFun
      rw [← hγ'_eq]
      exact h
  }
  holo' := serre_D_differentiable E₄.holo'
  bdd_at_cusps' := fun hc => by
    apply bounded_at_cusps_of_bounded_at_infty hc
    intro A hA
    rw [MonoidHom.mem_range] at hA
    obtain ⟨A', hA'_eq⟩ := hA
    have h := serre_D_slash_invariant 4 E₄.toFun E₄.holo' A'
      (E₄.slash_action_eq' _ ⟨A', mem_Gamma_one A', rfl⟩)
    change IsBoundedAtImInfty (serre_D 4 E₄.toFun ∣[(6 : ℤ)] A)
    rw [← hA'_eq]
    convert serre_D_E₄_isBoundedAtImInfty using 1

/-- serre_D 6 E₆ is bounded at infinity. -/
lemma serre_D_E₆_isBoundedAtImInfty : IsBoundedAtImInfty (serre_D 6 E₆.toFun) := by
  unfold serre_D
  have h1 : IsBoundedAtImInfty (D E₆.toFun) :=
    D_isBoundedAtImInfty_of_bounded E₆.holo' E₆_isBoundedAtImInfty
  have h2 : IsBoundedAtImInfty (fun z => (6 : ℂ) * 12⁻¹ * E₂ z * E₆.toFun z) := by
    have hconst : IsBoundedAtImInfty (fun _ : ℍ => (6 : ℂ) * 12⁻¹) :=
      Filter.const_boundedAtFilter _ _
    have hE₂E₆ : IsBoundedAtImInfty (E₂ * E₆.toFun) :=
      E₂_isBoundedAtImInfty.mul E₆_isBoundedAtImInfty
    convert hconst.mul hE₂E₆ using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  exact h1.sub h2

/-- serre_D 6 E₆ is a weight-8 modular form. -/
def serre_D_E₆_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 8 where
  toSlashInvariantForm := {
    toFun := serre_D 6 E₆.toFun
    slash_action_eq' := fun γ hγ => by
      rw [Subgroup.mem_map] at hγ
      obtain ⟨γ', _, hγ'_eq⟩ := hγ
      have hE₆_slash : E₆.toFun ∣[(6 : ℤ)] γ' = E₆.toFun := by
        have := E₆.slash_action_eq' γ ⟨γ', mem_Gamma_one γ', hγ'_eq⟩
        rw [← hγ'_eq] at this
        exact this
      have h := serre_D_slash_invariant 6 E₆.toFun E₆.holo' γ' hE₆_slash
      change serre_D 6 E₆.toFun ∣[(8 : ℤ)] γ = serre_D 6 E₆.toFun
      rw [← hγ'_eq]
      exact h
  }
  holo' := serre_D_differentiable E₆.holo'
  bdd_at_cusps' := fun hc => by
    apply bounded_at_cusps_of_bounded_at_infty hc
    intro A hA
    rw [MonoidHom.mem_range] at hA
    obtain ⟨A', hA'_eq⟩ := hA
    have h := serre_D_slash_invariant 6 E₆.toFun E₆.holo' A'
      (E₆.slash_action_eq' _ ⟨A', mem_Gamma_one A', rfl⟩)
    change IsBoundedAtImInfty (serre_D 6 E₆.toFun ∣[(8 : ℤ)] A)
    rw [← hA'_eq]
    convert serre_D_E₆_isBoundedAtImInfty using 1

/-! ## Limit of serre_D at infinity (for determining scalar) -/

/-- serre_D 4 E₄(iy) → -1/3 as y → +∞. -/
lemma serre_D_E₄_tendsto_at_infinity :
    Filter.Tendsto (fun y : PosReal => serre_D 4 E₄.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds (-(1/3 : ℂ))) := by
  have hserre : ∀ y : PosReal, serre_D 4 E₄.toFun (iMulPosReal y) =
      D E₄.toFun (iMulPosReal y) -
        (4 : ℂ) * 12⁻¹ * E₂ (iMulPosReal y) * E₄.toFun (iMulPosReal y) := by
    intro y
    simp only [serre_D, Pi.sub_apply]
  simp_rw [hserre]
  have hD : Filter.Tendsto (fun y : PosReal => D E₄.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds 0) :=
    D_tendsto_zero_of_tendsto_const E₄.holo' E₄_isBoundedAtImInfty E₄_tendsto_one_at_infinity
  have hE₂ := E₂_tendsto_one_at_infinity
  have hE₄ := E₄_tendsto_one_at_infinity
  have hlim : (0 : ℂ) - (4 : ℂ) * 12⁻¹ * 1 * 1 = -(1/3 : ℂ) := by norm_num
  rw [← hlim]
  refine Filter.Tendsto.sub hD ?_
  have hprod : Filter.Tendsto (fun y : PosReal => E₂ (iMulPosReal y) * E₄.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds (1 * 1)) :=
    hE₂.mul hE₄
  have hconst : Filter.Tendsto (fun _ : PosReal => (4 : ℂ) * 12⁻¹)
      (Filter.comap Subtype.val Filter.atTop) (nhds ((4 : ℂ) * 12⁻¹)) :=
    tendsto_const_nhds
  convert hconst.mul hprod using 1 <;> ring

/-- serre_D 6 E₆(iy) → -1/2 as y → +∞. -/
lemma serre_D_E₆_tendsto_at_infinity :
    Filter.Tendsto (fun y : PosReal => serre_D 6 E₆.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds (-(1/2 : ℂ))) := by
  have hserre : ∀ y : PosReal, serre_D 6 E₆.toFun (iMulPosReal y) =
      D E₆.toFun (iMulPosReal y) -
        (6 : ℂ) * 12⁻¹ * E₂ (iMulPosReal y) * E₆.toFun (iMulPosReal y) := by
    intro y
    simp only [serre_D, Pi.sub_apply]
  simp_rw [hserre]
  have hD : Filter.Tendsto (fun y : PosReal => D E₆.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds 0) := by
    apply D_tendsto_zero_of_tendsto_const E₆.holo'
    · exact E₆_isBoundedAtImInfty
    · exact E₆_tendsto_one_at_infinity
  have hE₂ := E₂_tendsto_one_at_infinity
  have hE₆ := E₆_tendsto_one_at_infinity
  have hlim : (0 : ℂ) - (6 : ℂ) * 12⁻¹ * 1 * 1 = -(1/2 : ℂ) := by norm_num
  rw [← hlim]
  refine Filter.Tendsto.sub hD ?_
  have hprod : Filter.Tendsto (fun y : PosReal => E₂ (iMulPosReal y) * E₆.toFun (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds (1 * 1)) :=
    hE₂.mul hE₆
  have hconst : Filter.Tendsto (fun _ : PosReal => (6 : ℂ) * 12⁻¹)
      (Filter.comap Subtype.val Filter.atTop) (nhds ((6 : ℂ) * 12⁻¹)) :=
    tendsto_const_nhds
  convert hconst.mul hprod using 1 <;> ring

/-- serre_D 1 E₂ is a weight-4 modular form.
Note: E₂ itself is NOT a modular form, but serre_D 1 E₂ IS. -/
def serre_D_E₂_ModularForm : ModularForm (CongruenceSubgroup.Gamma 1) 4 where
  toSlashInvariantForm := {
    toFun := serre_D 1 E₂
    slash_action_eq' := fun γ hγ => by
      rw [Subgroup.mem_map] at hγ
      obtain ⟨γ', _, hγ'_eq⟩ := hγ
      have h := serre_D_E₂_slash_invariant γ'
      change serre_D 1 E₂ ∣[(4 : ℤ)] γ = serre_D 1 E₂
      rw [← hγ'_eq]
      exact h
  }
  holo' := serre_D_differentiable E₂_holo'
  bdd_at_cusps' := fun hc => by
    apply bounded_at_cusps_of_bounded_at_infty hc
    intro A hA
    rw [MonoidHom.mem_range] at hA
    obtain ⟨A', hA'_eq⟩ := hA
    have h := serre_D_E₂_slash_invariant A'
    change IsBoundedAtImInfty (serre_D 1 E₂ ∣[(4 : ℤ)] A)
    rw [← hA'_eq]
    convert serre_D_E₂_isBoundedAtImInfty using 1

/-- serre_D 1 E₂(iy) → -1/12 as y → +∞. -/
lemma serre_D_E₂_tendsto_at_infinity :
    Filter.Tendsto (fun y : PosReal => serre_D 1 E₂ (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds (-(1/12 : ℂ))) := by
  have hserre : ∀ y : PosReal, serre_D 1 E₂ (iMulPosReal y) =
      D E₂ (iMulPosReal y) - 1 * 12⁻¹ * E₂ (iMulPosReal y) * E₂ (iMulPosReal y) := by
    intro y
    simp only [serre_D, Pi.sub_apply, Pi.mul_apply]
  simp_rw [hserre]
  have hD : Filter.Tendsto (fun y : PosReal => D E₂ (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds 0) :=
    D_tendsto_zero_of_tendsto_const E₂_holo' E₂_isBoundedAtImInfty E₂_tendsto_one_at_infinity
  have hE₂ := E₂_tendsto_one_at_infinity
  have hlim : (0 : ℂ) - (1 : ℂ) * 12⁻¹ * 1 * 1 = -(1/12 : ℂ) := by norm_num
  rw [← hlim]
  refine Filter.Tendsto.sub hD ?_
  have hprod : Filter.Tendsto (fun y : PosReal => E₂ (iMulPosReal y) * E₂ (iMulPosReal y))
      (Filter.comap Subtype.val Filter.atTop) (nhds (1 * 1)) :=
    hE₂.mul hE₂
  have hconst : Filter.Tendsto (fun _ : PosReal => (1 : ℂ) * 12⁻¹)
      (Filter.comap Subtype.val Filter.atTop) (nhds ((1 : ℂ) * 12⁻¹)) :=
    tendsto_const_nhds
  convert hconst.mul hprod using 1 <;> ring
