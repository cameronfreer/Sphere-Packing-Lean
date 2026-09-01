/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module


public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Polynomial Bounds on Cauchy-Product Coefficients

Exact coefficient functions for the `q`-expansions entering `φ₀ = (E₂E₄ - E₆)² / Δ`, and
polynomial growth bounds for their Cauchy products.

The single-series coefficients (`a_E₂E₄E₆` for `E₂E₄ - E₆`, `b_E₄` for `E₄`) have polynomial
growth by the divisor bound `σ k n ≤ n ^ (k + 1)`. The square `(E₂E₄ - E₆)²` and the products
with `E₄` have coefficients given by Cauchy products, and `cauchyCoeff_poly` shows a Cauchy
product of two polynomially bounded sequences is again polynomially bounded (with the degree
increasing by one). `evenExt` re-indexes a `q`-series (`q = e^{2πiz}`) as an `r`-series
(`r = e^{πiz}`, so `q = r²`) supported on even indices, and `toIntCoeff` extends by zero to
`ℤ`-indexed coefficients as consumed by `DivDiscBoundOfPolyFourierCoeff`.

## Main results

* `cauchyCoeff_poly`: `a = O(n^k)` and `b = O(n^ℓ)` give `cauchyCoeff a b = O(n^(k+ℓ+1))`,
* `c_E₂E₄E₆_poly`, `c_E₄_E₂E₄E₆_poly`, `c_E₄_sq_poly`: the concrete `O(n^11)`, `O(n^10)`,
  `O(n^9)` bounds for the three coefficient families.
-/

@[expose] public section

open Real Complex
open scoped ArithmeticFunction.sigma

noncomputable section

namespace MagicFunction.a.FourierExpansions

/-- The divisor-power bound `σ k n ≤ n ^ (k + 1)`: each of the at most `n` divisors is at
most `n`. -/
lemma sigma_bound (k n : ℕ) : σ k n ≤ n ^ (k + 1) := by
  rw [ArithmeticFunction.sigma_apply]
  calc ∑ d ∈ n.divisors, d ^ k ≤ ∑ _d ∈ n.divisors, n ^ k :=
        Finset.sum_le_sum fun i hi ↦ pow_le_pow_left₀ (Nat.zero_le _) (Nat.divisor_le hi) k
    _ ≤ n * n ^ k := by
        simpa using Nat.mul_le_mul_right (n ^ k) (Nat.card_divisors_le_self n)
    _ = n ^ (k + 1) := by rw [pow_succ, mul_comm]

/-! ## Coefficient Functions

The coefficient functions are defined to give exact Fourier expansions.
The key is converting from q-expansions (exp(2πinz)) to r-expansions (exp(πinz)).

Since q = exp(2πiz) = r² where r = exp(πiz), a q-series ∑ aₙ qⁿ becomes
an r-series with only even indices: ∑ a_{m/2} rᵐ for even m.

We use `Function.extend (fun n ↦ 2 * n)` for this even-indexing. -/

/-- Q-expansion coefficient for E₂E₄ - E₆: coefficient at qⁿ is 720·n·σ₃(n) for n ≥ 1. -/
def a_E₂E₄E₆ : ℕ → ℂ := fun n ↦ if n = 0 then 0 else 720 * n * (σ 3 n)

/-- Q-expansion coefficient for E₄: coefficient at qⁿ is 240·σ₃(n) for n ≥ 1, and 1 for n = 0. -/
def b_E₄ : ℕ → ℂ := fun n ↦ if n = 0 then 1 else 240 * (σ 3 n)

/-- Cauchy product (convolution) of two sequences at index n. -/
def cauchyCoeff (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2

/-- Even extension: extend a sequence to all naturals, zero on odd indices.
    evenExt a m = a(m/2) if m is even, 0 if m is odd. -/
def evenExt (a : ℕ → ℂ) : ℕ → ℂ := Function.extend (fun n ↦ 2 * n) a 0

/-- Convert ℕ coefficient to ℤ coefficient (zero for negative indices). -/
def toIntCoeff (a : ℕ → ℂ) : ℤ → ℂ := fun k ↦ if k < 0 then 0 else a k.toNat

/-- Coefficient function for (E₂E₄ - E₆)²: uses Cauchy product of a_E₂E₄E₆ with itself,
    then even extension for q→r conversion. -/
def c_E₂E₄E₆ : ℤ → ℂ := toIntCoeff (evenExt (cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆))

/-- Coefficient function for E₄ * (E₂E₄ - E₆): uses Cauchy product of b_E₄ and a_E₂E₄E₆,
    then even extension. -/
def c_E₄_E₂E₄E₆ : ℤ → ℂ := toIntCoeff (evenExt (cauchyCoeff b_E₄ a_E₂E₄E₆))

/-- Coefficient function for E₄²: uses Cauchy product of b_E₄ with itself,
    then even extension. -/
def c_E₄_sq : ℤ → ℂ := toIntCoeff (evenExt (cauchyCoeff b_E₄ b_E₄))

/-! ## Polynomial Growth Infrastructure -/

/-- A big-O bound `a =O[atTop] (n ^ k)` upgrades to a single global constant: there is `M > 0`
with `‖a i‖ ≤ M * n ^ k` for every `n ≥ 1` and every `i ≤ n`. The big-O bound covers the large
indices, while the finitely many initial terms are absorbed into `M`. -/
lemma exists_global_poly_bound {a : ℕ → ℂ} {k : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    ∃ M > 0, ∀ n i : ℕ, 1 ≤ n → i ≤ n → ‖a i‖ ≤ M * (n : ℝ) ^ k := by
  obtain ⟨C, hC0, hC⟩ := Asymptotics.bound_of_isBigO_nat_atTop ha
  refine ⟨max C (‖a 0‖ + 1), lt_max_of_lt_left hC0, fun n i hn hi ↦ ?_⟩
  have hM0 : (0 : ℝ) ≤ max C (‖a 0‖ + 1) := le_max_of_le_left hC0.le
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hn)
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · calc ‖a 0‖ ≤ max C (‖a 0‖ + 1) * 1 := by
          rw [mul_one]; exact le_max_of_le_right (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left hn1 hM0
  · have hi' : ((i : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hi0.ne'
    have h := hC (pow_ne_zero k hi')
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h.trans (mul_le_mul (le_max_left _ _)
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hi) k) (by positivity) hM0)

/-- Cauchy product of two polynomial-growth sequences has polynomial growth.
    If a = O(n^k) and b = O(n^ℓ), then cauchyCoeff a b = O(n^(k + ℓ + 1)).
    This follows from |∑_{i+j=n} a(i)·b(j)| ≤ (n+1) · sup|a(i)| · sup|b(j)|. -/
lemma cauchyCoeff_poly {a b : ℕ → ℂ} {k ℓ : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)))
    (hb : b =O[Filter.atTop] (fun n ↦ (n ^ ℓ : ℝ))) :
    cauchyCoeff a b =O[Filter.atTop] (fun n ↦ (n ^ (k + ℓ + 1) : ℝ)) := by
  -- Each of the `n + 1` terms of the Cauchy product is bounded by `A * n ^ k * (B * n ^ ℓ)`,
  -- and the factor `n + 1 ≤ 2 * n` is absorbed by the extra power of `n`.
  obtain ⟨A, hA, ha_bound⟩ := exists_global_poly_bound ha
  obtain ⟨B, hB, hb_bound⟩ := exists_global_poly_bound hb
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 * A * B, Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  calc ‖cauchyCoeff a b n‖
      = ‖∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2‖ := rfl
    _ ≤ ∑ kl ∈ Finset.antidiagonal n, ‖a kl.1‖ * ‖b kl.2‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ norm_mul_le _ _)
    _ ≤ ∑ _kl ∈ Finset.antidiagonal n, A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ) := by
        refine Finset.sum_le_sum fun ⟨i, j⟩ hij ↦ ?_
        simp only [Finset.mem_antidiagonal] at hij
        exact mul_le_mul (ha_bound n i hn (by omega)) (hb_bound n j hn (by omega))
          (norm_nonneg _) (by positivity)
    _ = ((n : ℝ) + 1) * (A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]; push_cast; ring
    _ ≤ 2 * (n : ℝ) * (A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ)) := by
        have : (0 : ℝ) ≤ A * (n : ℝ) ^ k * (B * (n : ℝ) ^ ℓ) := by positivity
        nlinarith
    _ = 2 * A * B * (n : ℝ) ^ (k + ℓ + 1) := by ring
    _ = 2 * A * B * ‖(n : ℝ) ^ (k + ℓ + 1)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- a_E₂E₄E₆ has polynomial growth O(n^5). -/
lemma a_E₂E₄E₆_poly : a_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 5 : ℝ)) := by
  -- a_E₂E₄E₆(n) = 720 * n * σ₃(n) for n ≥ 1. Since σ₃(n) ≤ n^4, the product is O(n^5).
  rw [Asymptotics.isBigO_iff]
  use 720
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [a_E₂E₄E₆, Nat.ne_of_gt hn, ↓reduceIte]
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n ^ 5)]
  have hσ : (σ 3 n : ℝ) ≤ n ^ 4 := by exact_mod_cast sigma_bound 3 n
  have h720 : ‖(720 : ℂ)‖ = 720 := by norm_num
  calc ‖(720 : ℂ)‖ * n * ((σ 3) n : ℝ)
      ≤ 720 * n * n ^ 4 := by rw [h720]; nlinarith
    _ = 720 * n ^ 5 := by ring

/-- b_E₄ has polynomial growth O(n^4). -/
lemma b_E₄_poly : b_E₄ =O[Filter.atTop] (fun n ↦ (n ^ 4 : ℝ)) := by
  -- b_E₄(n) = 240 * σ₃(n) for n ≥ 1. Since σ₃(n) ≤ n^4, the product is O(n^4).
  rw [Asymptotics.isBigO_iff]
  use 240
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  simp only [b_E₄, Nat.ne_of_gt hn, ↓reduceIte]
  rw [Complex.norm_mul, Complex.norm_natCast]
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n ^ 4)]
  have hσ : (σ 3 n : ℝ) ≤ n ^ 4 := by exact_mod_cast sigma_bound 3 n
  have h240 : ‖(240 : ℂ)‖ = 240 := by norm_num
  calc ‖(240 : ℂ)‖ * ((σ 3) n : ℝ) ≤ 240 * n ^ 4 := by rw [h240]; nlinarith

/-! ## Even Extension Lemmas

Properties of the even extension map used for q→r series conversion. -/

/-- evenExt at even index equals original coefficient. -/
lemma evenExt_even (a : ℕ → ℂ) (n : ℕ) : evenExt a (2 * n) = a n :=
  Function.Injective.extend_apply (fun m₁ m₂ h ↦ by omega) a (0 : ℕ → ℂ) n

/-- evenExt at odd index is zero. -/
lemma evenExt_odd (a : ℕ → ℂ) (n : ℕ) : evenExt a (2 * n + 1) = 0 :=
  Function.extend_apply' a (0 : ℕ → ℂ) _ (fun ⟨m, hm⟩ ↦ by omega)

/-- Cauchy product at 0 is zero if right factor vanishes at 0. -/
lemma cauchyCoeff_zero_of_right_zero {a b : ℕ → ℂ} (hb0 : b 0 = 0) :
    cauchyCoeff a b 0 = 0 := by
  simp only [cauchyCoeff, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hb0, mul_zero]

/-- Cauchy product at 1 is zero if both factors vanish at 0. -/
lemma cauchyCoeff_one_zero_of_both_zero {a b : ℕ → ℂ} (ha0 : a 0 = 0) (hb0 : b 0 = 0) :
    cauchyCoeff a b 1 = 0 := by
  simp only [cauchyCoeff]
  apply Finset.sum_eq_zero
  intro ⟨i, j⟩ hij
  simp only [Finset.mem_antidiagonal] at hij
  rcases Nat.eq_zero_or_pos i with hi | hi
  · simp only [hi, ha0, zero_mul]
  · simp only [Nat.lt_one_iff.mp (by omega : j < 1), hb0, mul_zero]

/-- `evenExt` of a Cauchy product vanishes for `m < 2` when the right factor vanishes at 0. -/
lemma evenExt_cauchyCoeff_zero_of_lt_two {a b : ℕ → ℂ} (hb0 : b 0 = 0) (m : ℕ) (hm : m < 2) :
    evenExt (cauchyCoeff a b) m = 0 := by
  have hc0 : cauchyCoeff a b 0 = 0 := cauchyCoeff_zero_of_right_zero hb0
  interval_cases m
  · rw [show (0 : ℕ) = 2 * 0 by omega, evenExt_even, hc0]
  · exact evenExt_odd _ 0

/-- evenExt of Cauchy self-product vanishes for m < 4 when factor vanishes at 0. -/
lemma evenExt_cauchyCoeff_zero_of_lt_four {a : ℕ → ℂ} (ha0 : a 0 = 0) (m : ℕ) (hm : m < 4) :
    evenExt (cauchyCoeff a a) m = 0 := by
  have hc0 : cauchyCoeff a a 0 = 0 := cauchyCoeff_zero_of_right_zero ha0
  have hc1 : cauchyCoeff a a 1 = 0 := cauchyCoeff_one_zero_of_both_zero ha0 ha0
  interval_cases m
  · rw [show (0 : ℕ) = 2 * 0 by omega, evenExt_even, hc0]
  · exact evenExt_odd _ 0
  · rw [show (2 : ℕ) = 2 * 1 by omega, evenExt_even, hc1]
  · exact evenExt_odd _ 1

/-- Even extension preserves polynomial growth. If a = O(n^k), then evenExt a = O(n^k). -/
lemma evenExt_poly {a : ℕ → ℂ} {k : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    evenExt a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)) := by
  rw [Asymptotics.isBigO_iff] at ha ⊢
  obtain ⟨C, hC⟩ := ha
  -- Use |C| to ensure we have a nonnegative constant
  use |C|
  rw [Filter.eventually_atTop] at hC ⊢
  obtain ⟨N, hN⟩ := hC
  refine ⟨2 * N, fun m hm ↦ ?_⟩
  simp only [Real.norm_eq_abs]
  by_cases heven : Even m
  · -- m = 2*n for some n, and evenExt a (2*n) = a n
    obtain ⟨n, hn⟩ := heven
    have hn_2n : m = 2 * n := by omega
    have hn_ge : n ≥ N := by omega
    rw [hn_2n, evenExt_even]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
    have hm_nonneg : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
    have hbound := hN n hn_ge
    simp only [Real.norm_eq_abs, abs_of_nonneg hn_nonneg] at hbound
    rw [abs_of_nonneg hm_nonneg]
    have hC_abs : C ≤ |C| := le_abs_self C
    have hn_le_2n : (n : ℝ) ≤ (2 * n : ℕ) := by simp only [Nat.cast_mul, Nat.cast_ofNat]; linarith
    have hpow_le : (n : ℝ) ^ k ≤ ((2 * n : ℕ) : ℝ) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le_2n k
    calc ‖a n‖ ≤ C * (n : ℝ) ^ k := hbound
      _ ≤ |C| * (n : ℝ) ^ k := mul_le_mul_of_nonneg_right hC_abs hn_nonneg
      _ ≤ |C| * ((2 * n : ℕ) : ℝ) ^ k := mul_le_mul_of_nonneg_left hpow_le (abs_nonneg C)
  · -- m is odd, so evenExt a m = 0
    obtain ⟨n, hn⟩ := Nat.not_even_iff_odd.mp heven
    have heq : evenExt a m = 0 := hn ▸ evenExt_odd a n
    rw [heq, norm_zero]
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
    rw [abs_of_nonneg hm_nonneg]
    exact mul_nonneg (abs_nonneg C) hm_nonneg

/-- toIntCoeff preserves polynomial growth (for atTop on ℤ). -/
lemma toIntCoeff_poly {a : ℕ → ℂ} {k : ℕ}
    (ha : a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ))) :
    toIntCoeff a =O[Filter.atTop] (fun n ↦ (n ^ k : ℝ)) := by
  rw [Asymptotics.isBigO_iff] at ha ⊢
  obtain ⟨C, hC⟩ := ha
  use |C|  -- Use |C| for robustness if caller provides negative C
  rw [Filter.eventually_atTop] at hC ⊢
  obtain ⟨N, hN⟩ := hC
  refine ⟨(N : ℤ), fun m hm ↦ ?_⟩
  simp only [toIntCoeff]
  have hm_nonneg : 0 ≤ m := le_trans (Int.natCast_nonneg N) hm
  simp only [not_lt.mpr hm_nonneg, ↓reduceIte]
  have htoNat : m.toNat ≥ N := by omega
  have hm_eq : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm_nonneg
  have hm_real_eq : (m.toNat : ℝ) = (m : ℝ) := by
    have h : (m.toNat : ℤ) = m := hm_eq
    exact congrArg (↑· : ℤ → ℝ) h
  have := hN m.toNat htoNat
  have hnat_nonneg : (0 : ℝ) ≤ (m.toNat : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) k
  have hint_nonneg : (0 : ℝ) ≤ (m : ℝ) ^ k := by rw [← hm_real_eq]; exact hnat_nonneg
  simp only [Real.norm_eq_abs, abs_of_nonneg hnat_nonneg] at this
  simp only [Real.norm_eq_abs, abs_of_nonneg hint_nonneg]
  calc ‖a m.toNat‖ ≤ C * (m.toNat : ℝ) ^ k := this
    _ ≤ |C| * (m.toNat : ℝ) ^ k := mul_le_mul_of_nonneg_right (le_abs_self C) hnat_nonneg
    _ = |C| * (m : ℝ) ^ k := by rw [hm_real_eq]

/-- c_E₂E₄E₆ has polynomial growth O(n^11).
    Cauchy product of two O(n^5) sequences, then even extension. -/
lemma c_E₂E₄E₆_poly : c_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 11 : ℝ)) := by
  unfold c_E₂E₄E₆
  apply toIntCoeff_poly
  apply evenExt_poly
  -- cauchyCoeff a_E₂E₄E₆ a_E₂E₄E₆: O(n^5) × O(n^5) → O(n^{5+5+1}) = O(n^11)
  exact cauchyCoeff_poly a_E₂E₄E₆_poly a_E₂E₄E₆_poly

/-- c_E₄_E₂E₄E₆ has polynomial growth O(n^10).
    Cauchy product of O(n^4) and O(n^5) sequences, then even extension. -/
lemma c_E₄_E₂E₄E₆_poly : c_E₄_E₂E₄E₆ =O[Filter.atTop] (fun n ↦ (n ^ 10 : ℝ)) := by
  unfold c_E₄_E₂E₄E₆
  apply toIntCoeff_poly
  apply evenExt_poly
  -- cauchyCoeff b_E₄ a_E₂E₄E₆: O(n^4) × O(n^5) → O(n^{4+5+1}) = O(n^10)
  exact cauchyCoeff_poly b_E₄_poly a_E₂E₄E₆_poly

/-- c_E₄_sq has polynomial growth O(n^9).
    Cauchy product of two O(n^4) sequences, then even extension. -/
lemma c_E₄_sq_poly : c_E₄_sq =O[Filter.atTop] (fun n ↦ (n ^ 9 : ℝ)) := by
  unfold c_E₄_sq
  apply toIntCoeff_poly
  apply evenExt_poly
  -- cauchyCoeff b_E₄ b_E₄: O(n^4) × O(n^4) → O(n^{4+4+1}) = O(n^9)
  exact cauchyCoeff_poly b_E₄_poly b_E₄_poly

end MagicFunction.a.FourierExpansions

end
