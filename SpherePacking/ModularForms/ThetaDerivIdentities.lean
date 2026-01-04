import SpherePacking.ModularForms.ThetaDerivSlashActions
import SpherePacking.ModularForms.AtImInfty

/-!
# Theta Derivative Identities

This file proves the Serre derivative identities for Jacobi theta functions
(Blueprint Proposition 6.52, equations (32)–(34)):

* `serre_D_H₂` : serre_D 2 H₂ = (1/6) * (H₂² + 2*H₂*H₄)
* `serre_D_H₃` : serre_D 2 H₃ = (1/6) * (H₂² - H₄²)
* `serre_D_H₄` : serre_D 2 H₄ = -(1/6) * (2*H₂*H₄ + H₄²)

## Contents

**Phase 6: Level-1 invariants**
* `theta_g` (weight 6): g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
* `theta_h` (weight 8): h = f₂² + f₂f₄ + f₄²
* S/T invariance: theta_g and theta_h are SL(2,ℤ)-invariant

**Phase 7: Cusp form arguments**
* Tendsto lemmas for f₂, f₄, theta_g, theta_h at infinity
* Cusp form construction for theta_g and theta_h

**Phase 8: Dimension vanishing**
* theta_g = 0 and theta_h = 0 by weight < 12 cusp form vanishing

**Phase 9: Main deduction**
* f₂ = f₃ = f₄ = 0

**Phase 10: Main theorems**
* serre_D_H₂, serre_D_H₃, serre_D_H₄

## Strategy

Using the S/T transformation rules from `ThetaDerivSlashActions`:
- f₂|S = -f₄, f₂|T = -f₂, f₄|S = -f₂, f₄|T = f₃

We construct g and h such that g|S = g, g|T = g, h|S = h, h|T = h.
Then g and h are level-1 cusp forms of weights 6 and 8, hence vanish.
From g = h = 0 we deduce f₂ = f₄ = 0, giving the main theorems.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => CongruenceSubgroup.Gamma n

/-!
## Phase 6: Level-1 Invariants g, h
-/

/-- Level-1 invariant of weight 6: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ -/
noncomputable def theta_g : ℍ → ℂ := fun z =>
  (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z

/-- Level-1 invariant of weight 8: h = f₂² + f₂f₄ + f₄² -/
noncomputable def theta_h : ℍ → ℂ := fun z =>
  f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2

/-- g is invariant under S.

Proof: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
Under S: H₂ ↦ -H₄, H₄ ↦ -H₂, f₂ ↦ -f₄, f₄ ↦ -f₂
g|S = (2(-H₄) + (-H₂))(-f₄) + ((-H₄) + 2(-H₂))(-f₂)
    = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂
    = g -/
lemma theta_g_S_action : (theta_g ∣[(6 : ℤ)] S) = theta_g := by
  have hf₂ := f₂_S_action
  have hf₄ := f₄_S_action
  have hH₂ := H₂_S_action
  have hH₄ := H₄_S_action
  -- First, prove the transformations for the linear combinations
  have h_2H₂_H₄ : ((fun z => 2 * H₂ z + H₄ z) ∣[(2 : ℤ)] S) =
      fun z => -(2 * H₄ z + H₂ z) := by
    have h_smul := SL_smul_slash (2 : ℤ) S H₂ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) S ((2 : ℂ) • H₂) H₄
    have hfun1 : (fun z => 2 * H₂ z + H₄ z) = ((2 : ℂ) • H₂) + H₄ := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  have h_H₂_2H₄ : ((fun z => H₂ z + 2 * H₄ z) ∣[(2 : ℤ)] S) =
      fun z => -(H₄ z + 2 * H₂ z) := by
    have h_smul := SL_smul_slash (2 : ℤ) S H₄ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) S H₂ ((2 : ℂ) • H₄)
    have hfun1 : (fun z => H₂ z + 2 * H₄ z) = H₂ + ((2 : ℂ) • H₄) := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Now prove the product transformations using mul_slash_SL2
  have h_term1 : ((fun z => (2 * H₂ z + H₄ z) * f₂ z) ∣[(6 : ℤ)] S) =
      fun z => (2 * H₄ z + H₂ z) * f₄ z := by
    have hmul := mul_slash_SL2 2 4 S (fun z => 2 * H₂ z + H₄ z) f₂
    have hfun : (fun z => (2 * H₂ z + H₄ z) * f₂ z) =
        (fun z => 2 * H₂ z + H₄ z) * f₂ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_2H₂_H₄, hf₂]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]; ring
  have h_term2 : ((fun z => (H₂ z + 2 * H₄ z) * f₄ z) ∣[(6 : ℤ)] S) =
      fun z => (H₄ z + 2 * H₂ z) * f₂ z := by
    have hmul := mul_slash_SL2 2 4 S (fun z => H₂ z + 2 * H₄ z) f₄
    have hfun : (fun z => (H₂ z + 2 * H₄ z) * f₄ z) =
        (fun z => H₂ z + 2 * H₄ z) * f₄ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_H₂_2H₄, hf₄]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]; ring
  -- Combine: g|S = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂ = g
  have hfun_g : theta_g =
      (fun z => (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z) := by
    funext z; unfold theta_g; ring
  rw [hfun_g]
  have hfun_sum : (fun z => (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z) =
      (fun z => (2 * H₂ z + H₄ z) * f₂ z) + (fun z => (H₂ z + 2 * H₄ z) * f₄ z) := by
    funext; simp [Pi.add_apply]
  have h_add := SlashAction.add_slash (6 : ℤ) S
    (fun z => (2 * H₂ z + H₄ z) * f₂ z) (fun z => (H₂ z + 2 * H₄ z) * f₄ z)
  rw [hfun_sum, h_add, h_term1, h_term2]
  funext z; simp only [Pi.add_apply]; ring

/-- g is invariant under T.

Proof: Under T: H₂ ↦ -H₂, H₄ ↦ H₃, f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
g|T = (2(-H₂) + H₃)(-f₂) + ((-H₂) + 2H₃)(f₂ + f₄)
Using Jacobi: H₃ = H₂ + H₄, simplifies to g. -/
lemma theta_g_T_action : (theta_g ∣[(6 : ℤ)] T) = theta_g := by
  have hf₂ := f₂_T_action
  have hf₄ := f₄_T_action
  have hH₂ := H₂_T_action
  have hH₄ := H₄_T_action
  have h_jacobi := fun z => jacobi_identity' z
  -- Under T: H₂ → -H₂, H₄ → H₃ = H₂ + H₄, f₂ → -f₂, f₄ → f₃
  -- Transform linear combinations
  have h_2H₂_H₄ : ((fun z => 2 * H₂ z + H₄ z) ∣[(2 : ℤ)] T) =
      fun z => -2 * H₂ z + H₃ z := by
    have h_smul := SL_smul_slash (2 : ℤ) T H₂ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) T ((2 : ℂ) • H₂) H₄
    have hfun1 : (fun z => 2 * H₂ z + H₄ z) = ((2 : ℂ) • H₂) + H₄ := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
  have h_H₂_2H₄ : ((fun z => H₂ z + 2 * H₄ z) ∣[(2 : ℤ)] T) =
      fun z => -H₂ z + 2 * H₃ z := by
    have h_smul := SL_smul_slash (2 : ℤ) T H₄ (2 : ℂ)
    have h_add := SlashAction.add_slash (2 : ℤ) T H₂ ((2 : ℂ) • H₄)
    have hfun1 : (fun z => H₂ z + 2 * H₄ z) = H₂ + ((2 : ℂ) • H₄) := by
      funext; simp [Pi.add_apply, Pi.smul_apply]
    rw [hfun1, h_add, h_smul, hH₂, hH₄]
    funext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
  -- Product transformations
  have h_term1 : ((fun z => (2 * H₂ z + H₄ z) * f₂ z) ∣[(6 : ℤ)] T) =
      fun z => (-2 * H₂ z + H₃ z) * (-f₂ z) := by
    have hmul := mul_slash_SL2 2 4 T (fun z => 2 * H₂ z + H₄ z) f₂
    have hfun : (fun z => (2 * H₂ z + H₄ z) * f₂ z) =
        (fun z => 2 * H₂ z + H₄ z) * f₂ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_2H₂_H₄, hf₂]
    funext z; simp [Pi.mul_apply, Pi.neg_apply]
  have h_term2 : ((fun z => (H₂ z + 2 * H₄ z) * f₄ z) ∣[(6 : ℤ)] T) =
      fun z => (-H₂ z + 2 * H₃ z) * f₃ z := by
    have hmul := mul_slash_SL2 2 4 T (fun z => H₂ z + 2 * H₄ z) f₄
    have hfun : (fun z => (H₂ z + 2 * H₄ z) * f₄ z) =
        (fun z => H₂ z + 2 * H₄ z) * f₄ := by funext; simp [Pi.mul_apply]
    have h6 : (6 : ℤ) = 2 + 4 := by norm_num
    rw [hfun, h6, hmul, h_H₂_2H₄, hf₄]
    funext z; simp [Pi.mul_apply]
  -- Now combine and simplify using Jacobi: H₃ = H₂ + H₄, f₃ = f₂ + f₄
  have hfun_g : theta_g = (fun z => (2 * H₂ z + H₄ z) * f₂ z +
      (H₂ z + 2 * H₄ z) * f₄ z) := by funext z; unfold theta_g; ring
  rw [hfun_g]
  have hfun_sum : (fun z => (2 * H₂ z + H₄ z) * f₂ z + (H₂ z + 2 * H₄ z) * f₄ z) =
      (fun z => (2 * H₂ z + H₄ z) * f₂ z) + (fun z => (H₂ z + 2 * H₄ z) * f₄ z) := by
    funext; simp [Pi.add_apply]
  have h_add := SlashAction.add_slash (6 : ℤ) T
    (fun z => (2 * H₂ z + H₄ z) * f₂ z) (fun z => (H₂ z + 2 * H₄ z) * f₄ z)
  rw [hfun_sum, h_add, h_term1, h_term2]
  -- Simplify using Jacobi identity
  funext z
  simp only [Pi.add_apply]
  -- H₃ = H₂ + H₄ and f₃ = f₂ + f₄
  have hH₃ : H₃ z = H₂ z + H₄ z := (h_jacobi z).symm
  have hf₃ : f₃ z = f₂ z + f₄ z := (congrFun f₂_add_f₄_eq_f₃ z).symm
  rw [hH₃, hf₃]
  ring

/-- h is invariant under S.

Proof: h = f₂² + f₂f₄ + f₄²
Under S: f₂|[4]S = -f₄, f₄|[4]S = -f₂
Using mul_slash_SL2: (f₂²)|[8]S = (f₂|[4]S)² = (-f₄)² = f₄²
                     (f₂f₄)|[8]S = (f₂|[4]S)(f₄|[4]S) = (-f₄)(-f₂) = f₂f₄
                     (f₄²)|[8]S = (f₄|[4]S)² = (-f₂)² = f₂²
So h|[8]S = f₄² + f₂f₄ + f₂² = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_S_action : (theta_h ∣[(8 : ℤ)] S) = theta_h := by
  have hf₂ := f₂_S_action
  have hf₄ := f₄_S_action
  -- h = f₂² + f₂f₄ + f₄² = f₂*f₂ + f₂*f₄ + f₄*f₄
  -- Use mul_slash_SL2: (f*g)|[k1+k2]S = (f|[k1]S)*(g|[k2]S)
  have h_f₂_sq : ((fun z => f₂ z ^ 2) ∣[(8 : ℤ)] S) = fun z => f₄ z ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₂
    rw [hf₂] at hmul
    have hfun : (fun z => f₂ z ^ 2) = (f₂ * f₂) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, sq, neg_mul_neg]
  have h_f₄_sq : ((fun z => f₄ z ^ 2) ∣[(8 : ℤ)] S) = fun z => f₂ z ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₄ f₄
    rw [hf₄] at hmul
    have hfun : (fun z => f₄ z ^ 2) = (f₄ * f₄) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, sq, neg_mul_neg]
  have h_f₂f₄ : ((fun z => f₂ z * f₄ z) ∣[(8 : ℤ)] S) = fun z => f₂ z * f₄ z := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₄
    rw [hf₂, hf₄] at hmul
    have hfun : (fun z => f₂ z * f₄ z) = (f₂ * f₄) := by funext w; simp [Pi.mul_apply]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, neg_mul_neg, mul_comm]
  -- Combine: h|S = f₄² + f₂f₄ + f₂² = h
  have hfun_h : theta_h = (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) := by
    funext z; unfold theta_h; ring
  rw [hfun_h]
  have hfun_lhs1 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z) =
      (fun z => f₂ z ^ 2) + (fun z => f₂ z * f₄ z) := by funext; simp [Pi.add_apply]
  have h_add1 := SlashAction.add_slash (8 : ℤ) S (fun z => f₂ z ^ 2) (fun z => f₂ z * f₄ z)
  have hfun_lhs2 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) =
      (fun z => f₂ z ^ 2 + f₂ z * f₄ z) + (fun z => f₄ z ^ 2) := by
    funext; simp [Pi.add_apply]
  have h_add2 := SlashAction.add_slash (8 : ℤ) S
    (fun z => f₂ z ^ 2 + f₂ z * f₄ z) (fun z => f₄ z ^ 2)
  rw [hfun_lhs2, h_add2, hfun_lhs1, h_add1, h_f₂_sq, h_f₂f₄, h_f₄_sq]
  funext z; simp only [Pi.add_apply]; ring

/-- h is invariant under T.

Proof: Under T: f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
h|T = (-f₂)² + (-f₂)(f₂ + f₄) + (f₂ + f₄)²
    = f₂² - f₂² - f₂f₄ + f₂² + 2f₂f₄ + f₄²
    = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_T_action : (theta_h ∣[(8 : ℤ)] T) = theta_h := by
  have hf₂ := f₂_T_action
  have hf₄ := f₄_T_action
  have hf₂f₄ := f₂_add_f₄_eq_f₃
  -- Under T: f₂ → -f₂, f₄ → f₃ = f₂ + f₄
  -- (f₂²)|T = (-f₂)² = f₂², (f₄²)|T = (f₂+f₄)², (f₂f₄)|T = (-f₂)(f₂+f₄)
  have h_f₂_sq : ((fun z => f₂ z ^ 2) ∣[(8 : ℤ)] T) = fun z => f₂ z ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₂
    rw [hf₂] at hmul
    have hfun : (fun z => f₂ z ^ 2) = (f₂ * f₂) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z; simp only [Pi.mul_apply, Pi.neg_apply, neg_mul_neg]
  have h_f₄_sq : ((fun z => f₄ z ^ 2) ∣[(8 : ℤ)] T) = fun z => (f₂ z + f₄ z) ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₄ f₄
    rw [hf₄] at hmul
    have hfun : (fun z => f₄ z ^ 2) = (f₄ * f₄) := by funext w; simp [Pi.mul_apply, sq]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z
    simp only [Pi.mul_apply, sq]
    rw [(congrFun hf₂f₄ z).symm, Pi.add_apply]
  have h_f₂f₄' : ((fun z => f₂ z * f₄ z) ∣[(8 : ℤ)] T) =
      fun z => (-f₂ z) * (f₂ z + f₄ z) := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₄
    rw [hf₂, hf₄] at hmul
    have hfun : (fun z => f₂ z * f₄ z) = (f₂ * f₄) := by funext w; simp [Pi.mul_apply]
    have h8 : (8 : ℤ) = 4 + 4 := by norm_num
    rw [hfun, h8, hmul]
    funext z
    simp only [Pi.mul_apply, Pi.neg_apply]
    rw [(congrFun hf₂f₄ z).symm, Pi.add_apply]
  -- Combine: h|T = f₂² + (-f₂)(f₂+f₄) + (f₂+f₄)² = h
  have hfun_h : theta_h = (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) := by
    funext z; unfold theta_h; ring
  rw [hfun_h]
  have hfun_lhs1 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z) =
      (fun z => f₂ z ^ 2) + (fun z => f₂ z * f₄ z) := by funext; simp [Pi.add_apply]
  have h_add1 := SlashAction.add_slash (8 : ℤ) T (fun z => f₂ z ^ 2) (fun z => f₂ z * f₄ z)
  have hfun_lhs2 : (fun z => f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) =
      (fun z => f₂ z ^ 2 + f₂ z * f₄ z) + (fun z => f₄ z ^ 2) := by
    funext; simp [Pi.add_apply]
  have h_add2 := SlashAction.add_slash (8 : ℤ) T
    (fun z => f₂ z ^ 2 + f₂ z * f₄ z) (fun z => f₄ z ^ 2)
  rw [hfun_lhs2, h_add2, hfun_lhs1, h_add1, h_f₂_sq, h_f₂f₄', h_f₄_sq]
  funext z; simp only [Pi.add_apply]; ring

/-!
## Infrastructure Lemmas (from PR #248)

These lemmas are proved in PR #248 (EisensteinAsymptotics). Once #248 merges,
remove these sorry stubs and import from EisensteinAsymptotics.
-/

/-- D F → 0 for MDifferentiable F with F → c (constant).
Proved in PR #248 (EisensteinAsymptotics). -/
lemma D_tendsto_zero_of_tendsto_const {F : ℍ → ℂ} {c : ℂ}
    (_ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (_ : Tendsto F atImInfty (𝓝 c)) :
    Tendsto (D F) atImInfty (𝓝 0) := by
  sorry

/-- E₂ → 1 at infinity.
Proved in PR #248 (EisensteinAsymptotics). -/
lemma E₂_tendsto_one_atImInfty : Tendsto E₂ atImInfty (𝓝 1) := by
  sorry

/-!
## Phase 7: Cusp Form Arguments

We need to show g and h vanish at infinity.
The tendsto lemmas for H₂, H₃, H₄ are already in AtImInfty.lean:
- H₂_tendsto_atImInfty : Tendsto H₂ atImInfty (𝓝 0)
- H₃_tendsto_atImInfty : Tendsto H₃ atImInfty (𝓝 1)
- H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 1)
-/

/-- theta_g is MDifferentiable (from MDifferentiable of f₂, f₄, H₂, H₄) -/
lemma theta_g_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) theta_g := by
  unfold theta_g
  apply MDifferentiable.add
  · apply MDifferentiable.mul
    · apply MDifferentiable.add
      · apply MDifferentiable.mul mdifferentiable_const H₂_SIF_MDifferentiable
      · exact H₄_SIF_MDifferentiable
    · exact f₂_MDifferentiable
  · apply MDifferentiable.mul
    · apply MDifferentiable.add H₂_SIF_MDifferentiable
      · apply MDifferentiable.mul mdifferentiable_const H₄_SIF_MDifferentiable
    · exact f₄_MDifferentiable

/-- theta_h is MDifferentiable (from MDifferentiable of f₂, f₄) -/
lemma theta_h_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) theta_h := by
  unfold theta_h
  apply MDifferentiable.add
  · apply MDifferentiable.add
    · simp only [pow_two]; exact f₂_MDifferentiable.mul f₂_MDifferentiable
    · exact f₂_MDifferentiable.mul f₄_MDifferentiable
  · simp only [pow_two]; exact f₄_MDifferentiable.mul f₄_MDifferentiable

/-- theta_g is slash-invariant under Γ(1) in GL₂(ℝ) form -/
lemma theta_g_slash_invariant_GL :
    ∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 1),
    theta_g ∣[(6 : ℤ)] γ = theta_g :=
  slashaction_generators_GL2R theta_g 6 theta_g_S_action theta_g_T_action

/-- theta_h is slash-invariant under Γ(1) in GL₂(ℝ) form -/
lemma theta_h_slash_invariant_GL :
    ∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 1),
    theta_h ∣[(8 : ℤ)] γ = theta_h :=
  slashaction_generators_GL2R theta_h 8 theta_h_S_action theta_h_T_action

/-- theta_g as a SlashInvariantForm of level 1 -/
noncomputable def theta_g_SIF : SlashInvariantForm (Γ 1) 6 where
  toFun := theta_g
  slash_action_eq' := theta_g_slash_invariant_GL

/-- theta_h as a SlashInvariantForm of level 1 -/
noncomputable def theta_h_SIF : SlashInvariantForm (Γ 1) 8 where
  toFun := theta_h
  slash_action_eq' := theta_h_slash_invariant_GL

/-- If D F → 0 and F → c, then serre_D k F → -k/12 * c.
Uses E₂_tendsto_one_atImInfty to compute E₂ * F → c. -/
lemma serre_D_tendsto_of_tendsto {k : ℤ} {F : ℍ → ℂ} {c : ℂ}
    (hD : Tendsto (D F) atImInfty (𝓝 0))
    (hF : Tendsto F atImInfty (𝓝 c)) :
    Tendsto (serre_D k F) atImInfty (𝓝 (-(k : ℂ) / 12 * c)) := by
  -- serre_D k F = D F - k/12 * E₂ * F
  -- D F → 0, E₂ → 1, F → c, so serre_D k F → 0 - k/12 * 1 * c = -k/12 * c
  have hE₂_F : Tendsto (fun z => E₂ z * F z) atImInfty (𝓝 c) := by
    have := E₂_tendsto_one_atImInfty.mul hF
    simp only [one_mul] at this
    exact this
  have h_coef : Tendsto (fun z => (k : ℂ) * 12⁻¹ * E₂ z * F z) atImInfty
      (𝓝 ((k : ℂ) / 12 * c)) := by
    have := hE₂_F.const_mul ((k : ℂ) * 12⁻¹)
    simp only [div_eq_mul_inv]
    convert this using 2; ring
  have h_eq : serre_D k F = fun z => D F z - (k : ℂ) * 12⁻¹ * E₂ z * F z := rfl
  rw [h_eq]
  have hsub := hD.sub h_coef
  convert hsub using 2
  simp only [div_eq_mul_inv]; ring

/-- f₂ tends to 0 at infinity.
Proof: f₂ = serre_D 2 H₂ - (1/6)H₂(H₂ + 2H₄)
Since H₂ → 0 and serre_D 2 H₂ = D H₂ - (1/6)E₂ H₂ → 0,
we get f₂ → 0 - 0 = 0. -/
lemma f₂_tendsto_atImInfty : Tendsto f₂ atImInfty (𝓝 0) := by
  have hH₂ := H₂_tendsto_atImInfty
  have hH₄ := H₄_tendsto_atImInfty
  have hD_H₂ := D_tendsto_zero_of_tendsto_const H₂_SIF_MDifferentiable hH₂
  have h_serre_H₂ : Tendsto (serre_D 2 H₂) atImInfty (𝓝 0) := by
    simpa using serre_D_tendsto_of_tendsto hD_H₂ hH₂
  have h_prod : Tendsto (fun z => H₂ z * (H₂ z + 2 * H₄ z)) atImInfty (𝓝 0) := by
    simpa using hH₂.mul (hH₂.add (hH₄.const_mul 2))
  have h_final := h_serre_H₂.sub (h_prod.const_mul (1/6 : ℂ))
  simp only [mul_zero, sub_zero] at h_final
  convert h_final using 1

/-- f₄ tends to 0 at infinity.
Proof: f₄ = serre_D 2 H₄ + (1/6)H₄(2H₂ + H₄)
serre_D 2 H₄ = D H₄ - (1/6)E₂ H₄ → 0 - (1/6)*1*1 = -1/6 (since H₄ → 1, E₂ → 1)
H₄(2H₂ + H₄) → 1*(0 + 1) = 1
So f₄ → -1/6 + (1/6)*1 = 0. -/
lemma f₄_tendsto_atImInfty : Tendsto f₄ atImInfty (𝓝 0) := by
  have hH₂ := H₂_tendsto_atImInfty
  have hH₄ := H₄_tendsto_atImInfty
  have hD_H₄ := D_tendsto_zero_of_tendsto_const H₄_SIF_MDifferentiable hH₄
  have h_serre_H₄ : Tendsto (serre_D 2 H₄) atImInfty (𝓝 (-(1/6 : ℂ))) := by
    convert serre_D_tendsto_of_tendsto hD_H₄ hH₄ using 2; norm_num
  have h_sum : Tendsto (fun z => 2 * H₂ z + H₄ z) atImInfty (𝓝 1) := by
    simpa using (hH₂.const_mul 2).add hH₄
  have h_prod : Tendsto (fun z => H₄ z * (2 * H₂ z + H₄ z)) atImInfty (𝓝 1) := by
    simpa using hH₄.mul h_sum
  have h_scaled : Tendsto (fun z => (1/6 : ℂ) * (H₄ z * (2 * H₂ z + H₄ z)))
      atImInfty (𝓝 (1/6 : ℂ)) := by simpa using h_prod.const_mul (1/6 : ℂ)
  have h_final := h_serre_H₄.add h_scaled
  simp only [neg_add_cancel] at h_final
  convert h_final using 1

/-- theta_g tends to 0 at infinity.
theta_g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄.
Since 2H₂ + H₄ → 1, H₂ + 2H₄ → 2, and f₂, f₄ → 0, we get theta_g → 0. -/
lemma theta_g_tendsto_atImInfty : Tendsto theta_g atImInfty (𝓝 0) := by
  have hH₂ := H₂_tendsto_atImInfty
  have hH₄ := H₄_tendsto_atImInfty
  have hf₂ := f₂_tendsto_atImInfty
  have hf₄ := f₄_tendsto_atImInfty
  have h_coef1 : Tendsto (fun z => 2 * H₂ z + H₄ z) atImInfty (𝓝 1) := by
    simpa using (hH₂.const_mul 2).add hH₄
  have h_coef2 : Tendsto (fun z => H₂ z + 2 * H₄ z) atImInfty (𝓝 2) := by
    simpa using hH₂.add (hH₄.const_mul 2)
  have h_term1 : Tendsto (fun z => (2 * H₂ z + H₄ z) * f₂ z) atImInfty (𝓝 0) := by
    simpa using h_coef1.mul hf₂
  have h_term2 : Tendsto (fun z => (H₂ z + 2 * H₄ z) * f₄ z) atImInfty (𝓝 0) := by
    simpa using h_coef2.mul hf₄
  have hsum := h_term1.add h_term2
  simp only [add_zero] at hsum
  convert hsum using 1

/-- theta_h tends to 0 at infinity.
theta_h = f₂² + f₂f₄ + f₄² → 0 + 0 + 0 = 0 as f₂, f₄ → 0. -/
lemma theta_h_tendsto_atImInfty : Tendsto theta_h atImInfty (𝓝 0) := by
  have hf₂ := f₂_tendsto_atImInfty
  have hf₄ := f₄_tendsto_atImInfty
  have h_f₂_sq : Tendsto (fun z => f₂ z ^ 2) atImInfty (𝓝 0) := by simpa [sq] using hf₂.mul hf₂
  have h_f₄_sq : Tendsto (fun z => f₄ z ^ 2) atImInfty (𝓝 0) := by simpa [sq] using hf₄.mul hf₄
  have h_f₂f₄ : Tendsto (fun z => f₂ z * f₄ z) atImInfty (𝓝 0) := by simpa using hf₂.mul hf₄
  have hsum := (h_f₂_sq.add h_f₂f₄).add h_f₄_sq
  simp only [add_zero] at hsum
  convert hsum using 1

/-- Build a cusp form from a SlashInvariantForm that's MDifferentiable and
tends to zero at infinity. This pattern is reused for theta_g and theta_h. -/
lemma IsCuspForm_of_SIF_tendsto_zero {k : ℤ} (f_SIF : SlashInvariantForm (Γ 1) k)
    (h_mdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f_SIF.toFun)
    (h_zero : Tendsto f_SIF.toFun atImInfty (𝓝 0)) :
    ∃ (f_MF : ModularForm (Γ 1) k),
    IsCuspForm (Γ 1) k f_MF ∧ ∀ z, f_MF z = f_SIF.toFun z := by
  -- Use slash invariance to show zero at all cusps
  have h_zero_at_cusps : ∀ {c : OnePoint ℝ}, IsCusp c (Γ 1) → c.IsZeroAt f_SIF.toFun k := by
    intro c hc
    apply zero_at_cusps_of_zero_at_infty hc
    intro A ⟨A', hA'⟩
    have h_inv := f_SIF.slash_action_eq' A ⟨A', CongruenceSubgroup.mem_Gamma_one A', hA'⟩
    rw [h_inv]
    exact h_zero
  -- Construct CuspForm
  let f_CF : CuspForm (Γ 1) k := {
    toSlashInvariantForm := f_SIF
    holo' := h_mdiff
    zero_at_cusps' := fun hc => h_zero_at_cusps hc
  }
  let f_MF := CuspForm_to_ModularForm (Γ 1) k f_CF
  exact ⟨f_MF, ⟨⟨f_CF, rfl⟩, fun _ => rfl⟩⟩

/-- g is a cusp form of level 1. -/
lemma theta_g_IsCuspForm : ∃ (g_MF : ModularForm (Γ 1) 6), IsCuspForm (Γ 1) 6 g_MF ∧
    ∀ z, g_MF z = theta_g z :=
  IsCuspForm_of_SIF_tendsto_zero theta_g_SIF theta_g_MDifferentiable theta_g_tendsto_atImInfty

/-- h is a cusp form of level 1. -/
lemma theta_h_IsCuspForm : ∃ (h_MF : ModularForm (Γ 1) 8), IsCuspForm (Γ 1) 8 h_MF ∧
    ∀ z, h_MF z = theta_h z :=
  IsCuspForm_of_SIF_tendsto_zero theta_h_SIF theta_h_MDifferentiable theta_h_tendsto_atImInfty

/-!
## Phase 8: Apply Dimension Vanishing
-/

/-- g = 0 by dimension argument.

Proof: g is a level-1 cusp form of weight 6. By IsCuspForm_weight_lt_eq_zero,
all cusp forms of weight < 12 vanish. Hence g = 0. -/
lemma theta_g_eq_zero : theta_g = 0 := by
  obtain ⟨g_MF, hg_cusp, hg_eq⟩ := theta_g_IsCuspForm
  have hzero := IsCuspForm_weight_lt_eq_zero 6 (by norm_num : (6 : ℤ) < 12) g_MF hg_cusp
  funext z
  rw [← hg_eq z, hzero]
  rfl

/-- h = 0 by dimension argument.

Proof: h is a level-1 cusp form of weight 8. By IsCuspForm_weight_lt_eq_zero,
all cusp forms of weight < 12 vanish. Hence h = 0. -/
lemma theta_h_eq_zero : theta_h = 0 := by
  obtain ⟨h_MF, hh_cusp, hh_eq⟩ := theta_h_IsCuspForm
  have hzero := IsCuspForm_weight_lt_eq_zero 8 (by norm_num : (8 : ℤ) < 12) h_MF hh_cusp
  funext z
  rw [← hh_eq z, hzero]
  rfl

/-!
## H_sum_sq: H₂² + H₂H₄ + H₄²
-/

/-- H₂² + H₂H₄ + H₄² -/
noncomputable def H_sum_sq : ℍ → ℂ := fun z => H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2

/-- H_sum_sq is MDifferentiable -/
lemma H_sum_sq_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H_sum_sq := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₂ z ^ 2) := by
    simpa [sq] using H₂_SIF_MDifferentiable.mul H₂_SIF_MDifferentiable
  have h2 := H₂_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable
  have h3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => H₄ z ^ 2) := by
    simpa [sq] using H₄_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable
  exact (h1.add h2).add h3

/-- H_sum_sq → 1 at infinity -/
lemma H_sum_sq_tendsto : Tendsto H_sum_sq atImInfty (𝓝 1) := by
  have h_H₂_lim := H₂_tendsto_atImInfty
  have h_H₄_lim := H₄_tendsto_atImInfty
  have h1 : Tendsto (fun z => H₂ z ^ 2) atImInfty (𝓝 0) := by
    simpa [sq] using h_H₂_lim.mul h_H₂_lim
  have h2 : Tendsto (fun z => H₂ z * H₄ z) atImInfty (𝓝 0) := by
    simpa using h_H₂_lim.mul h_H₄_lim
  have h3 : Tendsto (fun z => H₄ z ^ 2) atImInfty (𝓝 1) := by
    simpa [sq] using h_H₄_lim.mul h_H₄_lim
  have hsum := (h1.add h2).add h3
  simp only [zero_add, add_zero] at hsum
  exact hsum

/-- H_sum_sq ≠ 0 (since it tends to 1 ≠ 0) -/
lemma H_sum_sq_ne_zero : H_sum_sq ≠ 0 := by
  intro h
  have h_limit := H_sum_sq_tendsto
  rw [h] at h_limit
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h_limit).symm

/-- 3 * H_sum_sq ≠ 0 -/
lemma three_H_sum_sq_ne_zero : (fun z => 3 * H_sum_sq z) ≠ 0 := by
  intro h
  apply H_sum_sq_ne_zero
  funext z
  exact (mul_eq_zero.mp (congrFun h z)).resolve_left (by norm_num)

/-- 3 * H_sum_sq is MDifferentiable -/
lemma three_H_sum_sq_MDifferentiable :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => 3 * H_sum_sq z) :=
  mdifferentiable_const.mul H_sum_sq_MDifferentiable

/-!
## Phase 9: Deduce f₂ = f₃ = f₄ = 0
-/

/-- Key algebraic identity for proving f₂ = f₄ = 0.
Given Af₂ + Bf₄ = 0, we have f₄² * (A² - AB + B²) = A² * (f₂² + f₂f₄ + f₄²). -/
lemma f₄_sq_mul_eq (z : ℍ) (hg_z : theta_g z = 0) :
    f₄ z ^ 2 * (3 * H_sum_sq z) = (2 * H₂ z + H₄ z) ^ 2 * theta_h z := by
  unfold H_sum_sq
  -- Define A = 2H₂ + H₄, B = H₂ + 2H₄
  set A := 2 * H₂ z + H₄ z with hA
  set B := H₂ z + 2 * H₄ z with hB
  -- From theta_g = 0: A * f₂ + B * f₄ = 0
  have h_Af₂_eq : A * f₂ z + B * f₄ z = 0 := by
    simp only [theta_g, hA, hB] at hg_z ⊢
    linear_combination hg_z
  -- Af₂ = -Bf₄
  have hAf₂ : A * f₂ z = -(B * f₄ z) := by linear_combination h_Af₂_eq
  -- A²f₂² = B²f₄²
  have h1 : A ^ 2 * f₂ z ^ 2 = B ^ 2 * f₄ z ^ 2 := by
    have h_sq : (A * f₂ z) ^ 2 = (B * f₄ z) ^ 2 := by rw [hAf₂]; ring
    calc A ^ 2 * f₂ z ^ 2 = (A * f₂ z) ^ 2 := by ring
      _ = (B * f₄ z) ^ 2 := h_sq
      _ = B ^ 2 * f₄ z ^ 2 := by ring
  -- A²f₂f₄ = -ABf₄²
  have h2 : A ^ 2 * (f₂ z * f₄ z) = -(A * B * f₄ z ^ 2) := by
    calc A ^ 2 * (f₂ z * f₄ z) = (A * f₂ z) * (A * f₄ z) := by ring
      _ = (-(B * f₄ z)) * (A * f₄ z) := by rw [hAf₂]
      _ = -(A * B * f₄ z ^ 2) := by ring
  -- A² - AB + B² = 3(H₂² + H₂H₄ + H₄²)
  have h_sum : A ^ 2 - A * B + B ^ 2 = 3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2) := by
    simp only [hA, hB]; ring
  -- Now compute A²θₕ
  unfold theta_h
  calc f₄ z ^ 2 * (3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2))
      = f₄ z ^ 2 * (A ^ 2 - A * B + B ^ 2) := by rw [h_sum]
    _ = B ^ 2 * f₄ z ^ 2 + (-(A * B * f₄ z ^ 2)) + A ^ 2 * f₄ z ^ 2 := by ring
    _ = A ^ 2 * f₂ z ^ 2 + A ^ 2 * (f₂ z * f₄ z) + A ^ 2 * f₄ z ^ 2 := by rw [h1, h2]
    _ = A ^ 2 * (f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) := by ring

/-- From g = 0 and h = 0, deduce f₂ = 0.

Proof: We have two equations:
1. g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ = 0
2. h = f₂² + f₂f₄ + f₄² = 0

From (1): f₄ = -((2H₂ + H₄)/(H₂ + 2H₄)) * f₂ (where H₂ + 2H₄ ≠ 0 generically)

Substituting into (2) and simplifying gives f₂² times a non-zero expression = 0.
Since holomorphic functions have isolated zeros or are identically zero,
and f₂ is holomorphic on all of ℍ, we get f₂ = 0.

Alternative approach: Use that 3(H₂² + H₂H₄ + H₄²) = 3E₄ (blueprint identity).
Then 3E₄ · h = 0 with E₄ having invertible q-series implies h-summand relations
that force f₂ = f₄ = 0. -/
lemma f₂_eq_zero : f₂ = 0 := by
  have hg := theta_g_eq_zero
  have hh := theta_h_eq_zero
  -- From g = 0 and h = 0, derive f₂ = 0
  -- Strategy: Show f₄ = 0, then f₂ = 0 follows from theta_h = f₂² = 0
  --
  -- Algebraic analysis:
  -- theta_g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ = 0
  -- theta_h = f₂² + f₂f₄ + f₄² = 0
  --
  -- Let A = 2H₂ + H₄ and B = H₂ + 2H₄.
  -- From theta_g = 0: Af₂ + Bf₄ = 0, so f₂ = -(B/A)f₄ where A ≠ 0.
  --
  -- Substituting into theta_h = 0:
  -- (B/A)²f₄² - (B/A)f₄² + f₄² = 0
  -- f₄²(B² - AB + A²)/A² = 0
  --
  -- Computation: A² - AB + B² = 3(H₂² + H₂H₄ + H₄²)
  -- At infinity: H₂ → 0, H₄ → 1, so A² - AB + B² → 3 ≠ 0
  -- Hence A² - AB + B² is not identically zero.
  --
  -- Since f₄² * (nonzero analytic) = 0, we must have f₄ = 0.
  -- Then from theta_h = f₂² = 0, we get f₂ = 0.
  --
  -- First show f₄ = 0:
  suffices hf₄ : f₄ = 0 by
    funext z
    have hz : theta_h z = 0 := congrFun hh z
    have hf₄z : f₄ z = 0 := congrFun hf₄ z
    simp only [theta_h, hf₄z, mul_zero, add_zero, Pi.zero_apply,
               zero_pow (by norm_num : 2 ≠ 0)] at hz ⊢
    exact sq_eq_zero_iff.mp hz
  -- Proof that f₄ = 0 using identity principle (mul_eq_zero_iff)
  -- ================================================================
  -- From theta_g = Af₂ + Bf₄ = 0 where A = 2H₂ + H₄, B = H₂ + 2H₄:
  --   A·f₂ = -B·f₄
  --
  -- Multiply theta_h = f₂² + f₂f₄ + f₄² by A²:
  --   A²θₕ = A²f₂² + A²f₂f₄ + A²f₄²
  --        = (Af₂)² + (Af₂)(Af₄) + A²f₄²
  --        = (Bf₄)² + (-Bf₄)(Af₄) + A²f₄²
  --        = f₄²(A² - AB + B²)
  --
  -- Compute: A² - AB + B² = 3(H₂² + H₂H₄ + H₄²)
  -- Since θₕ = 0: f₄² · 3(H₂² + H₂H₄ + H₄²) = 0
  -- At ∞: H₂ → 0, H₄ → 1, so H₂² + H₂H₄ + H₄² → 1 ≠ 0
  -- By mul_eq_zero_iff: f₄² = 0, hence f₄ = 0
  --
  -- From f₄_sq_mul_eq and theta_h = 0: f₄² * (3 * H_sum_sq) = 0 as functions
  have h_f₄_sq_3H : f₄ ^ 2 * (fun z => 3 * H_sum_sq z) = 0 := by
    ext z
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    have hg_z : theta_g z = 0 := congrFun hg z
    have hh_z : theta_h z = 0 := congrFun hh z
    calc f₄ z ^ 2 * (3 * H_sum_sq z)
        = (2 * H₂ z + H₄ z) ^ 2 * theta_h z := f₄_sq_mul_eq z hg_z
      _ = _ := by rw [hh_z, mul_zero]
  -- f₄² is MDifferentiable
  have f₄_sq_MDiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f₄ ^ 2) := by
    have heq : f₄ ^ 2 = f₄ * f₄ := by ext z; simp only [Pi.mul_apply, Pi.pow_apply, sq]
    rw [heq]; exact f₄_MDifferentiable.mul f₄_MDifferentiable
  -- Apply mul_eq_zero_iff: f₄² * (3 * H_sum_sq) = 0 → f₄² = 0 ∨ (3 * H_sum_sq) = 0
  have h_or : f₄ ^ 2 = 0 ∨ (fun z => 3 * H_sum_sq z) = 0 := by
    rw [← UpperHalfPlane.mul_eq_zero_iff f₄_sq_MDiff three_H_sum_sq_MDifferentiable]
    exact h_f₄_sq_3H
  -- Since 3 * H_sum_sq ≠ 0, we have f₄² = 0
  have h_f₄_sq_zero : f₄ ^ 2 = 0 := h_or.resolve_right three_H_sum_sq_ne_zero
  -- From f₄² = f₄ * f₄ = 0, by mul_eq_zero_iff: f₄ = 0
  have h_f₄_mul : f₄ * f₄ = 0 := by
    convert h_f₄_sq_zero using 1; ext z; exact (sq (f₄ z)).symm
  exact (UpperHalfPlane.mul_eq_zero_iff f₄_MDifferentiable f₄_MDifferentiable).mp h_f₄_mul
    |>.elim id id

/-- From f₂ = 0 and h = 0, deduce f₄ = 0 -/
lemma f₄_eq_zero : f₄ = 0 := by
  -- From h = f₂² + f₂f₄ + f₄² = 0 and f₂ = 0:
  -- f₄² = 0 → f₄ = 0
  have h_eq := theta_h_eq_zero
  have f₂_eq := f₂_eq_zero
  funext z
  -- theta_h z = f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2 = 0
  -- With f₂ z = 0, this gives f₄ z ^ 2 = 0
  have hz : theta_h z = 0 := congrFun h_eq z
  have hf₂z : f₂ z = 0 := congrFun f₂_eq z
  simp only [theta_h, hf₂z, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero, zero_add] at hz
  simp only [Pi.zero_apply]
  exact sq_eq_zero_iff.mp hz

/-- From f₂ + f₄ = f₃ and both = 0, f₃ = 0 -/
lemma f₃_eq_zero : f₃ = 0 := by
  rw [← f₂_add_f₄_eq_f₃]
  simp [f₂_eq_zero, f₄_eq_zero]

/-!
## Phase 10: Main Theorems
-/

/-- Serre derivative of H₂: ∂₂H₂ = (1/6)(H₂² + 2H₂H₄) -/
theorem serre_D_H₂ :
    serre_D 2 H₂ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 + 2 * H₂ z * H₄ z) := by
  funext z
  have := congrFun f₂_eq_zero z
  simp only [f₂, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.add_apply,
    smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  convert this using 1; ring

/-- Serre derivative of H₃: ∂₂H₃ = (1/6)(H₂² - H₄²) -/
theorem serre_D_H₃ : serre_D 2 H₃ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 - H₄ z ^ 2) := by
  funext z
  have := congrFun f₃_eq_zero z
  simp only [f₃, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply,
    smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- Serre derivative of H₄: ∂₂H₄ = -(1/6)(2H₂H₄ + H₄²) -/
theorem serre_D_H₄ :
    serre_D 2 H₄ = fun z => -(1/6 : ℂ) * (2 * H₂ z * H₄ z + H₄ z ^ 2) := by
  funext z
  have := congrFun f₄_eq_zero z
  simp only [f₄, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, Pi.zero_apply, add_eq_zero_iff_eq_neg] at this
  convert this using 1; ring
