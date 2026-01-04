import SpherePacking.ModularForms.JacobiTheta
import SpherePacking.ModularForms.Derivative
import SpherePacking.ModularForms.DimensionFormulas

/-!
# Theta Derivative Error Terms and Slash Actions

This file defines error terms for the Serre derivative identities of Jacobi theta functions
H₂, H₃, H₄ (Blueprint Proposition 6.52) and establishes their S/T transformation rules.

## Contents

* Error terms `f₂`, `f₃`, `f₄` definitions
* MDifferentiable proofs for error terms
* Jacobi identity: `f₂ + f₄ = f₃`
* S/T transformation rules: `f₂_S_action`, `f₂_T_action`, `f₄_S_action`, `f₄_T_action`

## Strategy

We define error terms f₂, f₃, f₄ = (LHS - RHS) and prove their transformation rules under
the S and T generators of SL(2,ℤ). The key results are:
- f₂|S = -f₄, f₂|T = -f₂
- f₄|S = -f₂, f₄|T = f₃

These transformation rules are used in subsequent files to construct level-1 invariants
and prove the error terms vanish.
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups

/-!
## Phase 1: Error Term Definitions
-/

/-- Error term for the ∂₂H₂ identity: f₂ = ∂₂H₂ - (1/6)(H₂² + 2H₂H₄) -/
noncomputable def f₂ : ℍ → ℂ :=
  serre_D 2 H₂ - (1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))

/-- Error term for the ∂₂H₃ identity: f₃ = ∂₂H₃ - (1/6)(H₂² - H₄²) -/
noncomputable def f₃ : ℍ → ℂ :=
  serre_D 2 H₃ - (1/6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2)

/-- Error term for the ∂₂H₄ identity: f₄ = ∂₂H₄ + (1/6)(2H₂H₄ + H₄²) -/
noncomputable def f₄ : ℍ → ℂ :=
  serre_D 2 H₄ + (1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))

/-- f₂ decomposes as serre_D 2 H₂ + (-1/6) • (H₂ * (H₂ + 2*H₄)) -/
lemma f₂_decompose :
    f₂ = serre_D (2 : ℤ) H₂ + ((-1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))) := by
  ext z; simp [f₂, sub_eq_add_neg]; ring

/-- f₄ decomposes as serre_D 2 H₄ + (1/6) • (H₄ * (2*H₂ + H₄)) -/
lemma f₄_decompose :
    f₄ = serre_D (2 : ℤ) H₄ + ((1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))) := by
  rfl

/-!
## Phase 2: MDifferentiable for Error Terms
-/

/-- f₂ is MDifferentiable -/
lemma f₂_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₂ := by
  simp only [f₂]
  exact (serre_D_differentiable H₂_SIF_MDifferentiable).sub
    ((H₂_SIF_MDifferentiable.mul (H₂_SIF_MDifferentiable.add
      (H₄_SIF_MDifferentiable.const_smul _))).const_smul _)

/-- f₃ is MDifferentiable -/
lemma f₃_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₃ := by
  simp only [f₃, sq]
  exact (serre_D_differentiable H₃_SIF_MDifferentiable).sub
    (((H₂_SIF_MDifferentiable.mul H₂_SIF_MDifferentiable).sub
      (H₄_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable)).const_smul _)

/-- f₄ is MDifferentiable -/
lemma f₄_MDifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₄ := by
  simp only [f₄]
  exact (serre_D_differentiable H₄_SIF_MDifferentiable).add
    ((H₄_SIF_MDifferentiable.mul
      ((H₂_SIF_MDifferentiable.const_smul _).add H₄_SIF_MDifferentiable)).const_smul _)

/-!
## Phase 3-4: Jacobi Identity and Relation f₂ + f₄ = f₃
-/

/-- Jacobi identity: H₂ + H₄ = H₃ -/
lemma jacobi_identity' (z : ℍ) : H₂ z + H₄ z = H₃ z := by simp [H₂, H₃, H₄, jacobi_identity z]

/-- The error terms satisfy f₂ + f₄ = f₃ (from Jacobi identity) -/
lemma f₂_add_f₄_eq_f₃ : f₂ + f₄ = f₃ := by
  ext z
  simp only [Pi.add_apply, f₂, f₃, f₄]
  -- Key relation: serre_D 2 H₂ z + serre_D 2 H₄ z = serre_D 2 H₃ z (via Jacobi identity)
  have h_serre : serre_D 2 H₂ z + serre_D 2 H₄ z = serre_D 2 H₃ z := by
    have add_eq := serre_D_add (2 : ℤ) H₂ H₄ H₂_SIF_MDifferentiable H₄_SIF_MDifferentiable
    have jacobi_eq : H₂ + H₄ = H₃ := by funext w; exact jacobi_identity' w
    have h := congrFun add_eq z
    simp only [Pi.add_apply] at h
    -- Use convert to handle the (2 : ℂ) vs ↑(2 : ℤ) issue
    convert h.symm using 2; rw [jacobi_eq]
  -- Now algebraic: use h_serre to simplify and close with ring
  have h_jacobi := jacobi_identity' z
  calc serre_D 2 H₂ z - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z)) +
       (serre_D 2 H₄ z + 1/6 * (H₄ z * (2 * H₂ z + H₄ z)))
      = (serre_D 2 H₂ z + serre_D 2 H₄ z) +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) -
         1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by ring
    _ = serre_D 2 H₃ z +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) -
         1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by rw [h_serre]
    _ = serre_D 2 H₃ z - 1/6 * (H₂ z ^ 2 - H₄ z ^ 2) := by ring

/-!
## Phase 5: S/T Transformation Rules for f₂, f₄

These transformations depend on `serre_D_slash_equivariant` (which has a sorry in Derivative.lean).
The proofs use:
- serre_D_slash_equivariant: (serre_D k F)|[k+2]γ = serre_D k (F|[k]γ)
- H₂_S_action: H₂|[2]S = -H₄
- H₄_S_action: H₄|[2]S = -H₂
- H₂_T_action: H₂|[2]T = -H₂
- H₃_T_action: H₃|[2]T = H₄
- H₄_T_action: H₄|[2]T = H₃

From these, we get:
- (serre_D 2 H₂)|[4]S = serre_D 2 (H₂|[2]S) = serre_D 2 (-H₄) = -serre_D 2 H₄
- Products transform multiplicatively: (H₂·G)|[4]S = (H₂|[2]S)·(G|[2]S)
-/

/-- f₂ transforms under S as f₂|S = -f₄.

Proof outline using serre_D_slash_equivariant:
1. (serre_D 2 H₂)|[4]S = serre_D 2 (H₂|[2]S) = serre_D 2 (-H₄) = -serre_D 2 H₄
2. (H₂(H₂ + 2H₄))|[4]S = (-H₄)((-H₄) + 2(-H₂)) = H₄(H₄ + 2H₂)
3. f₂|[4]S = -serre_D 2 H₄ - (1/6)H₄(H₄ + 2H₂) = -f₄

Key lemmas used:
- serre_D_slash_equivariant: (serre_D k F)|[k+2]γ = serre_D k (F|[k]γ)
- serre_D_smul: serre_D k (c • F) = c • serre_D k F (used for negation)
- mul_slash_SL2: (f * g)|[k1+k2]A = (f|[k1]A) * (g|[k2]A)
- SlashAction.add_slash, SL_smul_slash for linearity -/
lemma f₂_S_action : (f₂ ∣[(4 : ℤ)] S) = -f₄ := by
  -- Step 1: (serre_D 2 H₂)|[4]S = -serre_D 2 H₄ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₄ := by
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable S
    calc (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] S)
        = (serre_D (2 : ℤ) H₂ ∣[(2 + 2 : ℤ)] S) := by ring_nf
      _ = serre_D (2 : ℤ) (H₂ ∣[(2 : ℤ)] S) := h_equivariant
      _ = serre_D (2 : ℤ) (-H₄) := by rw [H₂_S_action]
      _ = -serre_D (2 : ℤ) H₄ := by
            have := serre_D_smul (2 : ℤ) (-1) H₄ H₄_SIF_MDifferentiable
            simp only [neg_one_smul] at this ⊢; exact this
  -- Step 2: (H₂ + 2•H₄)|[2]S = -(H₄ + 2•H₂)
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    rw [SlashAction.add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]S = H₄ * (H₄ + 2•H₂)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] S) = H₄ * (H₄ + (2 : ℂ) • H₂) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, mul_slash_SL2 2 2 S _ _, H₂_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]; ring
  -- Combine: f₂|[4]S = -serre_D 2 H₄ - (1/6) * H₄ * (2*H₂ + H₄) = -f₄
  rw [f₂_decompose, SlashAction.add_slash, SL_smul_slash, h_serre_term, h_prod]
  unfold f₄
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring_nf

/-- f₂ transforms under T as f₂|T = -f₂.

Proof outline:
1. (serre_D 2 H₂)|[4]T = serre_D 2 (H₂|[2]T) = serre_D 2 (-H₂) = -serre_D 2 H₂
2. (H₂(H₂ + 2H₄))|[4]T = (-H₂)((-H₂) + 2H₃)
   Using Jacobi H₃ = H₂ + H₄: -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
   So: (H₂(H₂ + 2H₄))|[4]T = (-H₂)(H₂ + 2H₄)
3. f₂|[4]T = -serre_D 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄)
           = -serre_D 2 H₂ + (1/6)H₂(H₂ + 2H₄)
           = -(serre_D 2 H₂ - (1/6)H₂(H₂ + 2H₄)) = -f₂ -/
lemma f₂_T_action : (f₂ ∣[(4 : ℤ)] T) = -f₂ := by
  -- Step 1: (serre_D 2 H₂)|[4]T = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] T) = -serre_D (2 : ℤ) H₂ := by
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable T
    calc (serre_D (2 : ℤ) H₂ ∣[(4 : ℤ)] T)
        = (serre_D (2 : ℤ) H₂ ∣[(2 + 2 : ℤ)] T) := by ring_nf
      _ = serre_D (2 : ℤ) (H₂ ∣[(2 : ℤ)] T) := h_equivariant
      _ = serre_D (2 : ℤ) (-H₂) := by rw [H₂_T_action]
      _ = -serre_D (2 : ℤ) H₂ := by
            have := serre_D_smul (2 : ℤ) (-1) H₂ H₂_SIF_MDifferentiable
            simp only [neg_one_smul] at this ⊢; exact this
  -- Step 2: (H₂ + 2•H₄)|[2]T = H₂ + 2•H₄ using Jacobi: H₃ = H₂ + H₄
  -- -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = H₂ + (2 : ℂ) • H₄ := by
    rw [SlashAction.add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    -- -H₂ z + 2 * H₃ z = H₂ z + 2 * H₄ z using Jacobi
    have h_jacobi := jacobi_identity' z
    rw [← h_jacobi]; ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]T = (-H₂) * (H₂ + 2•H₄)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] T) = -H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, mul_slash_SL2 2 2 T _ _, H₂_T_action, h_lin_comb]
  -- Combine: f₂|[4]T = -serre_D 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄) = -f₂
  rw [f₂_decompose, SlashAction.add_slash, SL_smul_slash, h_serre_term, h_prod]
  ext z
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- f₄ transforms under S as f₄|S = -f₂.

Proof outline (symmetric to f₂_S_action):
1. (serre_D 2 H₄)|[4]S = serre_D 2 (H₄|[2]S) = serre_D 2 (-H₂) = -serre_D 2 H₂
2. (H₄(2H₂ + H₄))|[4]S = (-H₂)(2(-H₄) + (-H₂)) = H₂(H₂ + 2H₄)
3. f₄|[4]S = -serre_D 2 H₂ + (1/6)H₂(H₂ + 2H₄) = -f₂ -/
lemma f₄_S_action : (f₄ ∣[(4 : ℤ)] S) = -f₂ := by
  -- Step 1: (serre_D 2 H₄)|[4]S = -serre_D 2 H₂ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] S) = -serre_D (2 : ℤ) H₂ := by
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable S
    calc (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] S)
        = (serre_D (2 : ℤ) H₄ ∣[(2 + 2 : ℤ)] S) := by ring_nf
      _ = serre_D (2 : ℤ) (H₄ ∣[(2 : ℤ)] S) := h_equivariant
      _ = serre_D (2 : ℤ) (-H₂) := by rw [H₄_S_action]
      _ = -serre_D (2 : ℤ) H₂ := by
            have := serre_D_smul (2 : ℤ) (-1) H₂ H₂_SIF_MDifferentiable
            simp only [neg_one_smul] at this ⊢; exact this
  -- Step 2: (2•H₂ + H₄)|[2]S = -(2•H₄ + H₂)
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) = -((2 : ℂ) • H₄ + H₂) := by
    rw [SlashAction.add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₄ * (2•H₂ + H₄))|[4]S = H₂ * (H₂ + 2•H₄)
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] S) = H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, mul_slash_SL2 2 2 S _ _, H₄_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]; ring
  -- Combine: f₄|[4]S = -serre_D 2 H₂ + (1/6) * H₂ * (H₂ + 2H₄) = -f₂
  rw [f₄_decompose, SlashAction.add_slash, SL_smul_slash, h_serre_term, h_prod]
  unfold f₂
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring_nf

/-- f₄ transforms under T as f₄|T = f₃.

Proof outline:
1. (serre_D 2 H₄)|[4]T = serre_D 2 (H₄|[2]T) = serre_D 2 H₃
2. (H₄(2H₂ + H₄))|[4]T = H₃(2(-H₂) + H₃) = H₃(H₃ - 2H₂)
   Using Jacobi H₃ = H₂ + H₄: H₃ - 2H₂ = H₄ - H₂
3. f₄|[4]T = serre_D 2 H₃ + (1/6)H₃(H₃ - 2H₂)
   But H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄)H₃
   So (1/6)(H₂² - H₄²) = -(1/6)H₃(H₄ - H₂) = -(1/6)H₃(H₃ - 2H₂)
   Thus f₃ = serre_D 2 H₃ - (1/6)(H₂² - H₄²) = f₄|[4]T -/
lemma f₄_T_action : (f₄ ∣[(4 : ℤ)] T) = f₃ := by
  -- Step 1: (serre_D 2 H₄)|[4]T = serre_D 2 H₃ (via equivariance)
  have h_serre_term : (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] T) = serre_D (2 : ℤ) H₃ := by
    have h_equivariant := serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable T
    calc (serre_D (2 : ℤ) H₄ ∣[(4 : ℤ)] T)
        = (serre_D (2 : ℤ) H₄ ∣[(2 + 2 : ℤ)] T) := by ring_nf
      _ = serre_D (2 : ℤ) (H₄ ∣[(2 : ℤ)] T) := h_equivariant
      _ = serre_D (2 : ℤ) H₃ := by rw [H₄_T_action]
  -- Step 2: (2•H₂ + H₄)|[2]T = H₄ - H₂ using Jacobi: H₃ = H₂ + H₄
  -- -2H₂ + H₃ = -2H₂ + (H₂ + H₄) = H₄ - H₂
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = H₄ - H₂ := by
    rw [SlashAction.add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
    have h_jacobi := jacobi_identity' z
    rw [← h_jacobi]; ring
  -- Step 3: Product (H₄ * (2•H₂ + H₄))|[4]T = H₃ * (H₄ - H₂)
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] T) = H₃ * (H₄ - H₂) := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, mul_slash_SL2 2 2 T _ _, H₄_T_action, h_lin_comb]
  -- Combine: f₄|[4]T = serre_D 2 H₃ + (1/6) * H₃ * (H₄ - H₂) = f₃
  rw [f₄_decompose, SlashAction.add_slash, SL_smul_slash, h_serre_term, h_prod]
  -- Now: serre_D 2 H₃ + (1/6) • H₃ * (H₄ - H₂) = f₃
  -- Key: H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄) * H₃
  unfold f₃
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  have h_jacobi := jacobi_identity' z
  -- Need: 1/6 * H₃ z * (H₄ z - H₂ z) = -1/6 * (H₂ z^2 - H₄ z^2)
  rw [sq_sub_sq, h_jacobi]
  ring_nf
