/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-!
# The block gauge and the pointwise cost of an anti-symmetric perturbation

This module contains the pointwise matrix algebra behind the deterministic
localization lemma `l.localization.A` of the paper.

Write `s := symmPart a` and `k := skewPart a` for a coefficient matrix `a`, and
let `bfA(x)` be the block field of `e.bfA.def`, which is
`Homogenization.blockMatrixOfCoeff`. The manuscript's proof rests on the
factorization `e.bfG.factoring`

`bfA = G_{-k}^t (s 0 ; 0 s^{-1}) G_{-k}`,

with the triangular gauge matrix `G_h` of `e.G`, which is
`Homogenization.Book.Ch02.blockG`. Adding an anti-symmetric field `h` to `a`
leaves `s` unchanged and replaces `k` by `k + h`, so by the group law
`e.G.group` the block field of `a + h` is the `G_{-h}`-conjugate of the block
field of `a`, read in the gauge of `k`.

The quantity controlling the conjugation is `eta := s^{-1/2} h s^{-1/2}`, and
the manuscript's constant is `D = ‖eta‖_{L^infinity(U)} (1 + ‖eta‖_{L^infinity(U)})`.
The bound `‖eta‖ ≤ θ` is recorded here **without a matrix square root**, in its
equivalent two-vector form

`2 r · h p ≤ θ (p · s p + r · s r)` for all `p, r`,

which is exactly `2 v · eta u ≤ θ (|u|^2 + |v|^2)` after the substitution
`u = s^{1/2} p`, `v = s^{1/2} r`, hence exactly `‖eta‖ ≤ θ`. Everything below
is stated for that hypothesis, so no matrix square root ever appears.

## Main results

* `blockG_mul_blockG`: the group law `e.G.group`.
* `symmPart_add_of_skew`, `skewPart_add_of_skew`: an anti-symmetric shift moves
  only the anti-symmetric part.
* `blockQuadratic_add_skew_le`: the pointwise half of `l.localization.A`,
  `bfA(x; a + h) ≤ (1 + D) bfA(x; a)` as quadratic forms, `D = θ (1 + θ)`.
* `blockQuadratic_le_blockQuadratic_add_skew`: the reverse pointwise bound,
  obtained from the first with `a + h` as the base field and `-h` as the
  perturbation.
* `relSkewBound_of_symmPart_eq_smul_one`: for `s = nu Id` the hypothesis holds
  with `θ = nu⁻¹ M`, where `M` bounds the operator norm of `h`. This is the
  case the marginal paper uses at the infrared cutoffs.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## Pairing helpers for symmetric matrices -/

private theorem vecDot_matVecMul_comm_of_symm {S : Mat d} (hS : matTranspose S = S)
    (x y : Vec d) :
    vecDot x (matVecMul S y) = vecDot y (matVecMul S x) := by
  calc
    vecDot x (matVecMul S y) = vecDot x (matVecMul (matTranspose S) y) := by rw [hS]
    _ = vecDot (matVecMul S x) y := vecDot_matVecMul_transpose x y S
    _ = vecDot y (matVecMul S x) := vecDot_comm _ _

private theorem vecDot_sub_self_symm {S : Mat d} (hS : matTranspose S = S) (u v : Vec d) :
    vecDot (u - v) (matVecMul S (u - v)) =
      vecDot u (matVecMul S u) - 2 * vecDot u (matVecMul S v) +
        vecDot v (matVecMul S v) := by
  have hcross : vecDot v (matVecMul S u) = vecDot u (matVecMul S v) :=
    vecDot_matVecMul_comm_of_symm hS v u
  simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
    vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
  rw [hcross]
  ring

private theorem symmPart_inv_symm (A : Mat d) :
    matTranspose ((symmPart A)⁻¹) = (symmPart A)⁻¹ := by
  have h : Matrix.transpose ((symmPart A)⁻¹) = (Matrix.transpose (symmPart A))⁻¹ :=
    Matrix.transpose_nonsing_inv (symmPart A)
  have h2 : Matrix.transpose (symmPart A) = symmPart A := matTranspose_symmPart A
  rw [matTranspose, h, h2]

private theorem symmPart_mul_inv_vec {A : Mat d} {lam Lam : ℝ}
    (hA : IsEllipticMatrix lam Lam A) (v : Vec d) :
    matVecMul (symmPart A) (matVecMul ((symmPart A)⁻¹) v) = v := by
  have hunit : IsUnit (symmPart A).det :=
    (Matrix.isUnit_iff_isUnit_det (A := symmPart A)).mp
      (isUnit_symmPart_of_isEllipticMatrix hA)
  rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hunit, matVecMul_one]

/-- Only the symmetric part of a matrix is seen by its own quadratic form. -/
theorem vecDot_matVecMul_symmPart (A : Mat d) (p : Vec d) :
    vecDot p (matVecMul A p) = vecDot p (matVecMul (symmPart A) p) := by
  rw [matVecMul_eq_symmPart_add_skewPart A p, vecDot_add_right,
    vecDot_matVecMul_skewPart_self_eq_zero, add_zero]

/-! ## Anti-symmetric shifts and the gauge factorization -/

/-- An anti-symmetric shift does not change the symmetric part. -/
theorem symmPart_add_of_skew {A H : Mat d} (hH : matTranspose H = -H) :
    symmPart (A + H) = symmPart A := by
  ext i j
  have h : H j i = -H i j := congrFun (congrFun hH i) j
  simp only [symmPart, Matrix.add_apply, h]
  ring

/-- An anti-symmetric shift adds itself to the anti-symmetric part. -/
theorem skewPart_add_of_skew {A H : Mat d} (hH : matTranspose H = -H) :
    skewPart (A + H) = skewPart A + H := by
  ext i j
  have h : H j i = -H i j := congrFun (congrFun hH i) j
  simp only [skewPart, Matrix.add_apply, h]
  ring

/-- The group law `e.G.group` of the manuscript. -/
theorem blockG_mul_blockG (h₁ h₂ : Mat d) :
    blockMatMul (blockG h₁) (blockG h₂) = blockG (h₁ + h₂) := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> simp [blockMatMul, blockG]

/-! ## The pointwise cost of the perturbation -/

section Perturbation

variable {A H : Mat d} {lam Lam θ : ℝ}

/-- The Young bound `(h p) · s^{-1} (h p) ≤ θ^2 p · s p`, obtained from the
relative bound at the optimal test vector `r = θ⁻¹ s^{-1} h p`. -/
private theorem image_symmPartInv_le_of_relSkewBound
    (hA : IsEllipticMatrix lam Lam A) (hθ : 0 ≤ θ)
    (hbound : ∀ p r : Vec d,
      2 * vecDot r (matVecMul H p) ≤
        θ * (vecDot p (matVecMul (symmPart A) p) +
          vecDot r (matVecMul (symmPart A) r)))
    (p : Vec d) :
    vecDot (matVecMul H p) (matVecMul ((symmPart A)⁻¹) (matVecMul H p)) ≤
      θ ^ 2 * vecDot p (matVecMul (symmPart A) p) := by
  set B := vecDot p (matVecMul (symmPart A) p) with hB
  set z := matVecMul H p with hz
  set C := vecDot z (matVecMul ((symmPart A)⁻¹) z) with hC
  have hsInvSymm : matTranspose ((symmPart A)⁻¹) = (symmPart A)⁻¹ := symmPart_inv_symm A
  have hCnonneg : 0 ≤ C := symmPart_inv_nonneg_of_isEllipticMatrix hA z
  have hkey : ∀ t : ℝ, 2 * t * C ≤ θ * (B + t ^ 2 * C) := by
    intro t
    have h := hbound p (t • matVecMul ((symmPart A)⁻¹) z)
    have hleft : vecDot (t • matVecMul ((symmPart A)⁻¹) z) z = t * C := by
      rw [vecDot_smul_left, vecDot_comm,
        vecDot_matVecMul_comm_of_symm hsInvSymm z z]
    have hright :
        vecDot (t • matVecMul ((symmPart A)⁻¹) z)
            (matVecMul (symmPart A) (t • matVecMul ((symmPart A)⁻¹) z)) = t ^ 2 * C := by
      rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right,
        symmPart_mul_inv_vec hA z, vecDot_comm,
        vecDot_matVecMul_comm_of_symm hsInvSymm z z]
      ring
    rw [hleft, hright] at h
    linarith only [h]
  rcases eq_or_lt_of_le hθ with hθ0 | hθpos
  · have h := hkey 1
    rw [← hθ0] at h
    have hCle : C ≤ 0 := by linarith only [h]
    have hzero : θ ^ 2 * B = 0 := by rw [← hθ0]; ring
    linarith only [hCle, hzero, hCnonneg]
  · have h := hkey θ⁻¹
    have hinv : θ * (θ⁻¹) ^ 2 = θ⁻¹ := by field_simp
    rw [mul_add, ← mul_assoc, hinv] at h
    have h2 : θ⁻¹ * C ≤ θ * B := by linarith only [h]
    have h3 : θ * (θ⁻¹ * C) ≤ θ * (θ * B) :=
      mul_le_mul_of_nonneg_left h2 hθpos.le
    have h4 : θ * (θ⁻¹ * C) = C := by field_simp
    have h5 : θ * (θ * B) = θ ^ 2 * B := by ring
    rw [h4, h5] at h3
    exact h3

/-- The cross term of the perturbed Schur complement, bounded by the relative
bound at the test vector `r = -s^{-1} w`. -/
private theorem cross_le_of_relSkewBound
    (hA : IsEllipticMatrix lam Lam A)
    (hbound : ∀ p r : Vec d,
      2 * vecDot r (matVecMul H p) ≤
        θ * (vecDot p (matVecMul (symmPart A) p) +
          vecDot r (matVecMul (symmPart A) r)))
    (p w : Vec d) :
    -(2 * vecDot w (matVecMul ((symmPart A)⁻¹) (matVecMul H p))) ≤
      θ * (vecDot p (matVecMul (symmPart A) p) +
        vecDot w (matVecMul ((symmPart A)⁻¹) w)) := by
  have hsInvSymm : matTranspose ((symmPart A)⁻¹) = (symmPart A)⁻¹ := symmPart_inv_symm A
  have h := hbound p (-(matVecMul ((symmPart A)⁻¹) w))
  have hleft : vecDot (-(matVecMul ((symmPart A)⁻¹) w)) (matVecMul H p) =
      -(vecDot w (matVecMul ((symmPart A)⁻¹) (matVecMul H p))) := by
    rw [vecDot_neg_left, vecDot_comm,
      vecDot_matVecMul_comm_of_symm hsInvSymm (matVecMul H p) w]
  have hright : vecDot (-(matVecMul ((symmPart A)⁻¹) w))
      (matVecMul (symmPart A) (-(matVecMul ((symmPart A)⁻¹) w))) =
      vecDot w (matVecMul ((symmPart A)⁻¹) w) := by
    rw [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg,
      symmPart_mul_inv_vec hA w, vecDot_comm]
  rw [hleft, hright] at h
  linarith only [h]

/-- **Pointwise localization.** If `H` is anti-symmetric and its `symmPart A`
relative operator norm is at most `θ`, then the block coefficient matrix of
`A + H` is bounded by `(1 + θ (1 + θ))` times that of `A` in the quadratic-form
order.

This is the pointwise content of `e.ratio.fields`, with
`D = θ (1 + θ)`: the manuscript states it as a bound on
`‖bfA^{-1/2} hat{bfA} bfA^{-1/2} - I_{2d}‖`, transported to the perturbed
gauge through `e.bfG.doesnt.mess.up.ratios`. The variational, coarse-grained
display `e.localize.matrix.bounds.in.lemma` is its
consequence and is proved in
`SuperdiffusionCLT.Section2.Localization.BlockPerturbation`. -/
theorem blockQuadratic_add_skew_le
    (hA : IsEllipticMatrix lam Lam A) (hH : matTranspose H = -H) (hθ : 0 ≤ θ)
    (hbound : ∀ p r : Vec d,
      2 * vecDot r (matVecMul H p) ≤
        θ * (vecDot p (matVecMul (symmPart A) p) +
          vecDot r (matVecMul (symmPart A) r)))
    (Y : BlockVec d) :
    blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (A + H)) Y) ≤
      (1 + θ * (1 + θ)) *
        blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff A) Y) := by
  obtain ⟨p, q⟩ := Y
  have hsInvSymm : matTranspose ((symmPart A)⁻¹) = (symmPart A)⁻¹ := symmPart_inv_symm A
  have hQA : blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff A) (p, q)) =
      vecDot p (matVecMul (symmPart A) p) +
        vecDot (q - matVecMul (skewPart A) p)
          (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) :=
    blockMatrixOfCoeff_quadratic_eq A p q
  have hargeq : q - matVecMul (skewPart A + H) p =
      (q - matVecMul (skewPart A) p) - matVecMul H p := by
    rw [add_matVecMul]
    abel
  have hQAH : blockVecDot (p, q) (blockMatVecMul (blockMatrixOfCoeff (A + H)) (p, q)) =
      vecDot p (matVecMul (symmPart A) p) +
        vecDot ((q - matVecMul (skewPart A) p) - matVecMul H p)
          (matVecMul ((symmPart A)⁻¹)
            ((q - matVecMul (skewPart A) p) - matVecMul H p)) := by
    have h := blockMatrixOfCoeff_quadratic_eq (A + H) p q
    rw [symmPart_add_of_skew hH, skewPart_add_of_skew hH, hargeq] at h
    exact h
  rw [hQA, hQAH, vecDot_sub_self_symm hsInvSymm]
  have hW : 0 ≤ vecDot (q - matVecMul (skewPart A) p)
      (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) :=
    symmPart_inv_nonneg_of_isEllipticMatrix hA _
  have hM := cross_le_of_relSkewBound hA hbound p (q - matVecMul (skewPart A) p)
  have hC := image_symmPartInv_le_of_relSkewBound hA hθ hbound p
  have hsq : θ ^ 2 * vecDot p (matVecMul (symmPart A) p) ≤
      θ ^ 2 * (vecDot p (matVecMul (symmPart A) p) +
        vecDot (q - matVecMul (skewPart A) p)
          (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p))) := by
    have hθ2 : (0 : ℝ) ≤ θ ^ 2 := sq_nonneg θ
    have hle : vecDot p (matVecMul (symmPart A) p) ≤
        vecDot p (matVecMul (symmPart A) p) +
          vecDot (q - matVecMul (skewPart A) p)
            (matVecMul ((symmPart A)⁻¹) (q - matVecMul (skewPart A) p)) := by
      linarith only [hW]
    exact mul_le_mul_of_nonneg_left hle hθ2
  linarith only [hM, hC, hsq]

/-- The reverse pointwise bound, obtained from `blockQuadratic_add_skew_le`
with base field `A + H` and perturbation `-H`; the relative bound is unchanged
because `symmPart (A + H) = symmPart A`. -/
theorem blockQuadratic_le_blockQuadratic_add_skew
    (hAH : IsEllipticMatrix lam Lam (A + H)) (hH : matTranspose H = -H) (hθ : 0 ≤ θ)
    (hbound : ∀ p r : Vec d,
      2 * vecDot r (matVecMul H p) ≤
        θ * (vecDot p (matVecMul (symmPart A) p) +
          vecDot r (matVecMul (symmPart A) r)))
    (Y : BlockVec d) :
    blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff A) Y) ≤
      (1 + θ * (1 + θ)) *
        blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff (A + H)) Y) := by
  have hH' : matTranspose (-H) = -(-H) := by
    unfold matTranspose at hH ⊢
    rw [Matrix.transpose_neg, hH]
  have hsymAH : symmPart (A + H) = symmPart A := symmPart_add_of_skew hH
  have hbound' : ∀ p r : Vec d,
      2 * vecDot r (matVecMul (-H) p) ≤
        θ * (vecDot p (matVecMul (symmPart (A + H)) p) +
          vecDot r (matVecMul (symmPart (A + H)) r)) := by
    intro p r
    rw [hsymAH, neg_matVecMul, vecDot_neg_right]
    have hrr : vecDot (-r) (matVecMul (symmPart A) (-r)) =
        vecDot r (matVecMul (symmPart A) r) := by
      rw [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]
    have h := hbound p (-r)
    rw [vecDot_neg_left, hrr] at h
    linarith only [h]
  have hsum : A + H + -H = A := by abel
  have h := blockQuadratic_add_skew_le hAH hH' hθ hbound' Y
  rwa [hsum] at h

end Perturbation

/-! ## The scalar case `s = nu Id` -/

private theorem two_mul_le_of_sq_le {X M A B : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : X ^ 2 ≤ M ^ 2 * (A * B)) :
    2 * X ≤ M * (A + B) := by
  by_contra hcon
  push Not at hcon
  have hMnn : 0 ≤ M * (A + B) := by positivity
  have hsq : (M * (A + B)) ^ 2 < (2 * X) ^ 2 := by
    have h1 : M * (A + B) * (M * (A + B)) < 2 * X * (2 * X) :=
      mul_self_lt_mul_self hMnn hcon
    calc (M * (A + B)) ^ 2 = M * (A + B) * (M * (A + B)) := by ring
      _ < 2 * X * (2 * X) := h1
      _ = (2 * X) ^ 2 := by ring
  have hid : (M * (A + B)) ^ 2 = M ^ 2 * (A - B) ^ 2 + 4 * (M ^ 2 * (A * B)) := by ring
  have hnn : 0 ≤ M ^ 2 * (A - B) ^ 2 := by positivity
  have hX : (2 * X) ^ 2 = 4 * X ^ 2 := by ring
  linarith only [hsq, hid, hnn, hX, h]

private theorem matVecMul_smul_one (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- For a constant scalar symmetric part `s = nu Id`, an operator-norm bound
`M` for the anti-symmetric perturbation gives the relative bound with
`θ = nu⁻¹ M`. This is the marginal paper's cutoff situation,
where `nu` is the molecular diffusivity and `M = ‖k_ℓ - k_k‖_{L^infinity(U)}`. -/
theorem relSkewBound_of_symmPart_eq_smul_one {S H : Mat d} {ν M : ℝ}
    (hν : 0 < ν) (hM : 0 ≤ M) (hS : S = ν • (1 : Mat d))
    (hnorm : ∀ w : Vec d, vecNormSq (matVecMul H w) ≤ M ^ 2 * vecNormSq w)
    (p r : Vec d) :
    2 * vecDot r (matVecMul H p) ≤
      (ν⁻¹ * M) * (vecDot p (matVecMul S p) + vecDot r (matVecMul S r)) := by
  have hquad : ∀ w : Vec d, vecDot w (matVecMul S w) = ν * vecNormSq w := by
    intro w
    rw [hS, matVecMul_smul_one, vecDot_smul_right]
    rfl
  have hcs : (vecDot r (matVecMul H p)) ^ 2 ≤
      M ^ 2 * (vecNormSq p * vecNormSq r) := by
    have h1 : (vecDot r (matVecMul H p)) ^ 2 ≤
        vecNormSq r * vecNormSq (matVecMul H p) :=
      sq_vecDot_le_vecNormSq_mul_vecNormSq r (matVecMul H p)
    have h2 : vecNormSq r * vecNormSq (matVecMul H p) ≤
        vecNormSq r * (M ^ 2 * vecNormSq p) :=
      mul_le_mul_of_nonneg_left (hnorm p) (vecNormSq_nonneg r)
    have h3 : vecNormSq r * (M ^ 2 * vecNormSq p) =
        M ^ 2 * (vecNormSq p * vecNormSq r) := by ring
    linarith only [h1, h2, h3]
  have hyoung : 2 * vecDot r (matVecMul H p) ≤
      M * (vecNormSq p + vecNormSq r) :=
    two_mul_le_of_sq_le hM (vecNormSq_nonneg p) (vecNormSq_nonneg r) hcs
  have hrewrite : (ν⁻¹ * M) * (vecDot p (matVecMul S p) + vecDot r (matVecMul S r)) =
      M * (vecNormSq p + vecNormSq r) := by
    rw [hquad p, hquad r]
    field_simp
  rw [hrewrite]
  exact hyoung

end

end SuperdiffusionCLT.Section2.Localization
