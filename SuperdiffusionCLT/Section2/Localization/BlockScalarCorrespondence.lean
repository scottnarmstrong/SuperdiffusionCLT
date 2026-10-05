/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.CoarseGraining.BlockFormalism.EllipticBounds
public import Homogenization.Book.Ch02.Block

/-!
# The pointwise block form at an adjoint pair of slopes

Step 2 of `ss.localization` compares the maximizers of two nearby scalar variational problems by
passing to the block formulation.  The passage rests on one algebraic identity,
printed as `e.iden.AP`: for a coefficient matrix `a` with
symmetric part `s` and every pair of vectors `e, e*`,

`(e + e*, a e - aᵗ e*) · 𝐀 (e + e*, a e - aᵗ e*) = 2 e · s e + 2 e* · s e*`,

where `𝐀` is the pointwise block matrix `e.bfA.def`.  The
manuscript asserts this display without proof, and no other step of the printed
argument supplies it, so it is proved here from the factorization
`Homogenization.blockMatrixOfCoeff_quadratic_eq`,

`(p, q) · 𝐀 (p, q) = p · s p + (q - k p) · s⁻¹ (q - k p)`,

together with the observation that the second slot of the adjoint pair is the
one that cancels the inverse: writing `a = s + k` and `aᵗ = s - k`,

`(a e - aᵗ e*) - k (e + e*) = s (e - e*)`,

so the second summand is exactly `(e - e*) · s (e - e*)` and the parallelogram
law finishes the identity.  Only invertibility of `s` is used, which is the
print's standing uniform ellipticity on `U`.

The statements are pointwise in `x`; the manuscript's displays are their averages over `U`.
Nothing here is a statement about maximizers.

## Main results

* `blockVecDot_blockMatrixOfCoeff_adjointPair`: `e.iden.AP`.
* `blockVecDot_blockMatrixOfCoeff_nonneg`: the pointwise block form is
  nonnegative under ellipticity.
* `blockVecDot_blockMatrixOfCoeff_add_le`: the two-term Cauchy inequality for
  the pointwise block form, the triangle inequality of `e.minimizers.gradient.from.block`.
* `vecDot_symmPart_eq_mul_vecNormSq`: at a coefficient whose symmetric part is `ν Id`, the
  `s`-energy of a slope is `ν` times its squared norm.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## The symmetric and skew parts of a coefficient matrix -/

/-- `a = s + k`: a matrix is the sum of its symmetric and skew parts. -/
private theorem symmPart_add_skewPart (A : Mat d) : symmPart A + skewPart A = A := by
  ext i j
  simp only [Matrix.add_apply, symmPart, skewPart]
  ring

/-- `aᵗ = s - k`: the transpose is the difference of the symmetric and skew
parts. -/
private theorem symmPart_sub_skewPart (A : Mat d) :
    symmPart A - skewPart A = matTranspose A := by
  ext i j
  simp only [Matrix.sub_apply, symmPart, skewPart, matTranspose, Matrix.transpose_apply]
  ring

/-- The symmetric part is self-adjoint for the Euclidean pairing. -/
private theorem vecDot_symmPart_comm (A : Mat d) (x y : Vec d) :
    vecDot x (matVecMul (symmPart A) y) = vecDot y (matVecMul (symmPart A) x) := by
  have h := vecDot_matVecMul_transpose x y (symmPart A)
  rw [matTranspose_symmPart] at h
  rw [h]
  exact vecDot_comm _ _

/-- The inverse of the symmetric part is symmetric. -/
private theorem matTranspose_inv_symmPart (A : Mat d) :
    matTranspose ((symmPart A)⁻¹) = (symmPart A)⁻¹ := by
  show Matrix.transpose ((symmPart A)⁻¹) = (symmPart A)⁻¹
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  exact matTranspose_symmPart A

/-- `s⁻¹` inverts `s` on vectors when `s` is invertible. -/
private theorem matVecMul_inv_symmPart (A : Mat d) (hA : IsUnit (symmPart A).det)
    (x : Vec d) :
    matVecMul ((symmPart A)⁻¹) (matVecMul (symmPart A) x) = x := by
  rw [matVecMul_mul, Matrix.nonsing_inv_mul _ hA]
  funext i
  simp [matVecMul, Matrix.one_apply]

/-! ## `e.iden.AP`

The adjoint pair `(e + e*, a e - aᵗ e*)` and the value of
the pointwise block form on it. -/

/-- `a x = s x + k x` on vectors. -/
private theorem matVecMul_eq_symmPart_add_skewPart (A : Mat d) (x : Vec d) :
    matVecMul A x = matVecMul (symmPart A) x + matVecMul (skewPart A) x := by
  rw [← add_matVecMul, symmPart_add_skewPart]

/-- `aᵗ x = s x - k x` on vectors. -/
private theorem matVecMul_transpose_eq_symmPart_sub_skewPart (A : Mat d) (x : Vec d) :
    matVecMul (matTranspose A) x =
      matVecMul (symmPart A) x - matVecMul (skewPart A) x := by
  rw [← sub_matVecMul, symmPart_sub_skewPart]

/-- The flux slot of the adjoint pair, corrected by the skew part, is the
symmetric part applied to the difference of the two slopes:

`(a e - aᵗ e*) - k (e + e*) = s (e - e*)`.

This is the cancellation that makes `e.iden.AP` true. -/
private theorem adjointPair_flux_sub_skewPart (A : Mat d) (e f : Vec d) :
    matVecMul A e - matVecMul (matTranspose A) f - matVecMul (skewPart A) (e + f) =
      matVecMul (symmPart A) (e - f) := by
  have hA := matVecMul_eq_symmPart_add_skewPart A e
  have hAt := matVecMul_transpose_eq_symmPart_sub_skewPart A f
  have hk : matVecMul (skewPart A) (e + f) =
      matVecMul (skewPart A) e + matVecMul (skewPart A) f := matVecMul_add _ _ _
  have hs : matVecMul (symmPart A) (e - f) =
      matVecMul (symmPart A) e - matVecMul (symmPart A) f := by
    rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]
  rw [hA, hAt, hk, hs]
  abel

/-- **`e.iden.AP`**: the pointwise block form of a coefficient
matrix `a`, evaluated at the adjoint pair `(e + e*, a e - aᵗ e*)` built from
two slopes, is twice the sum of the two `s`-energies,

`(e + e*, a e - aᵗ e*) · 𝐀 (e + e*, a e - aᵗ e*) = 2 e · s e + 2 e* · s e*`.

The manuscript states this display without proof; only invertibility of the
symmetric part is needed. -/
theorem blockVecDot_blockMatrixOfCoeff_adjointPair (A : Mat d)
    (hA : IsUnit (symmPart A).det) (e f : Vec d) :
    blockVecDot (e + f, matVecMul A e - matVecMul (matTranspose A) f)
        (blockMatVecMul (blockMatrixOfCoeff A)
          (e + f, matVecMul A e - matVecMul (matTranspose A) f)) =
      2 * vecDot e (matVecMul (symmPart A) e) +
        2 * vecDot f (matVecMul (symmPart A) f) := by
  rw [blockMatrixOfCoeff_quadratic_eq, adjointPair_flux_sub_skewPart,
    matVecMul_inv_symmPart A hA, vecDot_comm (matVecMul (symmPart A) (e - f)) (e - f)]
  have hcomm := vecDot_symmPart_comm A e f
  simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
    vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
  linarith only [hcomm]

/-! ## The triangle inequality of `e.minimizers.gradient.from.block`

The proof applies `e.iden.AP` to `Z - Z̃₀` and then splits `Z - Z̃₀` as
`(Z - Z̃) + Z̃₁`.  The splitting step is the two-term Cauchy inequality for the
pointwise block form, which needs only that the form is a nonnegative
symmetric quadratic form. -/

/-- The two-term Cauchy inequality for a symmetric nonnegative quadratic form
on `Vec d`. -/
private theorem vecDot_add_le_of_symm_nonneg {M : Mat d}
    (hM : matTranspose M = M) (hpos : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul M x))
    (x y : Vec d) :
    vecDot (x + y) (matVecMul M (x + y)) ≤
      2 * vecDot x (matVecMul M x) + 2 * vecDot y (matVecMul M y) := by
  have hcomm : vecDot y (matVecMul M x) = vecDot x (matVecMul M y) := by
    have h := vecDot_matVecMul_transpose y x M
    rw [hM] at h
    rw [h]
    exact vecDot_comm _ _
  have hsub := hpos (x - y)
  simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
    vecDot_add_right, vecDot_neg_left, vecDot_neg_right] at hsub
  simp only [matVecMul_add, vecDot_add_left, vecDot_add_right]
  linarith only [hsub, hcomm]

/-- The `s`-energy of a slope is nonnegative under ellipticity. -/
private theorem vecDot_symmPart_nonneg {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (x : Vec d) :
    0 ≤ vecDot x (matVecMul (symmPart A) x) := by
  have hlower := lowerBound_symmPart_of_isEllipticMatrix hA x
  have hlam : 0 < lam := hA.1
  have hnn : 0 ≤ lam * vecNormSq x := mul_nonneg hlam.le (vecNormSq_nonneg x)
  linarith only [hlower, hnn]

/-- The pointwise block form of an elliptic coefficient matrix is
nonnegative. -/
theorem blockVecDot_blockMatrixOfCoeff_nonneg {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) := by
  obtain ⟨p, q⟩ := X
  rw [blockMatrixOfCoeff_quadratic_eq]
  have h1 := vecDot_symmPart_nonneg hA p
  have h2 := symmPart_inv_nonneg_of_isEllipticMatrix hA (q - matVecMul (skewPart A) p)
  linarith only [h1, h2]

/-- The two-term Cauchy inequality for the pointwise block form, the triangle
inequality used there. -/
theorem blockVecDot_blockMatrixOfCoeff_add_le {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (X Y : BlockVec d) :
    blockVecDot (X + Y) (blockMatVecMul (blockMatrixOfCoeff A) (X + Y)) ≤
      2 * blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) +
        2 * blockVecDot Y (blockMatVecMul (blockMatrixOfCoeff A) Y) := by
  obtain ⟨p₁, q₁⟩ := X
  obtain ⟨p₂, q₂⟩ := Y
  have hadd : ((p₁, q₁) + (p₂, q₂) : BlockVec d) = (p₁ + p₂, q₁ + q₂) := rfl
  rw [hadd, blockMatrixOfCoeff_quadratic_eq, blockMatrixOfCoeff_quadratic_eq,
    blockMatrixOfCoeff_quadratic_eq]
  have hr : q₁ + q₂ - matVecMul (skewPart A) (p₁ + p₂) =
      (q₁ - matVecMul (skewPart A) p₁) + (q₂ - matVecMul (skewPart A) p₂) := by
    rw [matVecMul_add]
    abel
  rw [hr]
  have h1 := vecDot_add_le_of_symm_nonneg (matTranspose_symmPart A)
    (fun x => vecDot_symmPart_nonneg hA x) p₁ p₂
  have h2 := vecDot_add_le_of_symm_nonneg (matTranspose_inv_symmPart A)
    (fun x => symmPart_inv_nonneg_of_isEllipticMatrix hA x)
    (q₁ - matVecMul (skewPart A) p₁) (q₂ - matVecMul (skewPart A) p₂)
  linarith only [h1, h2]

/-! ## The slope pair of a block vector

The proof writes the block variable `Z` of the doubled minimization
problem as `Z = ½ (∇u + ∇u*, a ∇u - aᵗ ∇u*)` for the scalar maximizer `u` and
its adjoint partner `u*`.  Both gradients are recovered from `Z` alone: the
upstream extraction theorem
`Homogenization.Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient`
reads `∇u` off a doubled minimizer `Z` as `Z.1 + (𝐀 Z).2`, and the print's
representation then forces `∇u* = Z.1 - (𝐀 Z).2`.  What is recorded here is the
algebra of that pair: for *any* `w` whose `s`-image is the skew-corrected flux
slot `q - k p`, the adjoint pair of `p + w` and `p - w` is `2 (p, q)`.  The
block-form value at `(p, q)` is then half the sum of the two `s`-energies,
which is the pointwise form of `e.minimizers.energy.vs.bfA`. -/

/-! ## The specialization `s = ν Id`

The print applies the deterministic comparison with `a = a_m`, whose symmetric
part is `ν Id`, and then divides by `ν`.  At that
specialization every `s`-energy above is `ν` times a squared Euclidean
norm, which is the quantity the clause `e.localization.minimizers`
averages. -/

/-- The identity `1 x = x` on vectors. -/
private theorem matVecMul_one_vec (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply]

/-- At a coefficient whose symmetric part is `ν Id`, the `s`-energy of a slope
is `ν` times its squared Euclidean norm. -/
theorem vecDot_symmPart_eq_mul_vecNormSq {A : Mat d} {nu : ℝ}
    (hs : symmPart A = nu • (1 : Mat d)) (x : Vec d) :
    vecDot x (matVecMul (symmPart A) x) = nu * vecNormSq x := by
  rw [hs, smul_matVecMul, matVecMul_one_vec, vecDot_smul_right]
  rfl

end

end SuperdiffusionCLT.Section2.Localization
