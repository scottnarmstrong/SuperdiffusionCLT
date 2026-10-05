/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BellUpscaleBoundRemainder
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Inputs
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks
public import SuperdiffusionCLT.Section2.Localization.UnsymmetricConversion

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Section2.Localization
open scoped ENNReal
open scoped MatrixOrder

/-!
# The printed inputs of `e.blupbounds` at the genuine coarse carriers

The deterministic core `blupbounds_operatorNorm_le`
(`BellUpscaleBoundRemainder.lean`) consumes four
printed relations between its free block binders: the Gram property `hSqrt` of
the printed square root `σ_{m,*}^{-1/2}(U)`, the symmetry `hSym` of
the upper-left block difference `(b_ℓ − b_m)(U)`, the
Cauchy-Schwarz input `hKappaB` and the block form `hAM` (`e.bigA.def`).  This
module supplies the first two at the genuine coarse carriers on the translated cubes,
in the exact shapes the instantiation of `blupbounds_operatorNorm_le` consumes.

* **The Gram square root.**  The printed square root `σ_{m,*}^{-1/2}(U)` is the
  positive square root `CFC.sqrt (σ_{m,*}^{-1}(U))` of the
  continuous functional calculus, and the printed Gram property
  `σ_{m,*}^{-1/2}(U)ᵗ σ_{m,*}^{-1/2}(U) = σ_{m,*}^{-1}(U)` is the
  `posSemidef_sqrt_mul_self` identity there: the coarse matrix
  `σ_{*}^{-1}` on a triadic cube is positive semidefinite
  (`posSemidef_sigmaStarInvCoarse_cutoffCube`, in `RHSTerm3Inputs.lean`),
  the square root of a positive-semidefinite block is symmetric
  (`posSemidef_sqrt_isSymm`, in `PsdSqrtQuadratic.lean`) and
  its square is the matrix.  `gramSqrt_sigmaStarInvCoarse_cutoffCube` is the
  instantiation, with the transpose read through the symmetry of the square
  root; the `∀ omega` corollary is the `hSqrt` slot of `blupbounds_operatorNorm_le`
  verbatim at the carrier
  `sigmaStarInvHalfU omega := CFC.sqrt (σ_{m,*}^{-1}(z + cu_m))`.

* **The symmetry of the block difference.**  The printed fact that the upper-left
  block of `bfA_ℓ(U) − bfA_m(U)` is the
  *symmetric* matrix `(b_ℓ − b_m)(U)`: each coarse block
  `b_L(z + cu_n)` is positive semidefinite
  (`posSemidef_translatedCoarseBlock`, in `TranslatedBlocks.lean`),
  and `Matrix.PosSemidef` carries the self-adjointness, so both blocks are
  symmetric and so is their difference (`Matrix.IsSymm.sub`).  The doubled
  block matrix `bfA_L(z + cu_n)` is symmetric as well
  (`Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix`), which gives the same
  statement at the level of the doubled blocks, for the two scales separately
  and for the difference of the two carriers.
-/

namespace SuperdiffusionCLT.Section3.Terms

variable {d : ℕ}

noncomputable section

/-! ## The Gram square root of `σ_{*,}^{-1}` on a triadic cube -/

/-- The transpose of a symmetric block matrix is the matrix itself: this is
`Matrix.IsSymm.eq` read through the `matTranspose` carrier. -/
theorem matTranspose_eq_self_of_isSymm {A : Mat d} (hA : A.IsSymm) :
    matTranspose A = A := by
  show Matrix.transpose A = A
  exact hA.eq

/-- **The Gram property `hSqrt` of `e.blupbounds` at the
carrier.**  The printed square root `σ_{*,}^{-1/2}(z + cu_m)` of the coarse
matrix `σ_{*}^{-1}(z + cu_m)` on a triadic cube is its positive square root
`CFC.sqrt (σ_{*}^{-1}(z + cu_m))`, and it satisfies the printed Gram property

`σ_{*,}^{-1/2}(z + cu_m)ᵗ σ_{*,}^{-1/2}(z + cu_m) = σ_{*,}^{-1}(z + cu_m)`.

The coarse matrix `σ_{*}^{-1}(z + cu_m)` is positive semidefinite
(`posSemidef_sigmaStarInvCoarse_cutoffCube`), the square root of a
positive-semidefinite block is symmetric (`posSemidef_sqrt_isSymm`), so the
transpose of the square root is the square root, and its square is the matrix
(`posSemidef_sqrt_mul_self`). -/
theorem gramSqrt_sigmaStarInvCoarse_cutoffCube [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (Q : TriadicCube d) :
    matTranspose (CFC.sqrt (sigmaStarInvCoarse (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField)) *
      CFC.sqrt (sigmaStarInvCoarse (cubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField) =
      sigmaStarInvCoarse (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField := by
  rw [matTranspose_eq_self_of_isSymm
    (posSemidef_sqrt_isSymm (sigmaStarInvCoarse (cubeSet Q)
      (coefficientCutoff nu omega L).toCoeffField))]
  exact posSemidef_sqrt_mul_self
    (posSemidef_sigmaStarInvCoarse_cutoffCube hnu L omega Q)

/-- The Gram property in the shape of the `hSqrt` binder of `blupbounds_operatorNorm_le`
(`Section3/Terms/BellUpscaleBoundRemainder.lean`): quantified over the shell sequence
and the cube, at the carrier
`sigmaStarInvHalfU omega := CFC.sqrt (σ_{*,}^{-1}(z + cu_m))` and the coarse
matrix `sigmaStarInvU omega := σ_{*,}^{-1}(z + cu_m)`. -/
theorem gramSqrt_sigmaStarInvCoarse_cutoffCube_forall [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) :
    ∀ omega : ShellSeq d, ∀ Q : TriadicCube d,
      matTranspose (CFC.sqrt (sigmaStarInvCoarse (cubeSet Q)
            (coefficientCutoff nu omega L).toCoeffField)) *
        CFC.sqrt (sigmaStarInvCoarse (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField) =
        sigmaStarInvCoarse (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField :=
  fun omega Q => gramSqrt_sigmaStarInvCoarse_cutoffCube hnu L omega Q

/-! ## The symmetry of the coarse block and of the block difference -/

/-- The coarse block `b_L(z + cu_n)` is symmetric: it is positive semidefinite
(`posSemidef_translatedCoarseBlock`) and `Matrix.PosSemidef` carries the
self-adjointness, which for real matrices is symmetry
(`posSemidef_isSymm` of `Section2/Localization/UnsymmetricConversion.lean`). -/
theorem isSymm_translatedCoarseBlock [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    (translatedCoarseBlock nu L omega z).IsSymm :=
  posSemidef_isSymm (posSemidef_translatedCoarseBlock hnu L omega z)

/-- **The symmetry `hSym` of `e.blupbounds` at the
carriers**: the upper-left block difference of the two coarse blocks on the
translated cube, `(b_ℓ − b_m)(z + cu_n)`, is a symmetric matrix.  Each block is
symmetric, so the difference is (`Matrix.IsSymm.sub`). -/
theorem isSymm_sub_translatedCoarseBlock [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L M : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    (translatedCoarseBlock nu L omega z -
      translatedCoarseBlock nu M omega z).IsSymm :=
  (isSymm_translatedCoarseBlock hnu L omega z).sub
    (isSymm_translatedCoarseBlock hnu M omega z)

/-! ## The upper-left block bound `hKappaB` of `e.blupbounds` -/

private theorem matVecMul_add_mat_self {A B : Mat d} (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  funext i
  simp only [matVecMul, Matrix.add_apply, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-! ### The Cauchy-Schwarz input `hKappaB` of `e.blupbounds` -/

/-- **The Cauchy-Schwarz input `hKappaB` of `e.blupbounds`** (in the proof of
`l.blupbounds`): in the block form `e.bigA.def` the upper-left block satisfies

`κᵗ σ_{*}^{-1} κ ≤ b`, tested as
`|σ_{*}^{-1/2} (κ e)|² ≤ e · b(U) e` on the unit slice `|e| = 1`.

The proof is the printed one: the quadratic form of
`b = σ + κᵗ σ_{*}^{-1} κ` splits as the quadratic form of `σ` plus the
quadratic form of `κᵗ σ_{*}^{-1} κ`, and the latter is the squared norm of the
square root applied to `κ e`, by the Gram property of the square root
(`vecNormSq (σ^{-1/2} (κ e)) = (κ e) · σ_{*}^{-1} (κ e)`).  The quadratic form
of `σ` is nonnegative, so it can be dropped. -/
theorem kappaUpperLeft_quadratic_le {sigma sigmaStarInv kappa bM : Mat d}
    (hB : bM = sigma + matTranspose kappa * sigmaStarInv * kappa)
    (hsigma : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul sigma v))
    (hsqrt : ∀ v : Vec d,
      vecNormSq (matVecMul (CFC.sqrt sigmaStarInv) v) =
        vecDot v (matVecMul sigmaStarInv v))
    (e : Vec d) :
    vecNormSq (matVecMul (CFC.sqrt sigmaStarInv) (matVecMul kappa e)) ≤
      vecDot e (matVecMul bM e) := by
  have hquad : vecDot e (matVecMul (matTranspose kappa * sigmaStarInv * kappa) e)
      = vecDot (matVecMul kappa e) (matVecMul sigmaStarInv (matVecMul kappa e)) := by
    rw [← matVecMul_mul (matTranspose kappa * sigmaStarInv) kappa e,
      ← matVecMul_mul (matTranspose kappa) sigmaStarInv (matVecMul kappa e)]
    exact vecDot_matVecMul_transpose e (matVecMul sigmaStarInv (matVecMul kappa e)) kappa
  have hadd : vecDot e (matVecMul (sigma + matTranspose kappa * sigmaStarInv * kappa) e)
      = vecDot e (matVecMul sigma e)
        + vecDot e (matVecMul (matTranspose kappa * sigmaStarInv * kappa) e) := by
    rw [matVecMul_add_mat_self, vecDot_add_right]
  calc vecNormSq (matVecMul (CFC.sqrt sigmaStarInv) (matVecMul kappa e))
      = vecDot (matVecMul kappa e) (matVecMul sigmaStarInv (matVecMul kappa e)) :=
        hsqrt (matVecMul kappa e)
    _ = vecDot e (matVecMul (matTranspose kappa * sigmaStarInv * kappa) e) := hquad.symm
    _ ≤ vecDot e (matVecMul (sigma + matTranspose kappa * sigmaStarInv * kappa) e) := by
        rw [hadd]
        linarith only [hsigma e]
    _ = vecDot e (matVecMul bM e) := by rw [hB]

/-- **`hKappaB` at the Chapter 2 coarse carriers** (`e.bigA.def`): the canonical
coupling matrix `κ(U; a)`, the canonical `s_*^{-1}(U; a)` with its positive square
root, and the canonical derived matrix `b(U; a) = σ + κᵗ σ_*^{-1} κ` satisfy, for every
direction `e`,

`|σ_*^{-1/2}(U; a) (κ(U; a) e)|² ≤ e · b(U; a) e`.

The quadratic form of `σ(U; a)` is nonnegative because the order chain
`σ_*(U) ≤ σ(U) ≤ b(U)` (`e.cg.bounds.basic.definitions`) and the positivity of
`σ_*(U)` make `σ(U)` positive semidefinite. -/
theorem kappaUpperLeft_quadratic_le_bCoarse (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (e : Vec d) :
    vecNormSq (matVecMul (CFC.sqrt (Book.Ch02.sigmaStarInvCoarse U a))
        (matVecMul (Book.Ch02.kappaCoarse U a) e)) ≤
      vecDot e (matVecMul (Book.Ch02.bCoarse U a) e) := by
  have hsigma : ∀ v : Vec d, 0 ≤
      vecDot v (matVecMul (Book.Ch02.sigmaCoarse U a) v) := by
    intro v
    have h1 := posSemidef_quadratic_nonneg
      (Book.Ch02.sigmaStarCoarse_posDef U a).posSemidef v
    have h2 := Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U a v
    linarith only [h1, h2]
  exact kappaUpperLeft_quadratic_le rfl hsigma
    (vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul
      (Book.Ch02.sigmaStarInvCoarse_posDef U a).posSemidef) e

end

end SuperdiffusionCLT.Section3.Terms