/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup
public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section3.Terms.BellUpscaleBound
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.Book.Ch02.Matrices

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

/-!
# The bell-upscale operator bound, corrected rendering (`l.blupbounds`, v2)

This module is the corrected successor of `BellUpscaleBound.lean`, whose remainder hypothesis
was quantified over *all* block vectors `Y` with a `Y`-independent bound; by homogeneity of the
block quadratic form this forces the quadratic form of `bL - bM` to vanish, hence `bL = bM`.

Two repairs are made here.

1. **The remainder is pinned on the unit slice.**  The hypothesis `hRemainder`
   quantifies over the unit-gradient slice only:
   `P = (e, 0)` with `|e| = 1` (`vecNormSq e = 1`), as in the paper's proof
   ("for `P = (e, 0)` with `|e| = 1`").  This is not vacuous: it is precisely
   the quadratic-form content of the final step of the proof, the supremum
   over `|e| = 1`, and a quadratic form bounded on the unit
   sphere by `Z omega` has operator norm at most `Z omega` by the bridge
   `matrixOperatorNorm_le_of_abs_quadratic_form_le` (with a symmetry
   hypothesis on `bL - bM`, which is load-bearing and sharp).

2. **The print's transposes.**  The remainder display carries the transposes
   of the paper's localized error display `e.blupbounds.localized.error`: the
   conjugation is `G_{-h}^t (G_h^t bfA_ell(U) G_h) G_{-h}`, not
   `G_{-h} (G_h bfA_ell G_h) G_{-h}`.  The transpose
   `blockGT h = [[1, h^t], [0, 1]]` of the gauge block
   `blockG h = [[1, 0], [h, 1]]` (`e.G`) is defined here, and the block pairing
   satisfies the transpose identity `blockVecDot_blockGT_transpose`:
   `X · blockGT(h) Y = blockG(h) X · Y`.

## A reading note on the printed remainder and the Young step

The remainder display is

`| (e,0) · G_{-h_U}^t (G_{h_U}^t bfA_ell(U) G_{h_U}) G_{-h_U} (e,0)
   − (e,0) · bfA_m(U) (e,0) | ≤ Z`,

with the `bfA_m(U)` term standing *outside* the conjugation.  The conjugated
factor cancels completely — `G_{-h}^t G_h^t = (G_h G_{-h})^t = I` and
`G_h G_{-h} = I` (`blockG_mul_neg`) — so the display bounds
`| e · (b_ell - b_m)(U) e |` itself, which is exactly what the last step of
the paper's proof ("taking the supremum over `|e| = 1`")
consumes.  Consequently the Young step
`l.blupbounds#young-cross-term` — which is needed when the
conjugation carries `bfA_m(U)` *inside*, as in the true remainder display
`e.blupbounds.remainder`, where it produces the cross term
`2 e · h_U^t sigma_{m,*}^{-1}(U) kappa_m(U) e` Young-controlled by the printed
weights `epsilon` and `epsilon^{-1}` — is not needed for this statement: after
the operator-norm passage, the printed `epsilon |b_m(U)|` and
`(1 + epsilon^{-1}) |sigma_{m,*}^{-1/2}(U) h_U|^2` terms of the conclusion are
nonnegative summands.  The Young route is proved in the predecessor module
(`young_cross_term`) and remains available
for the display of the proof that carries `bfA_m(U)` inside.
-/

namespace SuperdiffusionCLT.Section3.Terms

variable {d : ℕ}

/-! ### Private block algebra (associativity and unit laws of `blockMatMul`)-/

/-! ### Private scalar vector algebra -/

private theorem matVecMul_one_mat (y : Vec d) : matVecMul (1 : Mat d) y = y := by
  funext i
  simp [matVecMul, Matrix.one_apply]

private theorem matVecMul_zero_mat (y : Vec d) : matVecMul (0 : Mat d) y = 0 := by
  funext i
  simp [matVecMul, Matrix.zero_apply]

private theorem vecDot_transpose_matVecMul (x y : Vec d) (A : Mat d) :
    vecDot x (matVecMul (Matrix.transpose A) y) = vecDot (matVecMul A x) y :=
  vecDot_matVecMul_transpose x y A

/-! ### The transposed gauge block (`e.G`) -/

/-- The transpose of the gauge block matrix `blockG h = [[1, 0], [h, 1]]`:
`blockGT h = [[1, hᵀ], [0, 1]]`, so that `blockGT h` is `(blockG h)ᵗ` of the
print (`G_hᵗ A G_h`). -/
def blockGT {d : ℕ} (h : Mat d) : BlockMat d :=
  { upperLeft := 1
    upperRight := Matrix.transpose h
    lowerLeft := 0
    lowerRight := 1 }

/-- The transpose identity for the block pairing: pairing with the transposed
gauge block acting on the right is the pairing of the gauge block acting on
the left, `X · blockGT(h) Y = blockG(h) X · Y`, the block form of
`x · hᵀ y = h x · y` (`vecDot_matVecMul_transpose`).  This is what makes the
conjugation `G_{-h_U}^t (G_{h_U}^t A G_{h_U}) G_{-h_U}` of the print act on the slice
`(e, 0)` exactly as the paper's `Q · A Q` acts on `Q = G_{-h_U} (e, 0)`. -/
theorem blockVecDot_blockGT_transpose (h : Mat d) (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockGT h) Y)
      = blockVecDot (blockMatVecMul (blockG h) X) Y := by
  rcases X with ⟨x₁, x₂⟩
  rcases Y with ⟨y₁, y₂⟩
  have e1 : blockVecDot (x₁, x₂) (blockMatVecMul (blockGT h) (y₁, y₂))
      = vecDot x₁ (y₁ + matVecMul (Matrix.transpose h) y₂) + vecDot x₂ y₂ := by
    simp only [blockGT, blockMatVecMul_fst, blockMatVecMul_snd, blockVecDot,
      matVecMul_one_mat, matVecMul_zero_mat, zero_add]
  have e2 : blockVecDot (blockMatVecMul (blockG h) (x₁, x₂)) (y₁, y₂)
      = vecDot x₁ y₁ + vecDot (matVecMul h x₁ + x₂) y₂ := by
    simp only [blockG, blockMatVecMul_fst, blockMatVecMul_snd, blockVecDot,
      matVecMul_one_mat, matVecMul_zero_mat, add_zero]
  rw [e1, e2, vecDot_add_right, vecDot_transpose_matVecMul, vecDot_add_left]
  ring

/-! ### The main bound (`l.blupbounds`, corrected rendering) -/
