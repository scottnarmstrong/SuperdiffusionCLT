/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.SkewRemainderRepresentation

/-!
# The variational data of the skew remainder

`SkewRemainderRepresentation.lean` reduces the small-branch `η²` estimate at
the cutoff pair to two residuals: the pointwise remainder identity,
`(p,q) - (X x - Xt x) = (0, H r)`, and the energy domination of the shift,
`r · s r ≤ (p,q) · 𝐀_t (p,q)`.  This module records two elementary facts about
the energy side of that reduction.

## The `s`-energy at `symmPart A = ν Id`

At the cutoff pair the matrix `A` has `symmPart A = ν Id` with `ν > 0`
(`symmPart_coefficientCutoff`), so the `s`-energy `r · s r` is `ν ‖r‖²`.  It is
therefore unbounded in `r`, while the right side of the domination is a fixed
finite number.  Hence a domination stated separately for every `r : Vec d` is
unsatisfiable, and the domination can only be asked at the single witness `r`
of the remainder identity.

## The honest energy domination

At `symmPart A = ν Id` the block form dominates `ν ‖·‖²`, so the potential part
of any admissible state has `s`-energy at most its block energy.

## Main results

* `vecDot_smul_one_self`: the `s`-energy at `symmPart A = ν Id` is `ν ‖·‖²`.
* `symmEnergy_le_averagedBlockQuadratic`: the honest energy domination.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The `s`-energy at `symmPart A = ν Id` -/

private theorem matVecMul_one_local {d : ℕ} (x : Vec d) :
    matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply]

/-- The `s`-energy of a vector against `ν Id` is `ν` times its squared norm.
This is the identity that makes the universal-in-`r` domination unbounded. -/
theorem vecDot_smul_one_self (nu : ℝ) (r : Vec d) :
    vecDot r (matVecMul (nu • (1 : Mat d)) r) = nu * vecNormSq r := by
  have h : matVecMul (nu • (1 : Mat d)) r = nu • r := by
    rw [smul_matVecMul, matVecMul_one_local]
  rw [h, vecDot_smul_right]
  rfl

/-! ## The honest energy domination -/

/-- **The block energy dominates the potential `s`-energy.**  At
`symmPart A = ν Id` the block form is `ν ‖x‖² + ν⁻¹ ‖y - k x‖²`, so the first
slot alone accounts for `ν ‖x‖²`. -/
theorem symmEnergy_le_averagedBlockQuadratic {A : Mat d} {nu lam Lam : ℝ}
    (hA : IsEllipticMatrix lam Lam A) (hs : symmPart A = nu • (1 : Mat d))
    (W : BlockVec d) :
    nu * vecNormSq W.1 ≤ averagedBlockQuadratic A W := by
  unfold averagedBlockQuadratic
  rw [blockMatrixOfCoeff_quadratic_eq]
  have h1 : vecDot W.1 (matVecMul (symmPart A) W.1) = nu * vecNormSq W.1 :=
    vecDot_symmPart_eq_mul_vecNormSq hs W.1
  have h2 : 0 ≤ vecDot (W.2 - matVecMul (skewPart A) W.1)
      (matVecMul ((symmPart A)⁻¹) (W.2 - matVecMul (skewPart A) W.1)) :=
    symmPart_inv_nonneg_of_isEllipticMatrix hA _
  linarith only [h1, h2]

end

end SuperdiffusionCLT.Section2.Localization
