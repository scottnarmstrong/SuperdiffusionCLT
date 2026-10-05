/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespEllipticity
public import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Response

/-!
# An explicit, `R`-independent bound on `normalizedBlockResponseMax`

`Homogenization.normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn`
(`CoarseGraining`, `Deterministic/MultiscaleQuantitiesBasic/Response.lean`)
shows `normalizedBlockResponseValueSet Q a a0` is bounded above, for an
explicit constant built only from `lam, Lam, a0` (no dependence on `Q`), but it
only exposes `BddAbove`, an opaque existential: two separate applications (at
two different cubes) give two a priori unrelated bounds. This module reproves
the same estimate with the bound exposed explicitly, so that the SAME real
number bounds `normalizedBlockResponseMax R a a0` for every `R` sharing the
ellipticity constants `(lam, Lam)` — exactly what its use (bounding
every descendant cube of `originCube d n`, at every scale `l`, uniformly) needs.

## Main result

* `srootL3_normalizedBlockResponseMax_le`: an explicit bound on
  `normalizedBlockResponseMax R a a0` from `IsEllipticFieldOn lam Lam (cubeSet
  R) a`, depending only on `lam, Lam, a0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory
open scoped MatrixOrder

noncomputable section

/-- **An explicit, cube-independent upper bound on `normalizedBlockResponseMax`.**
Adapted from `normalizedBlockResponseValueSet_bddAbove_of_isEllipticFieldOn`'s
proof, exposing the bound (a pure function of `lam, Lam, a0`) directly instead
of packaging it as `BddAbove`. -/
theorem srootL3_normalizedBlockResponseMax_le {d : ℕ} [NeZero d] (R : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a) :
    normalizedBlockResponseMax R a a0 ≤
      (lam / (1 + 2 * Lam ^ 2))⁻¹ *
          fullBlockMatRowAbsSqBound (constantFullBlockMatrixSqrt a0) +
        (lam / (1 + 2 * Lam ^ 2))⁻¹ * blockMatrixOfCoeffNormSqBound lam Lam *
          fullBlockMatRowAbsSqBound (constantFullBlockMatrixInvSqrt a0) := by
  let MInv := constantFullBlockMatrixInvSqrt a0
  let MSqrt := constantFullBlockMatrixSqrt a0
  set B : ℝ :=
    (lam / (1 + 2 * Lam ^ 2))⁻¹ * fullBlockMatRowAbsSqBound MSqrt +
      (lam / (1 + 2 * Lam ^ 2))⁻¹ *
        blockMatrixOfCoeffNormSqBound lam Lam * fullBlockMatRowAbsSqBound MInv with hBdef
  unfold normalizedBlockResponseMax
  refine csSup_le (normalizedBlockResponseValueSet_nonempty R a a0) ?_
  rintro m ⟨e, he, rfl⟩
  let xR : Vec d := fun i => (R.index i : ℝ) * cubeScaleFactor R
  have hxR : xR ∈ cubeSet R := by
    intro i
    constructor <;> dsimp [xR]
    · have hscale : 0 < cubeScaleFactor R := by
        simpa [cubeScaleFactor] using zpow_pos (by norm_num : 0 < (3 : ℝ)) R.scale
      nlinarith only [hscale]
    · have hscale : 0 < cubeScaleFactor R := by
        simpa [cubeScaleFactor] using zpow_pos (by norm_num : 0 < (3 : ℝ)) R.scale
      nlinarith only [hscale]
  rcases hEll.2 xR hxR with ⟨hlam_pos, hlamLam, -, -⟩
  have hvolR : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hcoeff_nonneg : 0 ≤ (lam / (1 + 2 * Lam ^ 2))⁻¹ := by
    have hden_pos : 0 < 1 + 2 * Lam ^ 2 := by positivity
    have hfrac_pos : 0 < lam / (1 + 2 * Lam ^ 2) := div_pos hlam_pos hden_pos
    positivity
  have hbound_nonneg : 0 ≤ blockMatrixOfCoeffNormSqBound lam Lam := by
    unfold blockMatrixOfCoeffNormSqBound
    positivity
  let P := ofFullBlockVec (Matrix.mulVec MInv e)
  let Q' := ofFullBlockVec (Matrix.mulVec MSqrt e)
  have hP : blockVecDot P P ≤ fullBlockMatRowAbsSqBound MInv := by
    dsimp [P, MInv]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  have hQ : blockVecDot Q' Q' ≤ fullBlockMatRowAbsSqBound MSqrt := by
    dsimp [Q', MSqrt]
    rw [blockVecDot_ofFullBlockVec_self_eq_fullBlockVecNormSq]
    exact fullBlockVecNormSq_mulVec_le_rowAbsSqBound_of_eq_one _ he
  calc
    BlockJ (cubeSet R) P Q' a ≤ blockResponsePlainUpperBound lam Lam P Q' :=
      blockJ_le_plainUpperBound_of_isEllipticFieldOn
        (a := a) (U := cubeSet R) (measurableSet_cubeSet R) hEll hvolR P Q'
    _ ≤ B := by
      let c : ℝ := (lam / (1 + 2 * Lam ^ 2))⁻¹
      have htermQ : c * blockVecDot Q' Q' ≤ c * fullBlockMatRowAbsSqBound MSqrt :=
        mul_le_mul_of_nonneg_left hQ hcoeff_nonneg
      have htermP :
          c * blockMatrixOfCoeffNormSqBound lam Lam * blockVecDot P P ≤
            c * blockMatrixOfCoeffNormSqBound lam Lam * fullBlockMatRowAbsSqBound MInv :=
        mul_le_mul_of_nonneg_left hP (mul_nonneg hcoeff_nonneg hbound_nonneg)
      rw [hBdef]
      unfold blockResponsePlainUpperBound
      dsimp [c] at htermQ htermP
      linarith only [htermQ, htermP]

end

end SuperdiffusionCLT.Section4.MinimalScales
