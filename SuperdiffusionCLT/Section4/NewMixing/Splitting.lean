/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.ParamStatement
public import SuperdiffusionCLT.Section2.CoarseGraining.SkewShiftCutoff
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup
public import SuperdiffusionCLT.Frozen.Section2.LocalizationAverage

/-!
# The splitting step (`e.new.mixing.splitting`, `e.new.mixing.localization.error`)

This is part of the proof of `l.new.mixing.parameterized`.

Ingredients:
* the gauge-conjugation identity for a constant skew shift,
  `SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn`;
* the gauge group law `e.G.group`,
  `SuperdiffusionCLT.Section2.Localization.blockG_mul_blockG`;
* subadditivity of the doubled response,
  `Homogenization.coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic`,
  via the bridge identity
  `SuperdiffusionCLT.Section2.CoarseGraining.responseJ_eq_blockQuadratic`;
* the one-shot bound
  `SuperdiffusionCLT.Frozen.Section2.localization_average`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Localization

noncomputable section

/-- The constant-skew gauge identity, at the marginal `a_L + h_0` carrier:
`P · bfA(cu_m; a_L + h_0) P = (G_{-h_0} P) · bfA(cu_m; a_L) (G_{-h_0} P)`. -/
theorem newMixParam_splitting_gaugeShift {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (L m : ℕ) (h0 : Mat d) (hh0 : matTranspose h0 = -h0) (Pvec : BlockVec d) :
    blockVecDot Pvec
        (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix
            (Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
            (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
          Pvec) =
      blockVecDot (blockMatVecMul (blockG (-h0)) Pvec)
        (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix
            (Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
            (SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn
              (Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
              hnu omega L
              (fun x hx i j => newMixParam_entryBound_holds _ nu hnu omega L x hx i j)))
          (blockMatVecMul (blockG (-h0)) Pvec)) := by
  unfold newMixParam_aLplusH0
  rw [SuperdiffusionCLT.Section2.CoarseGraining.coarseBlockMatrix_addConstSkewCoeffOn]
  exact SuperdiffusionCLT.Section2.Localization.blockVecDot_conj_blockMatMul _ _ Pvec

/-- The cutoff field `a_L` is pointwise elliptic on any bounded domain `U`,
with the same lower constant `nu` and upper constant built from
`newMixParam_entryBound`. Needed for the raw `CoarseGraining` subadditivity
theorem's `IsEllipticFieldOn` hypothesis. -/
theorem newMixParam_isEllipticFieldOn_coefficientCutoff {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (L : ℕ) (U : Homogenization.Book.Ch02.Domain d) :
    Homogenization.IsEllipticFieldOn nu
        (((d : ℝ) * (d : ℝ) * (newMixParam_entryBound U nu omega L) ^ 2 + nu ^ 2) / nu)
        (U : Set (Vec d))
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField := by
  classical
  refine ⟨?_, ?_⟩
  · have hEq : (fun x i j => if x ∈ (U : Set (Vec d)) then
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x i j
        else 0) =
      fun x i j => if x ∈ (U : Set (Vec d))
        then (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField x
              i j
        else 0 := rfl
    rw [hEq]
    refine Measurable.of_eval (fun i => Measurable.of_eval (fun j => ?_))
    exact (Homogenization.RegCoeffField.entry_measurable
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L) i j).ite
      U.measurableSet measurable_const
  · intro x _hx
    exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
      hnu (SuperdiffusionCLT.Section2.Cutoff.symmPart_coefficientCutoff nu omega L x)
      (fun i j => newMixParam_entryBound_holds U nu hnu omega L x _hx i j)

/-- The `ResponseJ`-to-block-quadratic bridge for `a_L` on any open triadic
cube, in the raw `Set (Vec d)`/`CoeffField d` shape the `CoarseGraining`
subadditivity theorem needs. -/
theorem newMixParam_respJ_blockQuadratic {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (L : ℕ) (Q : Homogenization.TriadicCube d) (p q : Vec d) :
    Homogenization.ResponseJ (Homogenization.openCubeSet Q) p q
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.openCubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
            (-p, q)) -
        vecDot p q := by
  set aOn := SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn
    (Homogenization.Book.Ch02.cubeDomain Q) hnu omega L
    (fun x hx i j => newMixParam_entryBound_holds _ nu hnu omega L x hx i j) with haOn
  have hkey := SuperdiffusionCLT.Section2.CoarseGraining.responseJ_eq_blockQuadratic
    (Homogenization.Book.Ch02.cubeDomain Q) aOn p q
  rw [SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField] at hkey
  rw [Homogenization.Book.Ch02.cubeDomain_coe] at hkey
  rw [← SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_toCoeffField
    (Homogenization.Book.Ch02.cubeDomain Q) aOn] at hkey
  rw [SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField] at hkey
  rw [Homogenization.Book.Ch02.cubeDomain_coe] at hkey
  exact hkey

/-- **Subadditivity of `P·bfA(cu_m;a_L)P`** over the depth-`(m-n)` triadic
descendants of `cu_m`, `n ≤ m`: the first step of `e.new.mixing.splitting`
(printed as "subadditivity ... yield"). -/
theorem newMixParam_subadditivity {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (L m n : ℕ) (Pvec : BlockVec d) :
    blockVecDot Pvec
        (blockMatVecMul
          (Homogenization.coarseBlockMatrix
            (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)))
            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
          Pvec) ≤
      Homogenization.descendantsAverage (Homogenization.originCube d (m : ℤ)) (m - n)
        (fun R => blockVecDot Pvec
          (blockMatVecMul
            (Homogenization.coarseBlockMatrix (Homogenization.openCubeSet R)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
            Pvec)) := by
  have hEllU := newMixParam_isEllipticFieldOn_coefficientCutoff hnu omega L
    (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m : ℤ)))
  rw [Homogenization.Book.Ch02.cubeDomain_coe] at hEllU
  have hkey :=
    Homogenization.coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_blockQuadratic_of_responseJ_blockQuadratic
      (m - n) (Homogenization.originCube d (m : ℤ))
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField
      hEllU
      (fun p q => newMixParam_respJ_blockQuadratic hnu omega L
        (Homogenization.originCube d (m : ℤ)) p q)
      (fun R _ p q => newMixParam_respJ_blockQuadratic hnu omega L R p q)
      Pvec
  rw [Homogenization.descendantsAverage_smul] at hkey
  linarith only [hkey]

end
end SuperdiffusionCLT.Section4.NewMixing
