/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Blocks
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence
public import SuperdiffusionCLT.Section3.Setup.Scales

/-!
# The crude ellipticity bound and `e.p-bound-crude`

The paper records two crude deterministic bounds which
the term lemmas of Section 3 carry as explicit hypotheses named `hcrude`:

* the display `e.p-bound-crude`: `|p| ≤ nu^{-1/2}` for the test vector
  `p = shom_{L',*}^{-1/2}(cu_n) e` of `e.Sec3.p.q.def`;
* the scalar inequality `s_{L',*}^{-1}(cu_n) ≤ nu⁻¹` behind it, described in the
  sentence before `e.v.ky.energy` as "the bound
  `s_{L',*}^{-1}(U) ≤ nu^{-1} Id`, which is valid in every domain `U`".

This module derives both.  The paper derives them from the uniform ellipticity
`a_{L'} ≥ nu Id` of the cutoff coefficient, which is
available pointwise for `a_L = nu Id + k_L` because the shells are
anti-symmetric (`symmPart_coefficientCutoff`): the symmetric part of the cutoff
field is exactly `nu Id`, so the harmonic-mean identity
`e.CG.bounds.1` — `(⨍_U symmPart(a)^{-1})^{-1} ≤ s_*(U; a)` — reads

> `nu Id ≤ s_*(U; a_{L'})`, hence `s_*(U; a_{L'})^{-1} ≤ nu⁻¹ Id`,

and the inequality passes to the expectation because the annealed lower block
`shom_{L',*}^{-1}(U) = E[s_*^{-1}(U; a_{L'})]` is an entrywise Bochner integral
(`sigmaBarStarInv_eq_integral_sigmaStarInvCoarse`) and Loewner order is
preserved by entrywise integration (`matLoewnerLE_of_integral`). On an origin
cube the annealed lower block is a scalar matrix under J4
(`sigmaBarStarInv_originCube_eq_smul_one`), which gives the scalar form.

## Main results

* `averagedSymmPartInv_coefficientCutoff_cube`: the harmonic-mean matrix
  `⨍ symmPart(a_{L'})^{-1}` of the cutoff field on a triadic cube is `nu⁻¹ Id`.
* `matLoewnerLE_sigmaStarInvCoarse_cutoffCube`: the quenched crude ellipticity
  bound `s_*(cu; a_{L'})^{-1} ≤ nu⁻¹ Id`, valid on every triadic cube.
* `matLoewnerLE_sigmaBarStarInv_cutoffCube`: the annealed form,
  `shom_{L',*}^{-1}(cu) ≤ nu⁻¹ Id`.
* `sigmaBarStarInvSeq_le_nuInv`: the scalar form, the exact shape of the
  `hcrude` hypotheses of the term lemmas.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining

noncomputable section

variable {d : ℕ}

/-! ## Scalar identity matrices -/

section Scalars

/-- Positive definiteness of a strictly positive multiple of the identity, the
shape of `Matrix.PosDef.diagonal` for a scalar matrix. -/
theorem posDef_smul_one {nu : ℝ} (hnu : 0 < nu) :
    (nu • (1 : Mat d)).PosDef := by
  classical
  rw [Matrix.smul_one_eq_diagonal]
  exact Matrix.posDef_diagonal_iff.2 fun _ ↦ hnu

private theorem diag_smul_one (c : ℝ) (i : Fin d) : (c • (1 : Mat d)) i i = c := by
  simp

end Scalars

/-! ## The cutoff coefficient on a triadic cube -/

section Cube

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ)
  (Q : TriadicCube d)

/-- The Chapter 2 coefficient object of the cutoff field `a_L` on the triadic
cube `Q`, the object through which the Chapter 2 theory reaches `a_L` (the same
object the coarse-grained bounds of `Annealed.Integrability` use). -/
def cutoffCoeffOnCube : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
  (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (coefficientCutoff nu omega m)
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m)).coeffOn Q

omit [NeZero d] in
private theorem cutoffCoeffOnCube_toCoeffField :
    (cutoffCoeffOnCube hnu omega m Q).toCoeffField = (coefficientCutoff nu omega m).toFun :=
  rfl

omit [NeZero d] in
/-- **The harmonic-mean matrix of the cutoff field on a triadic cube is
`nu⁻¹ Id`**: the symmetric part of `a_L = nu Id + k_L` is the constant matrix
`nu Id` (`symmPart_coefficientCutoff`), so `⨍_{cu} symmPart(a_L)^{-1} =
nu⁻¹ Id` entrywise. -/
theorem averagedSymmPartInv_coefficientCutoff_cube :
    Book.Ch02.averagedSymmPartInv (Book.Ch02.cubeDomain Q) (cutoffCoeffOnCube hnu omega m Q)
      = nu⁻¹ • (1 : Mat d) := by
  classical
  ext i j
  have hpt : ∀ x : Vec d,
      ((symmPart ((coefficientCutoff nu omega m).toFun x))⁻¹ : Mat d) i j
        = (nu⁻¹ • (1 : Mat d)) i j := by
    intro x
    rw [symmPart_coefficientCutoff, inv_smul_one_mat hnu.ne']
  have hint : ∫ x in openCubeSet Q,
      ((symmPart ((coefficientCutoff nu omega m).toFun x))⁻¹ : Mat d) i j ∂volume =
      (volume (openCubeSet Q)).toReal * (nu⁻¹ • (1 : Mat d)) i j := by
    rw [MeasureTheory.setIntegral_congr_fun (isOpen_openCubeSet Q).measurableSet
      (fun x _ ↦ hpt x), MeasureTheory.setIntegral_const, smul_eq_mul,
      MeasureTheory.measureReal_def]
  change (volume (openCubeSet Q)).toReal⁻¹ *
    ∫ x in openCubeSet Q,
      ((symmPart ((cutoffCoeffOnCube hnu omega m Q).toCoeffField x))⁻¹ : Mat d) i j ∂volume
    = _
  rw [cutoffCoeffOnCube_toCoeffField, hint, volume_openCubeSet_toReal]
  have hvol : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  field_simp

end Cube

/-! ## The quenched crude ellipticity bound -/

section Quenched

variable {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d) (m : ℕ) (Q : TriadicCube d)

include hnu

/-- **The quenched crude ellipticity bound `s_*(cu; a_{L'})^{-1} ≤ nu⁻¹ Id`**,
valid on every triadic cube — the sentence before `e.v.ky.energy`, which derives it
from the uniform ellipticity `a_{L'} ≥ nu Id` of the cutoff coefficient. The
derivation here is: the harmonic-mean identity of `e.CG.bounds.1`,
`(⨍_{cu} symmPart(a)^{-1})^{-1} ≤ s_*(cu; a)` (`harmonicMean_le_sigmaStarCoarse`),
whose harmonic-mean matrix is `nu⁻¹ Id` because the symmetric part of `a_{L'}`
is the constant matrix `nu Id` (`averagedSymmPartInv_coefficientCutoff_cube`),
inverted by `matLoewnerLE_inv_of_posDef`. -/
theorem matLoewnerLE_sigmaStarInvCoarse_cutoffCube :
    MatLoewnerLE (sigmaStarInvCoarse (openCubeSet Q)
      (coefficientCutoff nu omega m).toFun) (nu⁻¹ • (1 : Mat d)) := by
  classical
  have havg : Book.Ch02.averagedSymmPartInv (Book.Ch02.cubeDomain Q)
      (cutoffCoeffOnCube hnu omega m Q) = nu⁻¹ • (1 : Mat d) :=
    averagedSymmPartInv_coefficientCutoff_cube hnu omega m Q
  have hAvg : ((Book.Ch02.averagedSymmPartInv (Book.Ch02.cubeDomain Q)
      (cutoffCoeffOnCube hnu omega m Q))⁻¹).PosDef := by
    rw [havg, inv_smul_one_mat (nu := nu⁻¹) (inv_ne_zero hnu.ne'), inv_inv]
    exact posDef_smul_one hnu
  have hSig : (sigmaStarCoarse (openCubeSet Q)
      (cutoffCoeffOnCube hnu omega m Q).toCoeffField).PosDef :=
    sigmaStarCoarse_posDef (Book.Ch02.cubeDomain Q) (cutoffCoeffOnCube hnu omega m Q)
  have horder := harmonicMean_le_sigmaStarCoarse (Book.Ch02.cubeDomain Q)
    (cutoffCoeffOnCube hnu omega m Q)
  have hAvgPos : (Book.Ch02.averagedSymmPartInv (Book.Ch02.cubeDomain Q)
      (cutoffCoeffOnCube hnu omega m Q)).PosDef := by
    rw [havg]
    exact posDef_smul_one (inv_pos.2 hnu)
  have h : MatLoewnerLE
      ((Homogenization.sigmaStarCoarse
          (Book.Ch02.cubeDomain Q : Set (Vec d))
          (cutoffCoeffOnCube hnu omega m Q).toCoeffField)⁻¹)
      ((Book.Ch02.averagedSymmPartInv (Book.Ch02.cubeDomain Q)
        (cutoffCoeffOnCube hnu omega m Q))⁻¹)⁻¹ :=
    matLoewnerLE_inv_of_posDef hAvg hSig horder
  rw [inv_sigmaStarCoarse (Book.Ch02.cubeDomain Q) (cutoffCoeffOnCube hnu omega m Q),
    cutoffCoeffOnCube_toCoeffField hnu omega m Q, Matrix.nonsing_inv_nonsing_inv _
      (((Book.Ch02.averagedSymmPartInv (Book.Ch02.cubeDomain Q)
        (cutoffCoeffOnCube hnu omega m Q)).isUnit_iff_isUnit_det).mp
        hAvgPos.isUnit), havg] at h
  exact h

end Quenched

/-! ## The annealed crude ellipticity bound -/

section Annealed

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- The quenched coarse matrix `s_*(cu; a_m)^{-1}` is integrable in `omega`, so
the annealed lower block of `e.homs.defs.U` is a genuine expectation. -/
theorem integrable_sigmaStarInvCoarse_apply (Q : TriadicCube d) (i j : Fin d) :
    Integrable (fun omega : ShellSeq d ↦
      sigmaStarInvCoarse (openCubeSet Q)
        (coefficientCutoff nu omega m).toFun i j) P.toMeasure := by
  refine (integrable_coarseBlockMatrix_lowerRight_apply hnu m Q hPrefix hJ2 hJ3 hJ4
    i j).congr (Filter.Eventually.of_forall fun omega ↦ ?_)
  show (coarseBlockMatrix (cubeSet Q)
      (coefficientCutoff nu omega m).toFun).lowerRight i j =
    sigmaStarInvCoarse (openCubeSet Q)
      (coefficientCutoff nu omega m).toFun i j
  rw [coarseBlockMatrix_cubeSet_lowerRight_eq
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) Q]

/-- **The annealed crude ellipticity bound `shom_{m,*}^{-1}(cu) ≤ nu⁻¹ Id`** on a
triadic cube, the annealed form of the sentence before `e.v.ky.energy`. The almost-sure ordering
`matLoewnerLE_sigmaStarInvCoarse_cutoffCube` passes to the entrywise
expectation `sigmaBarStarInv_eq_integral_sigmaStarInvCoarse` through
`matLoewnerLE_of_integral`. -/
theorem matLoewnerLE_sigmaBarStarInv_cutoffCube (Q : TriadicCube d) :
    MatLoewnerLE (sigmaBarStarInv nu m P (cubeSet Q)) (nu⁻¹ • (1 : Mat d)) := by
  have hA : ∀ i j : Fin d, Integrable (fun omega : ShellSeq d ↦
      sigmaStarInvCoarse (openCubeSet Q)
        (coefficientCutoff nu omega m).toFun i j) P.toMeasure :=
    fun i j => integrable_sigmaStarInvCoarse_apply hnu m hPrefix hJ2 hJ3 hJ4 Q i j
  have hB : ∀ i j : Fin d, Integrable
      (fun omega : ShellSeq d ↦ (nu⁻¹ • (1 : Mat d)) i j) P.toMeasure :=
    fun _ _ => integrable_const _
  have h := matLoewnerLE_of_integral hA hB
    (Filter.Eventually.of_forall fun omega ↦
      matLoewnerLE_sigmaStarInvCoarse_cutoffCube hnu omega m Q)
  have hAint : (sigmaBarStarInv nu m P (cubeSet Q) : Mat d)
      = fun i j ↦ ∫ omega, sigmaStarInvCoarse (openCubeSet Q)
          (coefficientCutoff nu omega m).toFun i j ∂P.toMeasure := by
    funext i j
    exact sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu m P Q i j
  have hBint : ((nu⁻¹ • (1 : Mat d)) : Mat d)
      = fun i j ↦ ∫ _omega : ShellSeq d, (nu⁻¹ • (1 : Mat d)) i j ∂P.toMeasure := by
    funext i j
    rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  intro x
  rw [hAint, hBint]
  exact h x

/-- **The scalar form of the crude bound, `shom_{m,*}^{-1}(cu_n) ≤ nu⁻¹`**: the
exact shape of the hypothesis `hcrude` carried by the term lemmas
(the sentence before `e.v.ky.energy` of the paper). -/
theorem sigmaBarStarInvSeq_le_nuInv (n : ℕ) :
    sigmaBarStarInvSeq nu m P n ≤ nu⁻¹ := by
  have h := matLoewnerLE_sigmaBarStarInv_cutoffCube hnu m hPrefix hJ2 hJ3 hJ4
    (originCube d n)
  rw [sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 n] at h
  have hd := diag_le_of_matLoewnerLE h 0
  rw [diag_smul_one, diag_smul_one] at hd
  exact hd

end Annealed

end

end SuperdiffusionCLT.Section3.Setup