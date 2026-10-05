/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Energy
public import SuperdiffusionCLT.Section2.Localization.PsdSqrtQuadratic
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks

/-!
# The flux-additivity step of `e.RHS.term3.A`, and the inverse square root of the coarse block

Step 2 of the proof of `e.RHS.term3.A`.  The printed argument has these steps.

* The display `e.flux-additivity-estimate-in-an-lemma`:
  `E[avsum_{z in 3^n Z^d cap cu_m} |b_{L'}^{-1/2}(z+cu_n)
  (a_{L'}nabla(u_m - u_{n,z}))_{z+cu_n}|^2] <=
  E[avsum_z ⨍_{z+cu_n} nabla(u_m-u_{n,z})·sigma nabla(u_m-u_{n,z})] <= delta + C eta_L`.
  The first inequality is `e.energymaps.nonsymm.flux` applied to
  the *difference* of two maximizers; the second is `e.additivity.error.superdiff`.
* The display `e.w-flux-indepen-decomp`: the split of the
  left side of `e.RHS.term3.A` into a product of independent factors plus a
  difference term.
* The next display: Cauchy-Schwarz in the metric of `b_{L'}`
  with the silent insertion `b^{1/2} b^{-1/2}`, ending with
  `<= E[avsum_{z',z}|b_{L'}^{1/2}(z+cu_n)(nabla w)_{z'+cu_k}|^2]^{1/2}
  (delta + C eta_L)^{1/2}`.
* The following display: the same chain for the difference term,
  ending with `<= C 3^{-d(ell'-ell)/(d+4)} (L')^2 nu^{-5/2}`.
* The conclusion: "where in the last inequality we used (e.nablaw.Lt) and
  (e.p-bound-crude). Combining the above displays yields (e.RHS.term3.A)."

## What this module proves

**The first inequality of the display `e.flux-additivity-estimate-in-an-lemma`.**
`hFluxAdd` — the flux
conjunct `(card^-1) sum_z ∫ normFlux omega z ≤ delta + etaL` of the coarse-graining
display — is `flux_additivity_estimate` verbatim.  Its `hEnergy` slot is
the printed middle member at the carrier `energyL2Carrier`, which is
`hEnergy_at_carriers`.  `hFluxAdd_of_energyMaps`
composes the two, so `hFluxAdd` needs exactly two things and nothing else:
`hEnergyMaps`, the pointwise energy-map inequality, and the four
printed hypotheses of `e.additivity.error.superdiff` that `hEnergy_at_carriers`
already carries (`hAnnealedSub`, `hAnnealedBig`, its integrability bundle, and
`hPigeon`).  `hEnergyMaps` is the one genuinely new residual, and it is the
step for which the printed `normFlux` needs a carrier: it is
`|b_{L'}^{-1/2}(z+cu_n)(a_{L'}nabla(u_m - u_{n,z}))_{z+cu_n}|^2`, whose
`b^{-1/2}` factor is the inverse square root of the coarse block.

**The `b^{-1/2}` carrier.**  `posDef_translatedCoarseBlock` proves the
positive-definiteness of `b_L(z+cu_n)` unconditionally from `0 < nu`: the coarse
block is the Chapter 2 `bCoarse` of the uniformly elliptic cutoff coefficient,
and `bCoarse_posDef` gives positive definiteness with no side condition beyond
ellipticity (the ellipticity being `nu Id` for the symmetric part, from
`coefficientCutoffCoeffOn`).  Hence `isUnit_translatedCoarseBlock`,
the positivity of its determinant and the inverse square root
`translatedBlockInvSqrt nu L omega z = b_L^{1/2}(z+cu_n) · b_L(z+cu_n)^{-1}`,
which is the printed `b_L^{-1/2}(z+cu_n)` because `b_L^{-2} = b_L^{-1}` for the
invertible `b_L`.  `translatedBlockHalfWeightInv` is its quadratic form
`|b_L^{-1/2}(z+cu_n) v|^2`, the `normFlux` carrier, and
`translatedBlockHalfWeightInv_eq_vecDot_inv` identifies it with the dual form
`v · b_L(z+cu_n)^{-1} v`.  `translatedBlock_insertion` is the printed insertion
of `b^{1/2} b^{-1/2}` — Cauchy-Schwarz in the `b_L(z+cu_n)` metric,
`(u·v)^2 <= |b_L^{1/2} u|^2 |b_L^{-1/2} v|^2` — at these carriers.
The carrier squared *is* `b_L(z+cu_n)^{-1}`, so it is the
inverse square root and not merely a formal product.

**The insertion step.**  `vecDot_le_sqrt_mul_sqrt` is the
pointwise Cauchy-Schwarz inequality in the square-root form the paper
prints, and `insertCS_of_volumeAverage` is that inequality at the printed
vectors, so the `hInsertCS` binder of the term-3.B assembly holds as soon
as its `normFlux` is named as the printed inverse half weight.
(The binder `hInsertDiff` differs only in having `bHalfDiff` in place of
`translatedBlockHalfWeight` on the left; its right factor is the same carrier.)

The positive-definiteness is not decorative: at a merely positive-*semi*definite
block the insertion fails, so the `b^{-1/2}` of the source is legitimate exactly
because the coarse block is invertible.

## Main results

* `sum_assemblyEnergyCarrier_eq_sum_volumeAverageDiff`,
  `hFluxAdd_of_energyMaps`: the reduction of `hFluxAdd`.
* `posDef_translatedCoarseBlock`, `isUnit_translatedCoarseBlock`: the invertibility of the
  coarse block.
* `translatedBlockInvSqrt`, `translatedBlockHalfWeightInv`,
  `translatedBlockHalfWeightInv_eq_vecDot_inv`, `translatedBlock_insertion`.
* `vecDot_le_sqrt_mul_sqrt`, `insertCS_of_volumeAverage`: the printed
  Cauchy-Schwarz step in the proof of `e.RHS.term3.A`, i.e. the `hInsertCS` step.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## 1. The transport of the printed middle member -/

/-- The printed middle member of `e.flux-additivity-estimate-in-an-lemma`,
`E[avsum_z ⨍_{z+cu_n} nabla(u_m-u_{n,z})·sigma
nabla(u_m-u_{n,z})]`, at the carrier `energyL2Carrier`, equals the sum
over the large cube's sub-cubes of the open-cube average of
`nu |nabla u_m - nabla u_{n,z}|^2` that `flux_additivity_estimate` consumes.

This is the transport that lets the conclusion of `hEnergy_at_carriers`
(stated at `assemblyEnergyCarrier`, i.e.
`energyL2Carrier`) fill the `hEnergy` slot of `flux_additivity_estimate`; its
body is the pointwise identification `energyL2Carrier_eq_volumeAverage_openCubeSet`
under the sum and the expectation. -/
theorem sum_assemblyEnergyCarrier_eq_sum_volumeAverageDiff [NeZero d]
    (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d) (S : ScaleSelection) :
    (∑ R ∈ largeCubeSubcubes d S.n S.m,
        ∫ omega : ShellSeq d,
          assemblyEnergyCarrier nu uMgrad uNGlued omega R ∂P.toMeasure) =
      ∑ R ∈ largeCubeSubcubes d S.n S.m,
        ∫ omega : ShellSeq d,
          volumeAverage (openCubeSet R)
            (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y))
          ∂P.toMeasure := by
  refine Finset.sum_congr rfl fun R _ => ?_
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
  show energyL2Carrier nu (uMgrad omega) (uNGlued omega) R = _
  exact energyL2Carrier_eq_volumeAverage_openCubeSet nu _ _ R


/-- **`hFluxAdd`, reduced to the energy-map step.**
The conclusion is *verbatim* the `hFluxAdd` binder of the coarse-graining display: with
`normFlux` the printed normalization `|b_{L'}^{-1/2}(z+cu_n)(a_{L'}nabla(u_m-u_{n,z}))_{z+cu_n}|^2`,
the flux conjunct is
`(card^-1) sum_{z in largeCubeSubcubes} ∫ omega, normFlux omega z <= delta + etaL`.

The proof is the composition of the two halves of the printed display
`e.flux-additivity-estimate-in-an-lemma`:

* `hEnergyMaps` is the first inequality, pointwise in `omega`
  and `R`: `normFlux omega R <= ⨍_{R} nu |nabla u_m - nabla u_{n,z}|^2`.  It is
  the only genuinely new hypothesis; it is `e.energymaps.nonsymm.flux` applied
  to the difference of two maximizers, and no carrier for it is available.
* the four printed inputs of `e.additivity.error.superdiff`
  `hAnnealedSub`, `hAnnealedBig`, the integrability bundle and `hPigeon`, which
  `hEnergy_at_carriers` turns into the second inequality,
  `E[avsum_z ⨍_R nu|nabla u_m - nabla u_{n,z}|^2] <= delta + etaL`, at the
  carrier `energyL2Carrier`.

No constant is invented: the constant of the conclusion is `1`, and the
`delta + etaL` is the paper's `delta + C eta_L` with `C = 1`
(`additivity_error_superdiff_at_carriers` is already normalized to `C = 1`). -/
theorem hFluxAdd_of_energyMaps [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) {e : Vec d} (he : vecNormSq e = 1)
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (normFlux : ShellSeq d → TriadicCube d → ℝ)
    (hEnergyMaps : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      normFlux omega R ≤
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)))
    (hFluxInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => normFlux omega R) P.toMeasure)
    (hEnergyIntDiff : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq (uMgrad omega y - uNGlued omega y)))
        P.toMeasure)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e uMgrad uNGlued omega R ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e uMgrad omega ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        energySubQCarrier nu P S e uMgrad uNGlued omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y))) P.toMeasure)
    (hEnergyCube : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => -(nu / 2) * vecNormSq (uMgrad omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e) (uMgrad omega y)) (cubeSet R) volume)
    {delta etaL : ℝ}
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
    ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, normFlux omega z ∂P.toMeasure ≤ delta + etaL := by
  have hEn := hEnergy_at_carriers hnu hPrefix hJ2 hJ3 hJ4 S he uMgrad uNGlued
    hAnnealedSub hAnnealedBig hJsubInt hEnergyInt hEnergyCube hPigeon
  rw [sum_assemblyEnergyCarrier_eq_sum_volumeAverageDiff nu P uMgrad uNGlued S] at hEn
  exact flux_additivity_estimate P S uMgrad uNGlued normFlux hEnergyMaps hFluxInt
    hEnergyIntDiff hEn

/-! ## 2. Positive-definiteness and invertibility of the coarse block -/

/-- **`b_L(z+cu_n)` is positive definite**, hence invertible — for every sample
and every translated cube, from `0 < nu` alone.

`translatedCoarseBlock nu L omega z` is the upper-left block of the coarse
block matrix of the cutoff coefficient `a_L = nu Id + k_L` on the cube `z`.  It
is the Chapter 2 `bCoarse` of `a_L`, whose symmetric part is the constant
`nu Id` (`coefficientCutoffCoeffOn`),
and `bCoarse_posDef` is unconditional in the ellipticity of that coefficient.
So the invertibility of the coarse block on the cutoff cube, which the paper
uses silently in the inverse square root, is a theorem and not an assumption. -/
theorem posDef_translatedCoarseBlock [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (omega : ShellSeq d) (z : TriadicCube d) :
    (translatedCoarseBlock nu L omega z).PosDef := by
  rw [translatedCoarseBlock, translatedBlockMat,
    ← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube z,
    show coarseBlockMatrix (cubeSet z) (coefficientCutoff nu omega L).toCoeffField =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain z)
        ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (coefficientCutoff nu omega L)
            (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn z) from
      Book.Ch04.RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z,
    Book.Ch02.coarseBlockMatrix_upperLeft]
  exact Book.Ch02.bCoarse_posDef _ _

/-- The coarse block on the cutoff cube is a unit: it is invertible, so
`b_L(z+cu_n)^{-1}` is the genuine inverse and `b_L^{-1/2}` is well defined. -/
theorem isUnit_translatedCoarseBlock [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (omega : ShellSeq d) (z : TriadicCube d) :
    IsUnit (translatedCoarseBlock nu L omega z) :=
  (posDef_translatedCoarseBlock hnu L omega z).isUnit

/-! ## 3. The `b^{-1/2}` carrier and the printed insertion -/

/-- **`b_L^{-1/2}(z+cu_n)`**, the inverse square root of the coarse block on the
translated cube: `b_L^{1/2}(z+cu_n) · b_L(z+cu_n)^{-1}`.

This is the printed `b^{-1/2}` of `e.RHS.term3.A`.  It is well defined
because `b_L(z+cu_n)` is invertible (`isUnit_translatedCoarseBlock`), and it is
the inverse square root because `b_L^{-2} = b_L^{-1}` for the invertible
`b_L`; the definition writes it as `b^{1/2} · b^{-1}` rather than
`(b^{1/2})^{-1}` so that the square-root quadratic form
`vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul` applies without any
commutation or invertibility hypothesis on the square root itself. -/
def translatedBlockInvSqrt (nu : ℝ) (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) :
    Mat d :=
  CFC.sqrt (translatedCoarseBlock nu L omega z) * (translatedCoarseBlock nu L omega z)⁻¹

/-- **`|b_L^{-1/2}(z+cu_n) v|^2`**, the printed normalization of the flux term and
the missing carrier of the `normFlux` binder. -/
def translatedBlockHalfWeightInv (nu : ℝ) (L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) (v : Vec d) : ℝ :=
  vecNormSq (matVecMul (translatedBlockInvSqrt nu L omega z) v)

/-- The inverse half weight is nonnegative. -/
theorem translatedBlockHalfWeightInv_nonneg (nu : ℝ) (L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) (v : Vec d) :
    0 ≤ translatedBlockHalfWeightInv nu L omega z v :=
  vecNormSq_nonneg _

/-- **The inverse half weight is the dual quadratic form**
`v · b_L(z+cu_n)^{-1} v`: the printed `|b_L^{-1/2}(z+cu_n) v|^2` equals
`(v)_{z+cu_n} · b_L^{-1}(z+cu_n) (v)_{z+cu_n}`. -/
theorem translatedBlockHalfWeightInv_eq_vecDot_inv [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (L : ℕ) (omega : ShellSeq d) (z : TriadicCube d) (v : Vec d) :
    translatedBlockHalfWeightInv nu L omega z v =
      vecDot v (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v) := by
  have hpsd : (translatedCoarseBlock nu L omega z).PosSemidef :=
    (posDef_translatedCoarseBlock hnu L omega z).posSemidef
  have hdet : IsUnit (translatedCoarseBlock nu L omega z).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_translatedCoarseBlock hnu L omega z)
  have hsq := vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul hpsd
    (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v)
  rw [translatedBlockHalfWeightInv, translatedBlockInvSqrt, ← matVecMul_mul]
  rw [hsq, matVecMul_mul, Matrix.mul_nonsing_inv _ hdet, matVecMul_one, vecDot_comm]

/-- **The printed insertion at these carriers.**  For the
invertible coarse block `b_L(z+cu_n)` and any vectors `u`, `v`,

`(u·v)^2 <= |b_L^{1/2}(z+cu_n) u|^2 · |b_L^{-1/2}(z+cu_n) v|^2`,

which is the Cauchy-Schwarz step `b^{1/2} b^{-1/2}` of the proof of `e.RHS.term3.A` with
`u = (nabla w)_{z'+cu_k}` and `v = (a_{L'}nabla(u_m - u_{n,z}))_{z+cu_n}`, the
left factor being `translatedBlockHalfWeight` and the right factor
the new `translatedBlockHalfWeightInv`. -/
theorem translatedBlock_insertion [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (omega : ShellSeq d) (z : TriadicCube d) (u v : Vec d) :
    vecDot u v ^ 2 ≤
      vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u) *
        translatedBlockHalfWeightInv nu L omega z v := by
  have hpsd : (translatedCoarseBlock nu L omega z).PosSemidef :=
    (posDef_translatedCoarseBlock hnu L omega z).posSemidef
  have hdet : IsUnit (translatedCoarseBlock nu L omega z).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_translatedCoarseBlock hnu L omega z)
  have hsymm : (CFC.sqrt (translatedCoarseBlock nu L omega z)).IsSymm :=
    posSemidef_sqrt_isSymm _
  have hBB : CFC.sqrt (translatedCoarseBlock nu L omega z) *
      CFC.sqrt (translatedCoarseBlock nu L omega z) = translatedCoarseBlock nu L omega z :=
    posSemidef_sqrt_mul_self hpsd
  have hBT : matTranspose (CFC.sqrt (translatedCoarseBlock nu L omega z)) =
      CFC.sqrt (translatedCoarseBlock nu L omega z) := by
    simpa [matTranspose] using hsymm.eq
  have hcomm : ∀ w : Vec d,
      vecDot (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u) w =
        vecDot u (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) w) := by
    intro w
    rw [vecDot_matVecMul_transpose u (CFC.sqrt (translatedCoarseBlock nu L omega z)) w,
      hBT]
  have hkey : vecDot (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u)
        (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
          (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v)) = vecDot u v := by
    calc vecDot (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u)
          (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
            (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v))
        = vecDot u (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
            (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
              (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v))) := hcomm _
      _ = vecDot u (matVecMul
            (CFC.sqrt (translatedCoarseBlock nu L omega z) *
              CFC.sqrt (translatedCoarseBlock nu L omega z))
            (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v)) := by
          rw [matVecMul_mul]
      _ = vecDot u (matVecMul (translatedCoarseBlock nu L omega z)
            (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v)) := by
          rw [hBB]
      _ = vecDot u v := by
          rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hdet, matVecMul_one]
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq
    (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u)
    (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z))
      (matVecMul (translatedCoarseBlock nu L omega z)⁻¹ v))
  rw [hkey] at hcs
  refine hcs.trans_eq ?_
  rw [translatedBlockHalfWeightInv, translatedBlockInvSqrt, ← matVecMul_mul]

/-- **`hInsertCS` of the term-3.B assembly, as a square-root form.**  The
pointwise Cauchy-Schwarz inequality — the inequality that carries the
`hInsertCS` binder — holds at these carriers
for *any* vectors: taking the square root of the insertion
`translatedBlock_insertion` (valid because both factors are nonnegative) gives
`u·v <= |b_L^{1/2}(z+cu_n) u|^{1/2·2} |b_L^{-1/2}(z+cu_n) v|^{1/2·2}`, i.e. the
printed product of two half-powers. -/
theorem vecDot_le_sqrt_mul_sqrt [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    (omega : ShellSeq d) (z : TriadicCube d) (u v : Vec d) :
    vecDot u v ≤
      (vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u)) ^
          ((1 : ℝ) / 2) *
        (translatedBlockHalfWeightInv nu L omega z v) ^ ((1 : ℝ) / 2) := by
  have hins := translatedBlock_insertion hnu L omega z u v
  have hX : 0 ≤ vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u) :=
    vecNormSq_nonneg _
  calc vecDot u v ≤ |vecDot u v| := le_abs_self _
    _ = Real.sqrt (vecDot u v ^ 2) := (Real.sqrt_sq_eq_abs (vecDot u v)).symm
    _ ≤ Real.sqrt (vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u) *
          translatedBlockHalfWeightInv nu L omega z v) := Real.sqrt_le_sqrt hins
    _ = Real.sqrt (vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u)) *
          Real.sqrt (translatedBlockHalfWeightInv nu L omega z v) :=
        Real.sqrt_mul hX (translatedBlockHalfWeightInv nu L omega z v)
    _ = (vecNormSq (matVecMul (CFC.sqrt (translatedCoarseBlock nu L omega z)) u)) ^
            ((1 : ℝ) / 2) *
          (translatedBlockHalfWeightInv nu L omega z v) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **The insertion at the printed vectors.**  The inequality is *verbatim* the
conclusion shape of the `hInsertCS` binder: the first factor is
`translatedBlockHalfWeight`
with `u = (nabla w)_{z'+cu_k}` (`z' = q.1`) and the second is the new
`translatedBlockHalfWeightInv` with `v = (a_{L'}(nabla u_m - nabla u_{n,z}))_{z+cu_n}`
(`z = q.2`).  So `hInsertCS` holds as soon as its `normFlux` is named as the
printed inverse half weight, which is exactly the identification
`translatedBlockHalfWeightInv` supplies. -/
theorem insertCS_of_volumeAverage [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)} (S : ScaleSelection) (e : Vec d)
    {U : Set (Vec d)} (w : ShellSeq d → H10Function U) (omega : ShellSeq d)
    (z' z : TriadicCube d) :
    vecDot (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))
        (volumeAverageVec (openCubeSet z)
          (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y))) ≤
      (translatedBlockHalfWeight nu S.LPrime w omega z' z) ^ ((1 : ℝ) / 2) *
        (translatedBlockHalfWeightInv nu S.LPrime omega z
          (volumeAverageVec (openCubeSet z)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) ^ ((1 : ℝ) / 2) := by
  have h := vecDot_le_sqrt_mul_sqrt hnu S.LPrime omega z
    (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))
    (volumeAverageVec (openCubeSet z)
      (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m
            (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega y)))
  rwa [← translatedBlockHalfWeight] at h

end

end SuperdiffusionCLT.Section3.Terms
