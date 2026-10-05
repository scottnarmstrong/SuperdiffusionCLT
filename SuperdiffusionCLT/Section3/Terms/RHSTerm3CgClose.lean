/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.EnergyMapsWiring
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCgB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Wiring

/-!
# `term3_cgBound_close`: `_hCgBound` at the statement's own carriers

The display `e.RHS.term3.A` of the paper
(the label `e.RHS.term3.C` does not exist; the two labels of the
term-3 step are `e.RHS.term3.B` and `e.RHS.term3.A`)
is the second term of `e.additivity.defect.splitting`, estimated in
Step 2 of the proof of `e.RHS.term3`.

The binder `_hCgBound` of the term-3 final assembly is that
display verbatim: its left member averages `∇w` and the flux
`a_{L'}(∇u_m − ∇u_{n,z})` over the sub-cubes `z + cu_n` of `cu_m` and expects
their pairing, and its right member is the printed Cauchy-Schwarz product
`(avsum_{z',z} |b_{L'}^{1/2}(z+cu_n) (∇w)_{z'+cu_k}|²)^{1/2} (δ+η_L)^{1/2}`
plus the printed difference term `Cerr 3^{-(ℓ'−ℓ)/4} (L')² ν^{-5/2}`.

`term3_cgBound_close` below proves exactly that display from the
statement's own binders plus the residual package described
in its docstring.  What is *discharged* on the way, with no hypothesis of its
own:

* the four scale side conditions `hell`, `hnk`, `hkm`, `hLP` of
  `cg_bound_bridge` (in `RHSTerm3OscCgB.lean`) follow from `ScalesOrdering S`
  and `coarse_block_scale_choice`;
* the two insertion steps `hInsertCS`, `hInsertDiff` are
  `insertCS_of_volumeAverage` and `vecDot_le_sqrt_mul_sqrt`
  (both in `RHSTerm3CgSteps.lean`), the printed Cauchy-Schwarz in the metric of the
  invertible coarse block `b_{L'}(z+cu_n)`
  (`posDef_translatedCoarseBlock`, in `RHSTerm3CgSteps.lean`);
* the ellipticity display `hEllip` is
  `translatedBlockNorm_sqMoment_envelope` (in `RHSTerm3CgInputs.lean`), whose
  constant is the dimension-only `bEllipConst d`;
* the Hölder pair `hHolder` is
  `holderPair_translatedBlockHalfWeightDiff` (in `RHSTerm3CgInputsB.lean`);
* the flux-additivity estimate `hFluxAdd` is
  `hFluxAdd_of_maximizers` (in `EnergyMapsWiring.lean`), i.e. the energy-map
  display `e.energymaps.nonsymm.flux` at the pinned glued carriers
  (`gluedMaximizerGrad`/`gluedSubcubeGrad`/`gluedFluxNorm`) together with the
  printed package `e.additivity.error.superdiff`;
* the sample-side nonnegativities `hnfnn`, `hbDnn`, `hbNnn` are `vecNormSq`
  nonnegativity and `matrixOperatorNorm_nonneg`.

The carriers of the assembly are *pinned* to the statement's own objects:
`uMgrad` and `uNGlued` are the two `gluedGradientField` occurrences of
`_hCgBound` at scales `S.m S.m` and `S.n S.m`, `normFlux` is their inverse half
weight (`gluedFluxNorm`, identified with the printed
`|b_{L'}^{-1/2}(z+cu_n)(a_{L'}∇(u_m−u_{n,z}))_{z+cu_n}|²` by
`gluedFluxNorm_eq`), `bHalfDiff` is `translatedBlockHalfWeightDiff` and
`bNormSq` is the squared coarse-block norm.

## What is *not* discharged

The residual package is the printed steps that have no carrier here.  It is
carried verbatim as the last group of binders of `term3_cgBound_close`; every
entry is listed in the file's final section.

## Main results

* `gluedFluxNorm_eq`: the pinned flux carrier read in the raw `gluedGradientField`
  spelling of `_hCgBound`.
* `term3_cgBound_close`: the display `_hCgBound` verbatim.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ} {nu : ℝ}

/-! ## 1. The pinned carriers, in the raw spelling of `_hCgBound` -/

/-- **`gluedFluxNorm` in the raw `gluedGradientField` spelling.**  The pinned
carrier `gluedFluxNorm` (in `EnergyMapsWiring.lean`) is the printed
`|b_{L'}^{-1/2}(z+cu_n)(a_{L'}∇(u_m−u_{n,z}))_{z+cu_n}|²`; written
out, it is the inverse half weight of the averaged flux
`a_{L'}(∇u_m − ∇u_{n,z})` at the two `gluedGradientField` occurrences of scales
`S.m S.m` and `S.n S.m` that `_hCgBound` itself displays. -/
theorem gluedFluxNorm_eq (hnu : 0 < nu) (S : ScaleSelection) (F : Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) :
    gluedFluxNorm hnu S F omega R =
      translatedBlockHalfWeightInv nu S.LPrime omega R
        (volumeAverageVec (openCubeSet R)
          (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
            (gluedGradientField hnu S.LPrime S.m S.m F omega y -
              gluedGradientField hnu S.LPrime S.n S.m F omega y))) := rfl

/-! ## 2. The display `_hCgBound` at the statement's own carriers

The conclusion is the binder `_hCgBound` of the term-3 final assembly
verbatim.  The binders before the residual
package are exactly the statement's own: the dimension and its bound
`2 ≤ d`, the cutoff ellipticity `ν` with `ν ≤ 1`, the shell laws, the scale
selection with its ordering and its three numeric binders, the unit vector `e`,
the smallness carriers `δ`, `η_L` with their nonnegativity, the response `w`
with its Dirichlet clause, and the named constant `Cerr` of the display.

The residual package after `Cerr` is the printed argument of
`e.RHS.term3.A` that no carrier here supplies; it is described entry by entry in section 3. -/
theorem term3_cgBound_close
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (_hTwoHLeM : 2 * S.h ≤ S.m) (_hHundredALeH : 100 * S.a ≤ S.h)
    (_hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (e : Vec d) (he : vecNormSq e = 1)
    (delta etaL : ℝ) (_hdelta : 0 ≤ delta) (_hetaL : 0 ≤ etaL)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (_hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (Cerr : ℝ)
    (Cp Cw : ℝ) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw)
    (hessianL4 : ShellSeq d → ℝ)
    (hde1 : delta + etaL ≤ 1)
    (hCerr : cgBoundConst Cp Cw (bEllipConst d) ≤ Cerr)
    (hFluxInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega R) P.toMeasure)
    (hEnergyIntDiff : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
            (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hJsubInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
          (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R) P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e)
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hEnergyCube : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d S.n S.m,
      IntegrableOn (fun y => -(nu / 2) * vecNormSq
          (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
        vecDot (fluxSlot nu S.LPrime P S.n e)
          (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))
        (cubeSet R) volume)
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL)
    (hMemDiff : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hXmeas : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      AEMeasurable (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu S.LPrime w omega q.1 q.2) P.toMeasure)
    (hPoincare : (((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            ∫ omega : ShellSeq d,
              vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
                  volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
              ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cp * (3 : ℝ) ^ ((coarseBlockScale d S : ℕ) : ℝ) *
        (∫ omega : ShellSeq d, hessianL4 omega ∂P.toMeasure) ^ ((1 : ℝ) / 4))
    (hNablaw : (∫ omega : ShellSeq d, hessianL4 omega ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cw * (3 : ℝ) ^ (-((S.ellPrime : ℕ) : ℝ)) * nu ^ (-(1 : ℝ) / 2))
    (hInt1 : Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
        vecDot (volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure)
    (hInt2 : Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
        vecDot (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y)))) P.toMeasure)
    (hProdCS : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2) *
          gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^
            ((1 : ℝ) / 2)) P.toMeasure)
    (hMembCS : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hProdDiff : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2) *
          gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^
            ((1 : ℝ) / 2)) P.toMeasure)
    (hMembDiff : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        translatedBlockHalfWeightDiff nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hMemf : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  -- the four scale side conditions of the bridge, from the scale ordering
  have hell : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  have hnl : S.n ≤ S.ell := le_of_lt hSorder.n_lt_ell
  obtain ⟨hlk, hkp, -, -⟩ := coarse_block_scale_choice d S hell
  have hnk : S.n ≤ coarseBlockScale d S := le_trans hnl hlk
  have hkm : coarseBlockScale d S ≤ S.m := le_trans hkp (le_of_lt hSorder.ellPrime_lt_m)
  have hLP : 1 ≤ ((S.LPrime : ℕ) : ℝ) := by
    have h : 1 ≤ S.LPrime := lt_of_le_of_lt (Nat.zero_le S.m) hSorder.m_lt_LPrime
    exact_mod_cast h
  -- the sample-side nonnegativities, definitional in the pinned carriers
  have hnfnn : ∀ (omega : ShellSeq d) (z : TriadicCube d),
      0 ≤ gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega z := by
    intro omega z
    rw [gluedFluxNorm_eq hnu S (fluxSlot nu S.LPrime P S.n e) omega z]
    exact translatedBlockHalfWeightInv_nonneg nu S.LPrime omega z _
  have hbDnn : ∀ (omega : ShellSeq d) (z' z : TriadicCube d),
      0 ≤ translatedBlockHalfWeightDiff nu S.LPrime w omega z' z :=
    fun omega z' z => translatedBlockHalfWeightDiff_nonneg S.LPrime w omega z' z
  have hbNnn : ∀ omega : ShellSeq d,
      0 ≤ translatedBlockNorm nu S.LPrime omega (originCube d (S.n : ℤ)) ^ (2 : ℝ) :=
    fun omega => Real.rpow_nonneg
      (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _) 2
  -- the printed ellipticity display, at the dimension-only constant
  have hEllip :
      (∫ omega : ShellSeq d,
        translatedBlockNorm nu S.LPrime omega (originCube d (S.n : ℤ)) ^ (2 : ℝ)
          ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
        bEllipConst d * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((1 : ℝ) / 2) :=
    translatedBlockNorm_sqMoment_envelope hnu hnu1 hPrefix hJ2 hJ3 hJ4 S.LPrime hLP
      (originCube d (S.n : ℤ))
  -- the printed Hoelder pair, at the difference carrier
  have hHolder := holderPair_translatedBlockHalfWeightDiff hnu hPrefix hJ2 hJ3 hJ4
    S.LPrime w hnk hkm (zc := originCube d (S.n : ℤ)) rfl hMemDiff hXmeas
  -- the printed insertion (Cauchy-Schwarz in the coarse-block metric)
  have hInsertCS : ∀ omega : ShellSeq d,
      ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      vecDot (volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y))) ≤
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2) *
          gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2) := by
    intro omega q _
    rw [gluedFluxNorm_eq hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2]
    exact insertCS_of_volumeAverage (P := P) hnu S e w omega q.1 q.2
  -- the printed insertion for the difference term
  have hInsertDiff : ∀ omega : ShellSeq d,
      ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      vecDot (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (gluedGradientField hnu S.LPrime S.m S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y -
                gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega y))) ≤
        translatedBlockHalfWeightDiff nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2) *
          gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2 ^ ((1 : ℝ) / 2) := by
    intro omega q _
    rw [gluedFluxNorm_eq hnu S (fluxSlot nu S.LPrime P S.n e) omega q.2]
    exact vecDot_le_sqrt_mul_sqrt (d := d) hnu S.LPrime omega q.2
      (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
        volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
      (volumeAverageVec (openCubeSet q.2)
        (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y)))
  -- the flux-additivity estimate, from the energy-map layer
  have hFluxAdd := hFluxAdd_of_maximizers (d := d) (P := P) hnu hPrefix hJ2 hJ3 hJ4 S he
    hFluxInt hEnergyIntDiff hAnnealedSub hAnnealedBig hJsubInt hEnergyInt hEnergyCube hPigeon
  have hmain := cg_bound_bridge (d := d) hd hnu hnu1 P S hell hnk hkm hLP w
    (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
    (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e))
    (gluedFluxNorm hnu S (fluxSlot nu S.LPrime P S.n e))
    (translatedBlockHalfWeightDiff nu S.LPrime w)
    (fun omega => translatedBlockNorm nu S.LPrime omega (originCube d (S.n : ℤ)) ^ (2 : ℝ))
    hessianL4
    (delta := delta) (etaL := etaL) (Cb := bEllipConst d) (Cp := Cp) (Cw := Cw)
    (bEllipConst_nonneg d) hCp hCw hde1 hnfnn hbDnn hbNnn hFluxAdd hInsertCS hInsertDiff
    hHolder hEllip hPoincare hNablaw hInt1 hInt2 hProdCS hMembCS hProdDiff hMembDiff hMemf
  exact cgBound_mono (Cerr := cgBoundConst Cp Cw (bEllipConst d)) (Cerr' := Cerr)
    hnu P S e w hCerr hmain

/-! ## 3. The residual package, entry by entry

Every binder of `term3_cgBound_close` after `Cerr` is an entry of the list
below.  None has a carrier here; each is named in the docstring of
`term3_cgBound_close` as a plain argument, not as a bundled proposition.

* `Cp`, `hCp`, `Cw`, `hCw`, `hessianL4`, `hPoincare`, `hNablaw` — the
  multiscale Poincaré step and the Hessian display
  `e.nablaw.Lt`, at the carrier `hessianL4` and the amplitudes
  `Cp`, `Cw`.  `hNablaw` is *blocked* at a constant free of the scale
  selection: the fourth-moment form carries the window factor
  `(1 + h)^{1/2}` on the amplitude of the clause of `e.nablaw.Lt`, which no decaying
  rate on the right side can pay for (see `RHSTerm3CgAssemblyB.lean`), so the printed
  `C_w` is not available and the amplitudes are carried.
* `hde1` — the numeric premise `δ + η_L ≤ 1` of `w_average_difference`
  (in `RHSTerm3StepsC.lean`), i.e. of the difference term of the proof.
  The statement carries only `0 ≤ δ`, `0 ≤ η_L`; it is derived
  from the printed `c⋆ ≤ 2` and the root's conditions in
  `RHSTerm3CgPremise.lean`.
* `hCerr` — the comparison `cgBoundConst Cp Cw (bEllipConst d) ≤ Cerr` between
  the constant produced by the printed argument (one
  dimension-only `C`) and the statement's named `Cerr`.  Without it the
  display is not a theorem: its right side is affine in `Cerr` with the
  positive slope `3^{-(ℓ'−ℓ)/4}(L')²ν^{-5/2}` (`cgBound_mono`,
  in `RHSTerm3Wiring.lean`), so a free `Cerr` has false instances.
* `hFluxInt`, `hEnergyIntDiff` — the integrability side conditions of the
  flux-additivity display.
* `hAnnealedSub`, `hAnnealedBig` — the annealed response values
  `e.homs.defs.U` at the glued carriers.
* `hJsubInt`, `hEnergyInt`, `hEnergyCube` — the integrability bundle of
  `e.additivity.error.superdiff`.
* `hPigeon` — the pigeonhole input `e.pigeon.scalar`.
* `hMemDiff`, `hXmeas` — the membership and measurability side conditions of
  the Hölder pair.
* `hInt1`, `hInt2` — the integrability of the two halves of
  `e.w-flux-indepen-decomp`.
* `hProdCS`, `hMembCS`, `hProdDiff`, `hMembDiff`, `hMemf` — the membership
  side conditions of the two Cauchy-Schwarz steps.
-/

end

end SuperdiffusionCLT.Section3.Terms
