/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCg

/-!
# `hCgBound`: the coarse-grained average term of `l.RHS.term3`

The display is `e.RHS.term3.A` of the paper, together with its proof.

`Section3/Terms/RHSTerm3StepsC.lean` proves `rhs_term3_A`, whose conclusion is
exactly the binder `_hCgBound` of the term-3 statement at
`k = coarseBlockScale d S` and `bHalfW = translatedBlockHalfWeight ν L' w`.  Its
two inputs are discharged here:

* `hCS` from `coarse_average_CS` (`Section3/Terms/RHSTerm3StepsB.lean`), the
  Cauchy-Schwarz step of the proof of `e.RHS.term3.A` against the normalized flux
  defect;
* `hDiff` from `w_average_difference` (`Section3/Terms/RHSTerm3StepsC.lean`),
  `l.RHS.term3#w-average-difference`, at
  `C_err = cgBoundConst Cp Cw Cb = 3C_PC_wC_b`.

`hDiff` is **not** `e.flux-additivity-estimate-in-an-lemma`; that estimate
is proved as `flux_additivity_estimate`
(`Section3/Terms/RHSTerm3StepsB.lean`) and its conclusion is the input
`hFluxAvg` shared by the two halves of `e.w-flux-indepen-decomp`.  Here it is
carried as the single named hypothesis `hFluxAdd` in its printed shape;
`flux_additivity_estimate` reduces it to `e.energymaps.nonsymm.flux` on the
difference of two maximizers and to `additivity_error_superdiff`.

## Main results

* `cgBoundConst`, `cg_bound_bridge`: `_hCgBound` in its exact shape, with both
  inputs of `rhs_term3_A` discharged.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
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

/-! ## `hCgBound` -/

/-- The constant `C_err` of `e.RHS.term3.A` produced by `cg_bound_bridge`: the
constant `3C_PC_wC_b` of `w_average_difference`. -/
def cgBoundConst (Cp Cw Cb : ℝ) : ℝ := 3 * (Cp * Cw * Cb)

/-- **`hCgBound` of the term-3 statement**, i.e.
`e.RHS.term3.A`, with
**both** inputs of `rhs_term3_A` discharged.

* `hCS` of `rhs_term3_A` is the conclusion of `coarse_average_CS`
  (`Section3/Terms/RHSTerm3StepsB.lean`), the elementary Cauchy-Schwarz step of
  the proof of `e.RHS.term3.A`, at `bHalfW = translatedBlockHalfWeight ν L' w`; its
  nonnegativity binder is discharged here, because
  `translatedBlockHalfWeight` is by definition a `vecNormSq`.
* `hDiff` of `rhs_term3_A` is the conclusion of `w_average_difference`
  (`Section3/Terms/RHSTerm3StepsC.lean`), `l.RHS.term3#w-average-difference`, at
  `C_err = 3C_PC_wC_b`.

The hypotheses that remain are exactly the printed steps carried as hypotheses:

* `hFluxAdd` — `e.flux-additivity-estimate-in-an-lemma` in the
  form carried by `flux_additivity_estimate` (`Section3/Terms/RHSTerm3StepsB.lean`),
  `avsum_z E[|b_{L'}^{-1/2}(z+cu_n)(a_{L'}∇(u_m−u_{n,z}))_{z+cu_n}|²] ≤ δ + η_L`.
  It is the single input shared by the two halves of the decomposition
  `e.w-flux-indepen-decomp`.  `flux_additivity_estimate` reduces it to
  `e.energymaps.nonsymm.flux` applied to the difference of two maximizers and
  to `additivity_error_superdiff`; here the estimate is carried as one named
  hypothesis in its printed shape.
* `hInsertCS`, `hInsertDiff` — the `b_{L'}^{±1/2}` insertion in the
  proof of `e.RHS.term3.A`, applied to the two halves; the paper does not remark
  on the invertibility of `b_{L'}(z+cu_n)` that it needs.
* `hHolder`, `hEllip`, `hPoincare`, `hNablaw` — the four steps of the proof of
  `l.RHS.term3#w-average-difference` carried by `w_average_difference`.

The free binders are the ones of `coarse_average_CS` and
`w_average_difference`: `normFlux ω z` is the printed
`|b_{L'}^{-1/2}(z+cu_n)(a_{L'}∇(u_m−u_{n,z}))_{z+cu_n}|²`, `bHalfDiff ω z' z`
the printed `|b_{L'}^{1/2}(z+cu_n)((∇w)_{z+cu_n} − (∇w)_{z'+cu_k})|²`,
`bNormSq ω` is `|b_{L'}(cu_n)|²` and `hessianL4 ω` is `‖∇²w‖⁴_{L̲⁴(cu_m)}`. -/
theorem cg_bound_bridge
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hell : S.ell ≤ S.ellPrime) (hnk : S.n ≤ coarseBlockScale d S)
    (hkm : coarseBlockScale d S ≤ S.m) (hLP : 1 ≤ ((S.LPrime : ℕ) : ℝ))
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (normFlux : ShellSeq d → TriadicCube d → ℝ)
    (bHalfDiff : ShellSeq d → TriadicCube d → TriadicCube d → ℝ)
    (bNormSq hessianL4 : ShellSeq d → ℝ)
    {delta etaL Cb Cp Cw : ℝ} (hCb : 0 ≤ Cb) (hCp : 0 ≤ Cp) (hCw : 0 ≤ Cw)
    (hde1 : delta + etaL ≤ 1)
    (hnfnn : ∀ (omega : ShellSeq d) (z : TriadicCube d), 0 ≤ normFlux omega z)
    (hbDnn : ∀ (omega : ShellSeq d) (z' z : TriadicCube d), 0 ≤ bHalfDiff omega z' z)
    (hbNnn : ∀ omega : ShellSeq d, 0 ≤ bNormSq omega)
    (hFluxAdd : ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d S.n S.m,
          ∫ omega : ShellSeq d, normFlux omega z ∂P.toMeasure ≤ delta + etaL)
    (hInsertCS : ∀ omega : ShellSeq d,
      ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      vecDot (volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) ≤
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2) *
          normFlux omega q.2 ^ ((1 : ℝ) / 2))
    (hInsertDiff : ∀ omega : ShellSeq d,
      ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      vecDot (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y))) ≤
        bHalfDiff omega q.1 q.2 ^ ((1 : ℝ) / 2) * normFlux omega q.2 ^ ((1 : ℝ) / 2))
    (hHolder : (((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            ∫ omega : ShellSeq d, bHalfDiff omega q.1 q.2 ∂P.toMeasure) ^ ((1 : ℝ) / 2) ≤
      (((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
            ∫ omega : ShellSeq d,
              vecNormSq (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
                  volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
              ∂P.toMeasure) ^ ((1 : ℝ) / 4) *
        (∫ omega : ShellSeq d, bNormSq omega ∂P.toMeasure) ^ ((1 : ℝ) / 4))
    (hEllip : (∫ omega : ShellSeq d, bNormSq omega ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
      Cb * (((S.LPrime : ℕ) : ℝ) * nu⁻¹) ^ ((1 : ℝ) / 2))
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
              (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hInt2 : Integrable (fun omega : ShellSeq d =>
      ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
        vecDot (volumeAverageVec (openCubeSet q.2) ((w omega).toH1Function.grad) -
            volumeAverageVec (openCubeSet q.1) ((w omega).toH1Function.grad))
          (volumeAverageVec (openCubeSet q.2)
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
              (uMgrad omega y - uNGlued omega y)))) P.toMeasure)
    (hProdCS : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2) *
          normFlux omega q.2 ^ ((1 : ℝ) / 2)) P.toMeasure)
    (hMembCS : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d =>
        translatedBlockHalfWeight nu S.LPrime w omega q.1 q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hProdDiff : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      Integrable (fun omega : ShellSeq d =>
        bHalfDiff omega q.1 q.2 ^ ((1 : ℝ) / 2) * normFlux omega q.2 ^ ((1 : ℝ) / 2))
        P.toMeasure)
    (hMembDiff : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d => bHalfDiff omega q.1 q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure)
    (hMemf : ∀ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
      MemLp (fun omega : ShellSeq d => normFlux omega q.2 ^ ((1 : ℝ) / 2))
        (ENNReal.ofReal (2 : ℝ)) P.toMeasure) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        cgBoundConst Cp Cw Cb * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  have hbWnn : ∀ (omega : ShellSeq d) (z' z : TriadicCube d),
      0 ≤ translatedBlockHalfWeight nu S.LPrime w omega z' z := by
    intro omega z' z
    exact vecNormSq_nonneg _
  have hCS := coarse_average_CS P S hnk hkm w uMgrad uNGlued
    (translatedBlockHalfWeight nu S.LPrime w) normFlux hbWnn hnfnn hInsertCS
    hFluxAdd hInt1 hProdCS hMembCS hMemf
  have hDiff := w_average_difference hd hnu hnu1 P S hell hnk hkm hLP w uMgrad uNGlued
    bHalfDiff normFlux bNormSq hessianL4 hCb hCp hCw hde1 hbDnn hnfnn hbNnn
    hInsertDiff hFluxAdd hHolder hEllip hPoincare hNablaw hInt2 hProdDiff hMembDiff
    hMemf
  simp only [cgBoundConst]
  exact rhs_term3_A P S hnk hkm w uMgrad uNGlued (translatedBlockHalfWeight nu S.LPrime w)
    hCS hDiff hInt1 hInt2

/-! ## `l.RHS.term3` from the anchors, with `hCgBound` discharged -/

end

end SuperdiffusionCLT.Section3.Terms
