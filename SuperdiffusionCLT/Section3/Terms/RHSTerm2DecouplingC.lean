/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2DecouplingB

/-!
# `l.RHS.term2` with the proxy fixed to the glued field

`l_RHS_term2_of_anchors` of `RHSTerm2DecouplingB` is
`l_RHS_term2_constFirst` with `hDecouple` discharged, but it carries the glued
proxy as *free* binders — `uTildeGlued : ShellSeq d → Vec d → Vec d` and
`pTilde : Vec d` — and asks for the two proxy inputs `hTint` (integrability in
the sample of the cube means of `uTildeGlued`) and `hmean` (their annealed
value is `pTilde`).  Its module docstring records that both are reachable at
the glued carriers: `hTint` from `integrable_sigmaStarInvCoarse` of
`GluedFieldAverages` through `volumeAverageVec_gluedGradientField`, and
`hmean` from `integral_sigmaStarInvCoarse_openCubeSet_eq` of `GluedField`
at the cutoff level `ℓ`.

This module carries out that observation.  `l_RHS_term2_of_anchors_glued` is
`l_RHS_term2_of_anchors` with the proxy fixed to the glued field of
`GluedField` at the coefficient cutoff `ℓ`,

* `uTildeGlued := gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`,
* `pTilde := annealedGluedAverage hnu P S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`,

and with the two proxy inputs removed: every other binder of
`l_RHS_term2_of_anchors` is kept, in the same order, and the conclusion is the
same estimate.  Concretely, the binders that survive are `d`, the instance
`[NeZero d]`, `hd : 2 ≤ d`, the constants `C₁ C₂ C₃ Cpoin` with
`hC₁ : 1 ≤ C₁`, `hC₂ : 1 ≤ C₂`, `hC₃ : 1 ≤ C₃`, `hCpoin : 0 ≤ Cpoin`, and then
inside the `∃ C` conclusion the chain `nu` (with `0 < nu`, `nu ≤ 1`), `P` (with
`ShellLawPrefix`, `ShellLawJ1Restriction`, `ShellLawJ2`, `ShellLawJ3`, `ShellLawJ4`),
`S` (with `ScalesOrdering`), `e` (with `vecNormSq e = 1`), `p` (with
`p = testVector …`), `w` (with `IsDirichletResponse`), `uNGlued` and `DR` (with
the weak-gradient typing data `hDR`, the two anchor bounds `hRb` and `hPe` and
the proxy anchor `hPen`), `Rfield` (with `hRfield`), `DRmat` (with `hDRmat`),
the four `MemVectorL2` data `hRL2`, `hUL2`, `hUtL2`, `hDRL2`, the four finiteness
hypotheses `hfinR`, `hfinDR`, `hfinDiff`, `hfinProx`, the four `AEMeasurable`
hypotheses `hmR`, `hmDR`, `hmDiff`, `hmProx`, the three integrability
hypotheses `hIntDiff`, `hIntProxy`, `hIntMean`, the Poincaré comparison
`hPoincare`, the measurability hypotheses `hRmeas` and `hTmeas`, and the
integrability hypothesis `hRint` of the cube means of `Rfield`; the two
hypotheses `hTint` and `hmean` are gone, discharged inside the proof by
`integrable_volumeAverageVec_gluedGradientField` and
`integral_volumeAverageVec_gluedGradientField_apply_eq` of
`RHSTerm2DecouplingB`.

One textual deviation from `l_RHS_term2_of_anchors`:
the anonymous hypothesis `0 < nu` of the chain `∀ (nu : ℝ), 0 < nu → nu ≤ 1 →`
is named `hnu`, because the glued proxy field mentions it; `nu ≤ 1` stays
anonymous as in `l_RHS_term2_of_anchors`.  The Pi type is otherwise unchanged.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open ProbabilityTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **`l_RHS_term2_constFirst` with `hDecouple` discharged and the proxy
fixed to the glued field**.  This is `l_RHS_term2_of_anchors` of
`RHSTerm2DecouplingB` with the two proxy binders fixed to the
glued field of `GluedField` at the coefficient cutoff `ℓ`,

* `uTildeGlued := gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`,
* `pTilde := annealedGluedAverage hnu P S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`,

and the two proxy inputs `hTint` and `hmean` removed; every other binder stands
in the same order and the conclusion is the same estimate.  The proof is
`l_RHS_term2_of_anchors` at that proxy, with `hTint` and `hmean` supplied by
`integrable_volumeAverageVec_gluedGradientField` and
`integral_volumeAverageVec_gluedGradientField_apply_eq` of the same module. -/
theorem l_RHS_term2_of_anchors_glued (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ C₂ C₃ Cpoin : ℝ) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hC₃ : 1 ≤ C₃)
    (hCpoin : 0 ≤ Cpoin) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (p : Vec d), p = testVector nu S.LPrime P S.n e →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) →
      ∀ (uNGlued : ShellSeq d → Vec d → Vec d) (DR : ShellSeq d → Fin d → Vec d → Vec d),
        (∀ omega : ShellSeq d, ∀ i : Fin d,
          HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                  (coefficientCutoff nu omega S.ell).toCoeffField x)
                ((w omega).toH1Function.grad x)) i) (DR omega i)) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                (originCube d (S.m : ℤ)) 2
                (fun x => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                  (coefficientCutoff nu omega S.ell).toCoeffField x)
                  ((w omega).toH1Function.grad x)) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
          (3 : ℝ) ^ ((S.ell : ℕ) : ℝ) *
            (∫⁻ omega : ShellSeq d,
                SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                    (originCube d (S.m : ℤ)) 2
                    (fun x => HilbertMat.ofMat (fun i j => DR omega i x j)) ^
              (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          C₁ * ((S.LPrime : ℕ) : ℝ) * Real.sqrt (vecNormSq p)) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (S.m : ℤ)) 2
                  (fun x => uNGlued omega x -
                    gluedGradientField hnu S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) +
          Real.sqrt (vecNormSq (annealedGluedAverage hnu P S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) - p)) ≤
          C₂ * nu ^ (-((3 : ℝ) / 2)) * ((S.LPrime : ℕ) : ℝ) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) *
            (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
        ((∫⁻ omega : ShellSeq d,
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (S.m : ℤ)) 2
                  (fun x => gluedGradientField hnu S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x -
                    annealedGluedAverage hnu P S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e)) ^
            (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal ^ ((1 : ℝ) / 2) ≤
          C₃ * nu ^ (-(1 : ℝ)) * (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹) →
      ∀ (Rfield : ShellSeq d → Vec d → Vec d),
        (∀ (omega : ShellSeq d) (y : Vec d), Rfield omega y =
          matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
              (coefficientCutoff nu omega S.ell).toCoeffField y)
            ((w omega).toH1Function.grad y)) →
      ∀ (DRmat : ShellSeq d → Vec d → HilbertMat d),
        (∀ (omega : ShellSeq d) (x : Vec d), DRmat omega x =
          HilbertMat.ofMat (fun i j => DR omega i x j)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (Rfield omega)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ))) (uNGlued omega)) →
        (∀ omega : ShellSeq d,
          MemVectorL2 (openCubeSet (originCube d (S.m : ℤ)))
            (gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega)) →
        (∀ omega : ShellSeq d,
          MemLp (DRmat omega) 2
            (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega) ^ (2 : ℕ)
            ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega) ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uNGlued omega x - gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) →
        ((∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e)) ^ (2 : ℕ)
              ∂P.toMeasure) ≠ ⊤) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (Rfield omega)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 2
            (DRmat omega)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => uNGlued omega x - gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x)) P.toMeasure) →
        (AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (uNGlued omega y - gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega y -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e)))) P.toMeasure) →
        (Integrable (fun omega : ShellSeq d =>
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot (Rfield omega y)
              (annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) - p))) P.toMeasure) →
        (∀ (omega : ShellSeq d), ∀ z ∈ largeCubeSubcubes d S.n S.m,
          vecCubeLpENorm z 2
              (fun x => Rfield omega x -
                volumeAverageVec (openCubeSet z) (Rfield omega)) ≤
            ENNReal.ofReal (Cpoin * (3 : ℝ) ^ ((S.n : ℕ) : ℝ)) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm z 2 (DRmat omega)) →
        (∀ z ∈ largeCubeSubcubes d S.n S.m,
          Measurable[highShellSigma d S.ell]
            (fun omega : ShellSeq d =>
              volumeAverageVec (openCubeSet z) (Rfield omega))) →
        (∀ z ∈ largeCubeSubcubes d S.n S.m,
          Measurable[lowShellSigma d S.ell]
            (fun omega : ShellSeq d =>
              volumeAverageVec (openCubeSet z)
                (gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega))) →
        (∀ z ∈ largeCubeSubcubes d S.n S.m, ∀ i : Fin d, Integrable
          (fun omega : ShellSeq d =>
            volumeAverageVec (openCubeSet z) (Rfield omega) i) P.toMeasure) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (uNGlued omega y - p))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) := by

  obtain ⟨C, hC1, hC⟩ := l_RHS_term2_of_anchors d hd C₁ C₂ C₃ Cpoin hC₁ hC₂ hC₃ hCpoin
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
    uNGlued DR hDR hRb hPe hPen Rfield hRfield DRmat hDRmat
    hRL2 hUL2 hUtL2 hDRL2 hfinR hfinDR hfinDiff hfinProx hmR hmDR hmDiff hmProx
    hIntDiff hIntProxy hIntMean hPoincare hRmeas hTmeas hRint
  have hnm : S.n ≤ S.m := hSorder.mem_pigeon_range.1.2
  exact hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
    uNGlued
    (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (annealedGluedAverage hnu P S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) DR
    hDR hRb hPe hPen Rfield hRfield DRmat hDRmat
    hRL2 hUL2 hUtL2 hDRL2 hfinR hfinDR hfinDiff hfinProx hmR hmDR hmDiff hmProx
    hIntDiff hIntProxy hIntMean hPoincare hRmeas hTmeas hRint
    (fun _z hz i => (integrable_volumeAverageVec_gluedGradientField hnu hPrefix hJ2
      hJ3 hJ4 S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e) hz).eval i)
    (fun _z hz i => integral_volumeAverageVec_gluedGradientField_apply_eq hnu hPrefix
      hJ2 hJ3 hJ4 S.ell hnm (fluxSlot nu S.LPrime P S.n e) hz i)

end

end SuperdiffusionCLT.Section3.Terms