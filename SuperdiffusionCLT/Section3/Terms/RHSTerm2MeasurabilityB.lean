/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Measurability

/-!
# `l.RHS.term2` with the proxy half of the measurability sentence discharged

The statement is `l.RHS.term2`; the measurability sentence occurs in its proof.

`l_RHS_term2_of_anchors_constFirst` of `RHSTerm2AnchorsConstFirst.lean` carries
the printed sentence as its last two binders, read on the two cube mean
vectors.  `RHSTerm2Measurability` proves the second of them at the
glued proxy: the cube mean of `gluedGradientField hnu S.ell S.n S.m F` on a
sub-cube is the quenched coarse matrix `s_{ℓ,*}^{-1}` of the cutoff field
`a_ℓ = ν Id + k_ℓ` applied to the flux slot, and `a_ℓ` reads only the shells
`r ≤ ℓ`.  This module removes that binder from the statement.

`hRmeas` stays.  Only the coefficient factor of `R = (k_{L'} − k_ℓ)^t ∇w` is
available (it reads only the shells `r > ℓ`); the response
factor is not.  This is not an artefact of `w` being a free binder, since the
observable is a genuine function of the shell sequence, but no declaration here
makes it measurable.

Everything else in `l_RHS_term2_of_anchors_constFirst` is untouched: the
quantifier order is the paper's own, the conclusion is byte-identical, and
every remaining binder stands unchanged and in the same order.

## Main results

* `l_RHS_term2_of_anchors_proxyMeasurable`: `l_RHS_term2_of_anchors_constFirst`
  with `hTmeas` discharged.
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

/-- **`l_RHS_term2_of_anchors_constFirst` with `hTmeas` discharged**
(the statement is `l.RHS.term2`; the measurability sentence occurs in its proof).

The quantifier order is the paper's own: the dimension, the three input
constants `C₁ C₂ C₃` and their lower bounds stand first, then one `C`, and only
then the scale `nu`, the shell law `P`, the scale selection `S`, the direction
`e`, the response field `w` and the glued fields.

Every binder of `l_RHS_term2_of_anchors_constFirst` stands, in the same order,
except the last one, `hTmeas`, which the proof supplies from
`measurable_volumeAverageVec_gluedGradientField_lowShellSigma`.  The other half
of the printed sentence, `hRmeas`, remains; the module docstring records why. -/
theorem l_RHS_term2_of_anchors_proxyMeasurable (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (C₁ C₂ C₃ : ℝ) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hC₃ : 1 ≤ C₃) :
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
        (∀ z ∈ largeCubeSubcubes d S.n S.m,
          Measurable[highShellSigma d S.ell]
            (fun omega : ShellSeq d =>
              volumeAverageVec (openCubeSet z) (Rfield omega))) →
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
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2))
    := by
  obtain ⟨C, hC1, hC⟩ := l_RHS_term2_of_anchors_constFirst d hd C₁ C₂ C₃ hC₁ hC₂ hC₃
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
    uNGlued DR hDR hRb hPe hPen Rfield hRfield DRmat hDRmat
    hRL2 hUL2 hUtL2 hDRL2 hfinR hfinDR hfinDiff hfinProx hmR hmDR hmDiff hmProx
    hIntDiff hIntProxy hIntMean hRmeas
  exact hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he p hp w hw
    uNGlued DR hDR hRb hPe hPen Rfield hRfield DRmat hDRmat
    hRL2 hUL2 hUtL2 hDRL2 hfinR hfinDR hfinDiff hfinProx hmR hmDR hmDiff hmProx
    hIntDiff hIntProxy hIntMean hRmeas
    (measurable_volumeAverageVec_gluedGradientField_lowShellSigma hnu S.ell S.n S.m
      (fluxSlot nu S.LPrime P S.n e))

end

end SuperdiffusionCLT.Section3.Terms
