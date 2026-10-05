/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.LHSTerm1Assembly
public import SuperdiffusionCLT.Section3.Terms.LHSSandwichInputs

/-!
# The LHS term after the available sandwich inputs are discharged

`LHSSandwichInputs.lean` supplies the invariant measure, the projection
representative, the Neumann response, the stationarity cocycle, and the
Dirichlet energy measurability.  This module feeds that result into
`lhs_of_sandwich`, so the existential `hSandwich` is no longer a premise of
the resulting LHS statement.

The remaining premises are kept explicit.  They are the Neumann energy
measurability transfer for the selected response and the realization of the
stationary potential gradient on the cube.  The latter is the realization
conjunct carried by the Section 3 structural input; neither premise is
silently replaced by a definition or by an additional theorem hypothesis of
the statement.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped BigOperators ENNReal

noncomputable section

/-- The conclusion of `l.LHS.term1` with the sandwich existential removed, assuming
the two structural inputs that remain after the available response-field data
are assembled. -/
theorem lhs_term1_of_neumannMeas_of_realization
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P), ShellLawJ1Restriction d P →
          ∀ (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P), ShellLawJ4 d P →
          ∀ (cStar K : ℝ), ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ (S : ScaleSelection), ScalesOrdering S →
          ∀ (e : Vec d), Homogenization.vecNormSq e = 1 →
            Homogenization.Book.Ch02.vecNorm e = 1 →
            ∀ (p : Vec d), p = testVector nu S.LPrime P S.n e →
            ∀ (F : ShellSeq d → Vec d → Vec d),
              (∀ omega : ShellSeq d, F omega = fun x =>
                Homogenization.matVecMul
                  (SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.LPrime x -
                    SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.ellPrime x) p) →
              ∀ (w : ShellSeq d →
                  Homogenization.H10Function
                    (Homogenization.openCubeSet
                      (Homogenization.originCube d (S.m : ℤ)))),
                (∀ omega : ShellSeq d,
                  IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega)
                    (w omega)) →
                (hNmeas : ∀ (wN : ShellSeq d →
                    H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
                  (∀ omega : ShellSeq d,
                    IsCubeNeumannResponse (originCube d (S.m : ℤ))
                      (F omega) (wN omega)) →
                  AEStronglyMeasurable (fun omega : ShellSeq d =>
                    vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                      (wN omega).toH1Function.grad) P.toMeasure) →
                (hReal : ∀ (gradHatW : ShellSeq d → Vec d)
                    (hFmemLp : MemLp (fun omega : ShellSeq d =>
                      HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
                    (hGmemLp : MemLp (fun omega : ShellSeq d =>
                      HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
                  (hGmemLp.toLp (fun omega : ShellSeq d =>
                      HilbertVec.ofVec (gradHatW omega))) =
                    -@stationaryPotentialProjection d (ShellSeq d) _
                      P.toMeasure _ _
                      (ShellField.vaddInvariantMeasure hPrefix hJ2)
                      (hFmemLp.toLp (fun omega : ShellSeq d =>
                        HilbertVec.ofVec (F omega 0))) →
                  ∃ uReal : ShellSeq d →
                    H1Function (openCubeSet (originCube d (S.m : ℤ))),
                    (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
                        HilbertVec.ofVec (gradHatW (z.2 +ᵥ z.1)))
                      (P.toMeasure.prod
                        (normalizedCubeMeasure (originCube d (S.m : ℤ))))) ∧
                    (AEStronglyMeasurable (fun z : ShellSeq d × Vec d =>
                        HilbertVec.ofVec (F (z.2 +ᵥ z.1) 0))
                      (P.toMeasure.prod
                        (normalizedCubeMeasure (originCube d (S.m : ℤ))))) ∧
                    (∀ᵐ omega ∂P.toMeasure,
                      (uReal omega).grad =ᵐ[volumeMeasureOn
                          (openCubeSet (originCube d (S.m : ℤ)))]
                        fun x => gradHatW (x +ᵥ omega)) ∧
                    (∀ᵐ omega ∂P.toMeasure, ∀ phi : H10Function
                        (openCubeSet (originCube d (S.m : ℤ))),
                      ∫ x in openCubeSet (originCube d (S.m : ℤ)),
                          vecDot ((uReal omega).grad x)
                            (phi.toH1Function.grad x) =
                        -∫ x in openCubeSet (originCube d (S.m : ℤ)),
                          vecDot (F omega x) (phi.toH1Function.grad x))) →
                |(∫⁻ omega : ShellSeq d,
                      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
                        (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                  ℝ≥0∞).toReal -
                  cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
                (C * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p := by
  obtain ⟨Clhs, hClhs, hmain⟩ := lhs_of_sandwich d hd
  refine ⟨Clhs, hClhs, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder e he
    hunit p hp F hF w hwD hNmeas hReal
  have hp_smul : p = sigmaBarStarInvSqrt nu S.LPrime P S.n • e := by
    calc
      p = testVector nu S.LPrime P S.n e := hp
      _ = sigmaBarStarInvSqrt nu S.LPrime P S.n • e :=
        testVector_eq_smul nu S.LPrime P S.n e
  have hSandwich := lhs_sandwich_of_neumannMeas_of_realization d hd P hPrefix hJ2
    hJ3 S hSorder e hunit (sigmaBarStarInvSqrt nu S.LPrime P S.n) p hp_smul F hF
    w hwD hNmeas hReal
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder e
    he hunit p hp F hF w hwD hSandwich

end

end SuperdiffusionCLT.Section3.Terms
