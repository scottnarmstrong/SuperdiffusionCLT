/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.LHSSandwichInputsB
public import SuperdiffusionCLT.Section3.Terms.NeumannRealizationInputs
public import SuperdiffusionCLT.Section3.Terms.StationaryRealization

/-!
# `l.LHS.term1` after the stationary realization assumption

This file proves `l.LHS.term1` from one named input: the conclusion of the
stationary-potential realization statement, with its two product
measurability conjuncts omitted.  `StationaryRealization` reconstructs those
two conjuncts, and `NeumannRealizationInputs` supplies the Neumann energy
measurability for the concrete flux.  The result below has the
`l.LHS.term1` conclusion verbatim.
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

/-- **The `l.LHS.term1` conclusion from the stationary realization statement.**

The only additional premise beyond the printed statement is
`hStationaryAnchor`, exactly the conclusion of that statement after specializing the
carrier, flux, and cube.  Its output contains the cube `H¹` realization,
translated-gradient identity, and interior weak equation.  The two joint
measurability conjuncts are reconstructed by
`hReal_of_energyRealization`; the Neumann energy measurability is reconstructed
by `aesm_vecCubeLpENorm_grad_neumann_of_fluxFormula`.
-/
theorem lhs_term1_of_stationaryAnchor
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
                (hStationaryAnchor : ∀ (gradHatW : ShellSeq d → Vec d)
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
  obtain ⟨C, hC, hmain⟩ :=
    lhs_term1_of_neumannMeas_of_realization d hd
  refine ⟨C, hC, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder e he
    hunit p hp F hF w hwD hStationaryAnchor
  have hNmeas : ∀ (wN : ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
      (∀ omega : ShellSeq d,
        IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega)) →
      AEStronglyMeasurable (fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wN omega).toH1Function.grad) P.toMeasure := by
    intro wN hwN
    exact aesm_vecCubeLpENorm_grad_neumann_of_fluxFormula S p F hF hwN
  have hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure :=
    ShellField.vaddInvariantMeasure hPrefix hJ2
  have hReal := hReal_of_energyRealization d P hInv S F hStationaryAnchor
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 cStar K hJ5 S hSorder
    e he hunit p hp F hF w hwD hNmeas hReal

end

end SuperdiffusionCLT.Section3.Terms
