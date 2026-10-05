/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffLocalizationAssembly
public import SuperdiffusionCLT.Section2.Localization.Conj3EndgameMinimizerEnergy

/-!
# The cutoff localization estimate with no hypothesis beyond the dimension

`CutoffLocalizationAssembly.cutoff_localization_proved` consumes exactly one
explicit input, the third conjunct, in the shape

`∀ C, localizationMaxConst d ≤ C → …`,

its conjuncts 1 and 2 being proved internally by
`cutoffLocalizationConjunct1` and `localizationConjunct2_proved`.
`Conj3EndgameMinimizerEnergy.cutoffLocalizationConjunct3_hconj3_minimizerEnergy` supplies
that input binder for binder, carrying nothing beyond the data of the statement: the
shell laws, `nu ≤ 1`, the cube containment, the two maximizer properties, and
`[NeZero d]` / `hd : 2 ≤ d`.

This module applies the two, proving the cutoff localization
estimate, stated here in full, with no hypothesis beyond `d`, `[NeZero d]` and
`hd : 2 ≤ d`.

Everything stays averaged; dimension one is out of scope.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-- **The cutoff localization estimate.** The statement at the binders `d`,
`[NeZero d]`, `hd : 2 ≤ d`, obtained by applying `cutoff_localization_proved` to the closed third
conjunct `cutoffLocalizationConjunct3_hconj3_minimizerEnergy`. No further hypothesis
remains. -/
theorem cutoff_localization_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m n L : ℕ, n ≤ m → m ≤ L →
            ∀ U : Homogenization.Book.Ch02.Domain d,
              (U : Set (Homogenization.Vec d)) ⊆
                  Homogenization.openCubeSet
                    (Homogenization.originCube d (n : ℤ)) →
              (∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X ∧
                  Homogenization.IndependentSums.IsBigO P.toMeasure
                      (Homogenization.IndependentSums.gammaSigma 1) X
                      (C * nu ^ (-(2 : ℝ)) *
                        (3 : ℝ) ^ (-((m - n : ℕ) : ℝ))) ∧
                    ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                      Homogenization.MatLoewnerLE
                          ((1 - X omega) •
                            Homogenization.sigmaCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField)
                          (Homogenization.sigmaCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega m).toCoeffField) ∧
                        Homogenization.MatLoewnerLE
                          (Homogenization.sigmaCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega m).toCoeffField)
                          ((1 + X omega) •
                            Homogenization.sigmaCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega L).toCoeffField) ∧
                        Homogenization.MatLoewnerLE
                          ((1 - X omega) •
                            Homogenization.sigmaStarInvCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega m).toCoeffField)
                          (Homogenization.sigmaStarInvCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega L).toCoeffField) ∧
                        Homogenization.MatLoewnerLE
                          (Homogenization.sigmaStarInvCoarse
                            (U : Set (Homogenization.Vec d))
                            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega L).toCoeffField)
                          ((1 + X omega) •
                            Homogenization.sigmaStarInvCoarse
                              (U : Set (Homogenization.Vec d))
                              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                  nu omega m).toCoeffField)) ∧
                (∃ Y : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable Y ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma 1) Y
                        (C * nu ^ (-(2 : ℝ)) *
                          (3 : ℝ) ^ (-(((m - n : ℕ) : ℝ) / 2))) ∧
                      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                        (p q : Homogenization.Vec d),
                        2 * Homogenization.vecDot p
                            (Homogenization.matVecMul
                              (Homogenization.kappaCoarse
                                  (U : Set (Homogenization.Vec d))
                                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega L).toCoeffField -
                                Homogenization.kappaCoarse
                                  (U : Set (Homogenization.Vec d))
                                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega m).toCoeffField -
                                Homogenization.volumeAverageMat
                                  (U : Set (Homogenization.Vec d))
                                  (fun y =>
                                    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                      omega m L y))
                              q) ≤
                          Y omega *
                            (Homogenization.vecDot p
                                (Homogenization.matVecMul
                                  (Homogenization.sigmaStarCoarse
                                    (U : Set (Homogenization.Vec d))
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L).toCoeffField) p) +
                              Homogenization.vecDot q
                                (Homogenization.matVecMul
                                  (Homogenization.sigmaCoarse
                                    (U : Set (Homogenization.Vec d))
                                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L).toCoeffField) q))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.Vec d)
                    (u : Homogenization.AHarmonicFunction
                      (fun x : Homogenization.Vec d =>
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                              nu omega L).toCoeffField x -
                          Homogenization.volumeAverageMat
                            (U : Set (Homogenization.Vec d))
                            (fun y =>
                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                omega m L y))
                      (U : Set (Homogenization.Vec d)))
                    (v : Homogenization.AHarmonicFunction
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                          nu omega m).toCoeffField
                      (U : Set (Homogenization.Vec d))),
                    (∀ w : Homogenization.AHarmonicFunction
                        (fun x : Homogenization.Vec d =>
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                nu omega L).toCoeffField x -
                            Homogenization.volumeAverageMat
                              (U : Set (Homogenization.Vec d))
                              (fun y =>
                                SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                  omega m L y))
                        (U : Set (Homogenization.Vec d)),
                        Homogenization.volumeAverage
                            (U : Set (Homogenization.Vec d))
                            (Homogenization.scalarResponseIntegrand
                              (U : Set (Homogenization.Vec d))
                              (fun x : Homogenization.Vec d =>
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega L).toCoeffField x -
                                  Homogenization.volumeAverageMat
                                    (U : Set (Homogenization.Vec d))
                                    (fun y =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega m L y))
                              p q w) ≤
                          Homogenization.volumeAverage
                            (U : Set (Homogenization.Vec d))
                            (Homogenization.scalarResponseIntegrand
                              (U : Set (Homogenization.Vec d))
                              (fun x : Homogenization.Vec d =>
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                      nu omega L).toCoeffField x -
                                  Homogenization.volumeAverageMat
                                    (U : Set (Homogenization.Vec d))
                                    (fun y =>
                                      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                        omega m L y))
                              p q u)) →
                      (∀ w : Homogenization.AHarmonicFunction
                          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                              nu omega m).toCoeffField
                          (U : Set (Homogenization.Vec d)),
                          Homogenization.volumeAverage
                              (U : Set (Homogenization.Vec d))
                              (Homogenization.scalarResponseIntegrand
                                (U : Set (Homogenization.Vec d))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega m).toCoeffField p q w) ≤
                            Homogenization.volumeAverage
                              (U : Set (Homogenization.Vec d))
                              (Homogenization.scalarResponseIntegrand
                                (U : Set (Homogenization.Vec d))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega m).toCoeffField p q v)) →
                        Homogenization.volumeAverage
                            (U : Set (Homogenization.Vec d))
                            (fun x =>
                              Homogenization.vecNormSq
                                (u.toH1.grad x - v.toH1.grad x)) ≤
                          C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
                              sSup
                                (Set.range fun o :
                                    Option {x : Homogenization.Vec d //
                                      x ∈ Homogenization.openCubeSet
                                        (Homogenization.originCube d (n : ℤ))} =>
                                  match o with
                                  | none => 0
                                  | some x =>
                                      SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixDerivativeNorm
                                        (∑ k ∈ Finset.Ioc m L,
                                          SuperdiffusionCLT.Frozen.Assumptions.ShellField.deriv
                                            (omega k) x.1)) *
                            (Homogenization.ResponseJ
                                (U : Set (Homogenization.Vec d)) p q
                                (fun x : Homogenization.Vec d =>
                                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                        nu omega L).toCoeffField x -
                                    Homogenization.volumeAverageMat
                                      (U : Set (Homogenization.Vec d))
                                      (fun y =>
                                        SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                          omega m L y)) +
                              Homogenization.ResponseJ
                                (U : Set (Homogenization.Vec d)) p q
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega m).toCoeffField +
                              2 * Homogenization.vecDot p q) := by
  exact cutoff_localization_proved d
    (cutoffLocalizationConjunct3_hconj3_minimizerEnergy d hd)

end

end SuperdiffusionCLT.Section2.Localization
