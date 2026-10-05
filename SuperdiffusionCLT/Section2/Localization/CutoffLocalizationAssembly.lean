/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffSkewPremisesB
public import SuperdiffusionCLT.Section2.Localization.ShellWindowDomination

/-!
# The localization statement assembled from its conjuncts

The second conjunct is supplied by `localizationConjunct2_proved`.  The third
conjunct is the explicit input `hconj3` of `cutoff_localization_proved`; it is
supplied by `Conj3EndgameMinimizerEnergy.cutoffLocalizationConjunct3_hconj3_minimizerEnergy`.
It is consumed only at the constants the assembly chooses, those dominating
`localizationMaxConst d`; the statement binds an existential `C`, so nothing
forces the clause at the small constants (in particular at `C = 0`) that the
averaged route cannot reach.
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

/-- The shared constant of the assembled anchor: the maximum of the three
conjuncts' own constants, `localizationConst d` (conjunct 1),
`localizationSkewConst d` (conjunct 2) and the conjunct-3 gate constant
`(45 / 4) * matrixOperatorNorm_diamConst d`.  The statement binds a
single existential `C`, and this is the constant the assembly chooses, so the
third conjunct is consumed only at constants dominating it. -/
def localizationMaxConst (d : ℕ) : ℝ :=
  max (max (localizationConst d) (localizationSkewConst d))
    ((45 / 4) * matrixOperatorNorm_diamConst d)

theorem cutoff_localization_proved (d : ℕ)
    (hconj3 : ∀ C : ℝ, localizationMaxConst d ≤ C →
        ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
          ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ m n L : ℕ, n ≤ m → m ≤ L →
            ∀ U : Domain d,
              (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)) →
              ∀ (omega : ShellSeq d) (p q : Vec d)
                (u : AHarmonicFunction
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega L).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega m L y))
                  (U : Set (Vec d)))
                (v : AHarmonicFunction
                  (coefficientCutoff nu omega m).toCoeffField
                  (U : Set (Vec d))),
                (∀ w : AHarmonicFunction
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega L).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega m L y))
                    (U : Set (Vec d)),
                    volumeAverage (U : Set (Vec d))
                        (scalarResponseIntegrand (U : Set (Vec d))
                          (fun x : Vec d =>
                            (coefficientCutoff nu omega L).toCoeffField x -
                              volumeAverageMat (U : Set (Vec d))
                                (fun y => finiteShellIncrement omega m L y))
                          p q w) ≤
                      volumeAverage (U : Set (Vec d))
                        (scalarResponseIntegrand (U : Set (Vec d))
                          (fun x : Vec d =>
                            (coefficientCutoff nu omega L).toCoeffField x -
                              volumeAverageMat (U : Set (Vec d))
                                (fun y => finiteShellIncrement omega m L y))
                          p q u)) →
                  (∀ w : AHarmonicFunction
                      (coefficientCutoff nu omega m).toCoeffField
                      (U : Set (Vec d)),
                      volumeAverage (U : Set (Vec d))
                          (scalarResponseIntegrand (U : Set (Vec d))
                            (coefficientCutoff nu omega m).toCoeffField p q w) ≤
                        volumeAverage (U : Set (Vec d))
                          (scalarResponseIntegrand (U : Set (Vec d))
                            (coefficientCutoff nu omega m).toCoeffField p q v)) →
                    volumeAverage (U : Set (Vec d))
                        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
                      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
                          sSup (Set.range fun o :
                            Option {x : Vec d //
                              x ∈ openCubeSet (originCube d (n : ℤ))} =>
                              match o with
                              | none => 0
                              | some x =>
                                  ShellField.matrixDerivativeNorm
                                    (∑ k ∈ Finset.Ioc m L,
                                      ShellField.deriv (omega k) x.1)) *
                        (ResponseJ (U : Set (Vec d)) p q
                            (fun x : Vec d =>
                              (coefficientCutoff nu omega L).toCoeffField x -
                                volumeAverageMat (U : Set (Vec d))
                                  (fun y => finiteShellIncrement omega m L y)) +
                          ResponseJ (U : Set (Vec d)) p q
                            (coefficientCutoff nu omega m).toCoeffField +
                          2 * vecDot p q))  :
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
                              2 * Homogenization.vecDot p q)
 := by
  refine ⟨localizationMaxConst d, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n L hnm hmL U hU
  -- Conjunct 1, applied: the proved clause at its packaging constant.
  obtain ⟨X, hXmeas, hXbigO, hXclauses⟩ :=
    cutoffLocalizationConjunct1 P hJ3 nu hnu hnu1 n m L hnm hmL U hU
  -- Conjunct 2, at the shared constant.
  obtain ⟨Y, hYmeas, hYbigO, hYbilinear⟩ :=
    localizationConjunct2_proved d (localizationMaxConst d)
      (le_trans (le_max_left (localizationConst d) (localizationSkewConst d))
        (le_max_left (max (localizationConst d) (localizationSkewConst d))
          ((45 / 4) * matrixOperatorNorm_diamConst d)))
      (le_trans (le_max_right (localizationConst d) (localizationSkewConst d))
        (le_max_left (max (localizationConst d) (localizationSkewConst d))
          ((45 / 4) * matrixOperatorNorm_diamConst d)))
      nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n L hnm hmL U hU
  refine ⟨⟨X, hXmeas, ?_, hXclauses⟩, ⟨Y, hYmeas, hYbigO, hYbilinear⟩, ?_⟩
  · -- The constant bridge for the sandwich witness: the packaging constant is
    -- dominated by the shared one, and the rate factors are nonnegative.
    have hnu2 : 0 ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg (le_of_lt hnu) _
    have hT0 : 0 ≤ (3 : ℝ) ^ (-((m - n : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    exact hXbigO.mono_scale (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (le_trans (le_max_left (localizationConst d) (localizationSkewConst d))
          (le_max_left (max (localizationConst d) (localizationSkewConst d))
            ((45 / 4) * matrixOperatorNorm_diamConst d))) hnu2)
      hT0)
  · -- Conjunct 3, assumed at the shared constant.
    exact hconj3 (localizationMaxConst d) (le_refl _) nu hnu hnu1 P hPrefix
      hJ1 hJ2 hJ3 hJ4 m n L hnm hmL U hU

end

end SuperdiffusionCLT.Section2.Localization
