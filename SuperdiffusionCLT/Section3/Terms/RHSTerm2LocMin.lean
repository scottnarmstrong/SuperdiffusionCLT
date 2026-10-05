/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02.Setup
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable
public import SuperdiffusionCLT.Section2.Cutoff.Finite
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Analytic
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2FinalB

/-!
# `hLocMin` of the term-2 assembly from the localization conclusion

## Summary

The clause `hLocMin` of the term-2 assembly of `l.RHS.term2`
is the localization minimizer clause at
the scales `(m, L, n) = (S.ell, S.LPrime, S.n)`. It is **character for
character the same clause** as `_hLocMin` of `term1_close`
(`Section3/Terms/RHSTerm1Close.lean`), and the same as the predicate
`RHSTerm1Residues.LocMinClause d nu S Cloc`: all three use the localization
carriers (`coefficientCutoff nu omega' S.LPrime` shifted by the cube average of
`finiteShellIncrement omega' S.ell S.LPrime`, and `coefficientCutoff nu omega'
S.ell`), the same response values `ResponseJ …` at those two fields, and the same
window `anchorDerivSup S.ell S.LPrime S.n`. There are **no term-specific
carriers**: term 1 and term 2 read the identical clause, so the two shapes are
the same statement, not two different clauses. Any difference between term 1 and
term 2 lives strictly below `hLocMin` (in the *consumer* that feeds `hLocMin`),
never in the clause itself.

## Main result

The theorem `cutoff_localization`
carries the conclusion

`∃ C, ∀ nu, P, laws, ∀ m n L, n ≤ m → m ≤ L, ∀ U ⊆ cu_n, conj1 ∧ conj2 ∧ conj3`,

whose third conjunct is the localization minimizer bound `e.localization.minimizers`
at that theorem's constant and its three scales. That theorem is not
imported here; instead its conclusion is carried as the named hypothesis `hLoc`.

`term2_hLocMin_of_localization` derives from `hLoc` the exact `hLocMin`
clause of the term-2 assembly, at `Cloc` the anchor's own constant, by
specializing the anchor at `(m, n, L) = (S.ell, S.n, S.LPrime)`; the two scale
inequalities `S.n ≤ S.ell ≤ S.LPrime` are read off `ScalesOrdering S`. The
hypothesis uses the anchor's literal `sSup`-render of the `L^∞(cu_n)` window,
and the conclusion uses the `rfl`-equal carrier `anchorDerivSup`.

## Main results

* `term2_hLocMin_of_localization`.

## References

* The paper: `e.localization.minimizers`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **`hLocMin` of the term-2 assembly from the localization conclusion.**

`hLoc` is the conclusion of
`cutoff_localization` in its
literal shape, carried as a named hypothesis. The theorem extracts its third conjunct
(`e.localization.minimizers`) and specializes it at the scale triple
`(m, n, L) = (S.ell, S.n, S.LPrime)`, giving exactly the `hLocMin` clause of
the term-2 assembly at the anchor's constant.

The scale inequalities the anchor needs are the first two entries of
`ScalesOrdering`: `S.n < S.ell < S.ellPrime < S.m < S.LPrime`. The anchor's
`sSup`-rendered `L^∞(cu_n)` window is the definitional unfold of the carrier
`anchorDerivSup S.ell S.LPrime S.n omega'`, so the conclusion is the clause
verbatim. -/
theorem term2_hLocMin_of_localization (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
    (hLoc : ∃ C : ℝ,
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
                              2 * Homogenization.vecDot p q)) :
    ∃ Cloc : ℝ,
      ∀ (nu : ℝ) (_hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S),
      ∀ U : Book.Ch02.Domain d,
        (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
        ∀ (omega' : ShellSeq d) (p q : Vec d)
          (u : AHarmonicFunction
            (fun x : Vec d =>
              (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                volumeAverageMat (U : Set (Vec d))
                  (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
            (U : Set (Vec d)))
          (v : AHarmonicFunction
            (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
          (∀ w : AHarmonicFunction
              (fun x : Vec d =>
                (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                  volumeAverageMat (U : Set (Vec d))
                    (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
              (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                    p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                    p q u)) →
          (∀ w : AHarmonicFunction
              (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
              volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
                volumeAverage (U : Set (Vec d))
                  (scalarResponseIntegrand (U : Set (Vec d))
                    (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
            volumeAverage (U : Set (Vec d))
                (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
              Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                  anchorDerivSup S.ell S.LPrime S.n omega' *
                (ResponseJ (U : Set (Vec d)) p q
                    (fun x : Vec d =>
                      (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                        volumeAverageMat (U : Set (Vec d))
                          (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                  ResponseJ (U : Set (Vec d)) p q
                    (coefficientCutoff nu omega' S.ell).toCoeffField +
                  2 * vecDot p q) := by
  obtain ⟨C, hC⟩ := hLoc
  refine ⟨C, ?_⟩
  intro nu _hnu _hnu1 P _hPrefix _hJ1 _hJ2 _hJ3 _hJ4 S _hSorder
  have hnm : S.n ≤ S.ell := le_of_lt _hSorder.n_lt_ell
  have hmL : S.ell ≤ S.LPrime :=
    le_trans (le_of_lt _hSorder.ell_lt_ellPrime)
      (le_trans (le_of_lt _hSorder.ellPrime_lt_m) (le_of_lt _hSorder.m_lt_LPrime))
  intro U hU omega' p q u v hu hv
  exact (hC nu _hnu _hnu1 P _hPrefix _hJ1 _hJ2 _hJ3 _hJ4 S.ell S.n S.LPrime hnm hmL
      U hU).2.2 omega' p q u v hu hv

end

end SuperdiffusionCLT.Section3.Terms
