/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2DispCanonical

/-!
# `l.RHS.term2` from the localization clause alone

`SuperdiffusionCLT.Frozen.Section3.rhs_term2` (the statement of `l.RHS.term2`)
is not imported by this module.  Instead its
conclusion is restated here character for character as the goal of
`rhs_term2_statement_of_localization`, with the localization clause `hLocMinEx`
— the conclusion of the reduction
`RHSTerm2LocMin.term2_hLocMin_of_localization` — as its only hypothesis.  The
proof is one application of
`RHSTerm2DispCanonical.term2_finalC_canonical_of_localization`, whose own
hypotheses are exactly `d`, `[NeZero d]`, `hd : 2 ≤ d` and `hLocMinEx`.

## Constant-first

Only `d`, `[NeZero d]` and `hd : 2 ≤ d` precede `∃ C` inside the goal, and the
single constant is chosen before `nu`, the shell law, the scale selection, the
unit vector, the Dirichlet response and the response field, exactly as the
statement orders them.  No display constant of the proof is promoted into the
statement: the assembly `term2_finalC_canonical_of_localization` already carries
the constant of `e.RHS.term2.R.bounds` internally.

## What remains

Nothing separates this theorem from the statement of `l.RHS.term2` except the localization
clause `hLocMinEx`: the conclusion of the two is the same text, so discharging
`hLocMinEx` proves `l.RHS.term2`.  `hLocMinEx` is the third
conjunct `e.localization.minimizers` of `Frozen.Section2.cutoff_localization`
(`Frozen/Section2/CutoffLocalization.lean`) at the scales
`(m, n, L) = (S.ell, S.n, S.LPrime)`, so the residue between this
theorem and the statement is exactly that localization theorem.

## Witness of the standing hypotheses

`d = 2` witnesses the dimension binders: the instance `[NeZero 2]` exists and
`hd : 2 ≤ 2` is `le_refl 2`.  The remaining hypothesis `hLocMinEx` is the
localization clause, not a vacuous side condition: it is by construction the
exact conclusion of `RHSTerm2LocMin.term2_hLocMin_of_localization`, whose only
hypothesis is the conclusion of `cutoff_localization`.  No witness for it is
exhibited in this module; it is supplied by that localization theorem.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

/-- **`l.RHS.term2` from the localization clause alone.**

The conclusion is the statement of `Frozen/Section3/RHSTerm2.lean` with only the
declaration name changed; the
hypothesis `hLocMinEx` is the `hLocMin` family of
`RHSTerm2DispCanonical.term2_finalC_canonical_of_localization`, i.e. the third
conjunct `e.localization.minimizers` of `cutoff_localization` at the scales
`(m, n, L) = (S.ell, S.n, S.LPrime)`.  `d`, `[NeZero d]` and `hd : 2 ≤ d` are the
only standing binders and `∃ C` stands before every other quantifier, as in the
statement. -/
theorem rhs_term2_statement_of_localization (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hLocMinEx : ∃ Cloc : ℝ,
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
                  2 * vecDot p q)) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu), nu ≤ 1 →
      ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P →
        ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
      ∀ (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d), vecNormSq e = 1 →
      ∀ (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega)) →
        |∫ omega : ShellSeq d,
            ((SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d
                S.n S.m).card : ℝ)⁻¹ *
              ∑ z ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes
                d S.n S.m,
                volumeAverage (openCubeSet z)
                  (fun y => vecDot ((w omega).toH1Function.grad y)
                    (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                      (coefficientCutoff nu omega S.ell).toCoeffField y)
                      (gluedGradientField hnu S.LPrime S.n S.m
                          (fluxSlot nu S.LPrime P S.n e) omega y -
                        testVector nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) :=
  term2_finalC_canonical_of_localization d hd hLocMinEx

end

end SuperdiffusionCLT.Section3.Terms
