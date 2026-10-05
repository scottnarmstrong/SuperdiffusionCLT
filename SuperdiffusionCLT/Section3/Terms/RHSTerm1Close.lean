/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.HatNegNormMeasurable
public import SuperdiffusionCLT.Section3.Terms.ResponseHessianMeasurableB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1AnalyticB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1MeasurableInputs

/-!
# `l.RHS.term1` in its shortest form

The statement `SuperdiffusionCLT.Frozen.Section3.rhs_term1` (`e.RHS.term1` of the
paper) is proved here with its conclusion **verbatim** and with the shortest list
of named hypotheses that the supporting results support.

## Summary

`term1_close` carries exactly **two** obligation binders, the localization
clause `_hLocMin` and the concentration clause `_hConcDepth`, in the shapes of the
statement, together with the two section constants `Cloc` and `Cc` and the
pigeonhole side condition `_hPigeon`.  Every measurability obligation and the
difference-Jensen obligation are discharged.

## What each supporting module supplies

* The reduction of `l.RHS.term1` to `_hLocMin`, `_hJensen`, `_hConcDepth` plus
  `Cloc`, `Cc` already *wires* both hard measurability residues, so no
  measurability binder survives:
  * `_hMeasH1`, the `ω`-measurability of the `H̲¹(cu_m)` carrier of the response
    at the canonical weak Hessian, is supplied inside the proof at the canonical witness;
  * `_hMeasHminus`, the `ω`-measurability of
    `ω ↦ ‖a_ℓ ∇ũ_n − q̃‖_{Ĥ̲^{-1}(cu_m)}`, is supplied inside the proof.
  No hypothesis is added in their place.
* `RHSTerm1Analytic.term1_hInt1` and `RHSTerm1Analytic.term1_hInt2` are the two
  integrability inputs of `_hJensen`, proved **unconditionally** from the premises the
  statement already carries (the `Γ₂` envelope `coeffLinftySupBound`, its
  first-moment finiteness, and the scale facts `n < ℓ < m`).  Hence `_hJensen`
  is discharged outright: `_hJensen` is gone, with no replacement hypothesis.
* `RHSTerm1AnalyticB.term1_finalC_jensenFree` is the wiring of that discharge;
  its residue is `_hLocMin` (as the abbreviation `LocMinClause`) and
  `_hConcDepth`, plus `Cloc`, `Cc`.  `term1_close` below is that statement with
  `_hLocMin` written out in full.
* The printed depth-moment clause `_hConcDepth` is proved at every `Cc`
  dominating `3^{d (S.m - S.ell)}`, because the descendant Jensen bound
  `vecDepthSqMoment_le_vecSqAvg_of_memVectorL2` already dominates the display
  once the depth weight is absorbed.  This is a **reduction** of `_hConcDepth`, not a
  discharge.
* `SublatticeConcentrationDepth` contains the per-sublattice rule for the block
  averages of the flux and the annealed envelope of the proxy.  The hypotheses of
  the term-1 flux block observable bound, namely lane measurability and
  centering, together with the identification of a depth-`j` descendant mean with a
  finset average, are the structural residue recorded in the
  `SublatticeConcentrationDepth` docstring; they do not reach the clause at a
  scale-independent constant.
* `RHSTerm1MeasurableInputs{,B,C}` give the sample measurability of the flux cube
  means and of their centred depth moments, all consumed by the chain above.
* `RHSTerm1PigeonJensen` gives the constant gates at the clause level
  (`hConcDepth_gate_upgrade`, `hLocMin_gate_upgrade`).

## The concentration residue

The two candidate residues for `_hConcDepth` are not equivalent, and the
*larger* one is the right one:

* the printed clause `_hConcDepth` at the constant `Cc`;
* the numeric pin `3^{d (m - ℓ)} ≤ Cc`.

The pin **implies** the clause, so a theorem
carrying the pin is *weaker* than one carrying the clause; the clause is
therefore the shortest residue and is what `term1_close` carries.  The
pin cannot even be met uniformly: for every real `Cc` there is a scale selection
with `ScalesOrdering` and the pigeonhole bound
whose weight `3^{d (S.m - S.ell)}` exceeds `Cc`, so no single `Cc`
dominates the weight over all admissible scale selections.  The route uses the
identity `S.m - S.ell = S.h + S.a` (`ScaleSelection.ell_add_a`,
`ScaleSelection.ellPrime_add_h`), through which `S.m - S.ell` is unbounded over
the scale selections.  Consequently the pin form is a strict weakening of
the statement `rhs_term1`, not a discharge of `_hConcDepth`.

## Main results

* `term1_close` is the `l.RHS.term1` conclusion verbatim, from `_hLocMin`
  (at `Cloc`) and `_hConcDepth` (at `Cc`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

/-- **`l.RHS.term1`, shortest form.**

The binders and the conclusion are those of
`SuperdiffusionCLT.Frozen.Section3.rhs_term1` verbatim; the only additions
are the section constants `Cloc` and `Cc` (the constants of the two clauses,
both entering ungated) and the two named obligations `_hLocMin` and
`_hConcDepth`, attached after the `_hw` binder and before the
`_hPigeon` side condition, with `_hLocMin` reproduced in full.

Three premises that the intermediate forms carried are gone:

* `_hMeasH1` and `_hMeasHminus` — the two `ω`-measurability obligations, wired
  inside the proof of `RHSTerm1FinalB.term1_finalB` by
  `ResponseHessianMeasurableB.aemeasurable_vecCubeH1ENorm_grad_canonicalResponseHessian`
  and `HatNegNormMeasurable.aemeasurable_vecHatNegENormOrderOne_term1Hminus`;
* `_hJensen` — the difference-Jensen obligation, discharged unconditionally by
  `RHSTerm1AnalyticB.term1_finalC_jensenFree` from the integrability
  theorems `RHSTerm1Analytic.term1_hInt1` and `term1_hInt2`.

The residue is therefore exactly `_hLocMin` (the localization clause, being
closed elsewhere) and `_hConcDepth` (the printed concentration clause), with the
two section constants. -/
theorem term1_close (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (Cloc : ℝ) (Cc : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega))
        (_hLocMin : ∀ U : Book.Ch02.Domain d,
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
                      2 * vecDot p q))
        (_hConcDepth : ∀ j : ℕ,
          (∫⁻ omega : ShellSeq d,
              ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                    qVector hnu P S.ell S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e)))
            ∂P.toMeasure : ℝ≥0∞) ≤
            ENNReal.ofReal (Cc *
                (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
              (∫⁻ omega : ShellSeq d,
                  ENNReal.ofReal (vecSqAvg (originCube d (S.m : ℤ))
                    (fun x => matVecMul
                      ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (gluedGradientField hnu S.ell S.n S.m
                        (fluxSlot nu S.LPrime P S.n e) omega x) -
                        qVector hnu P S.ell S.ell S.n S.m
                          (fluxSlot nu S.LPrime P S.n e)))
              ∂P.toMeasure : ℝ≥0∞))
        (_hPigeon : 2 * S.h ≤ S.m),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                  qVector hnu P S.LPrime S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
            ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) := by
  exact term1_finalC_jensenFree d _hd Cloc Cc

end

end SuperdiffusionCLT.Section3.Terms
