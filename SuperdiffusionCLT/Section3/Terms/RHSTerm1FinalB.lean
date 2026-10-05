/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Residues
public import SuperdiffusionCLT.Section3.Terms.ResponseHessianMeasurableB

/-!
# `l.RHS.term1` with every discharge wired in

The statement `SuperdiffusionCLT.Frozen.Section3.rhs_term1` (`e.RHS.term1` of
the paper) is proved here with its conclusion **verbatim** and with the shortest
list of named hypotheses that the supporting results support.

## The chain

* `RHSTerm1WeakHessian.term1_of_residueB` gives the
  conclusion from the five obligations `_hMeasH1`, `_hMeasHminus`,
  `_hLocMin`, `_hJensen`, `_hConcDepth` and the three section binders `Cloc`,
  `hCloc` (the gate `1 ≤ Cloc`), `Cc`.  (The weak-Hessian binder `HD` is
  *produced* by the divergence-form endpoint `canonicalResponseHessian`, so it
  is no longer assumed, and the `1 ≤ Cc` gate is already free.)
* `RHSTerm1Final.term1_final` drops the last section
  gate: the localization clause is carried at the bare constant `Cloc` and
  upgraded to `max 1 Cloc` inside the proof (`locMinConstant_mono` with the
  derived sign `locMinResponseFactor_nonneg`).  Five obligations remain.
* `RHSTerm1Residues.term1_final_hMinusFree` discharges `_hMeasHminus` by
  `HatNegNormMeasurable.aemeasurable_vecHatNegENormOrderOne_term1Hminus`, which is
  the exact shape of that binder.  Four obligations remain.
* This file discharges `_hMeasH1` by
  `ResponseHessianMeasurableB.aemeasurable_vecCubeH1ENorm_grad_canonicalResponseHessian`,
  the exact shape of that binder at the canonical weak Hessian.  **Three
  obligations remain**: `_hLocMin`, `_hJensen`, `_hConcDepth`, together with
  the two section constants `Cloc` and `Cc`.

## The residue of `term1_finalB`

* `Cloc`, `Cc` — the section constants of `_hLocMin` and of `_hConcDepth`, both
  entering ungated.  They are constants of the two clauses, not gates on the
  statement: no inequality of the form `1 ≤ Cloc` or `1 ≤ Cc` is
  assumed, and both clauses are upward-closed in their constants.  Neither can
  be *pinned* here, because both appear as hypotheses rather
  than as conclusions produced at a packaging constant.
* `_hLocMin` — the minimizer clause of the cutoff localization statement of
  `Frozen.Section2`, at the constant `Cloc`.
* `_hJensen` — the *difference*-Jensen bound at the pinned proxy.  It is not a
  Jensen bound on one annealed average: writing
  `q̃ = qVector hnu P S.ell S.ell S.n S.m F` and
  `q = qVector hnu P S.LPrime S.ell S.n S.m F`, the two are the annealed
  `cu_ℓ`-averages of `a_ℓ ∇ũ_ℓ` and of `a_ℓ ∇ũ_{L'}`, so `q̃ − q` is the
  annealed average of `a_ℓ (∇ũ_ℓ − ∇ũ_{L'})`, the field whose annealed `L²`
  energy is the right side of the binder up to sign.  Its **primitive form** is
  the componentwise integrability of the two annealed `cu_ℓ`-averages
  (`_hInt1`, `_hInt2`): the binder follows from it, and the total convention for
  the Bochner integral makes the mixed case irreducible without it.
* `_hConcDepth` — the sublattice concentration of `a_ℓ ∇ũ_n − q̃` at `Cc`, the
  printed clause of `e.RHS.term1`.  `SublatticeConcentrationDepth` proves
  the per-sublattice rule for the flux block averages and the
  annealed envelope of the proxy, and the rule is converted to the printed
  second-moment shape.  What remains is the
  structural identification of each depth-`j` descendant mean with such a
  finset average, together with the block-measurability, deterministic-bound
  and translated-block centering inputs listed in the
  `SublatticeConcentrationDepth` docstring.

So the residue of `term1_finalB` is the localization clause `_hLocMin` plus two
analytic obligations, `_hJensen` and `_hConcDepth`.  Every measurability
obligation and every section gate is gone.

## Main results

* `term1_finalB`: the `l.RHS.term1` conclusion verbatim, from
  `_hLocMin`, `_hJensen`, `_hConcDepth` and the section constants `Cloc`, `Cc`.
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

/-! ## The statement with the two measurability obligations discharged -/

/-- **`l.RHS.term1` with the two measurability obligations discharged.**

The binders and the conclusion are those of
`SuperdiffusionCLT.Frozen.Section3.rhs_term1` verbatim; the only additions
are the section constants `Cloc` and `Cc` (the constants of the two clauses,
both entering ungated) and the three named obligations `_hLocMin`, `_hJensen`,
`_hConcDepth`, attached after the `_hw` binder and before the
`_hPigeon` side condition, exactly as in `RHSTerm1WeakHessian.term1_of_residueB`
with the two measurability binders removed.

Two premises that `term1_final_hMinusFree` carried are gone:

* `_hMeasH1` — the `ω`-measurability of the `H̲¹(cu_m)` carrier of the response
  at the canonical weak Hessian, supplied inside the proof by
  `ResponseHessianMeasurableB.aemeasurable_vecCubeH1ENorm_grad_canonicalResponseHessian`;
* `_hMeasHminus` — the `ω`-measurability of `ω ↦ ‖a_ℓ ∇ũ_n − q̃‖_{Ĥ̲^{-1}(cu_m)}`,
  supplied inside the proof by
  `HatNegNormMeasurable.aemeasurable_vecHatNegENormOrderOne_term1Hminus`.

See the module header for the standing of each remaining binder. -/
theorem term1_finalB (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (Cloc : ℝ) (Cc : ℝ) :
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
        (_hJensen : ENNReal.ofReal (Real.sqrt (vecNormSq
              (qVector hnu P S.ell S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) -
                qVector hnu P S.LPrime S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e)))) ≤
          (∫⁻ omega : ShellSeq d,
              (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x -
                    gluedGradientField hnu S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x))) ^ (2 : ℕ)
            ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
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
  obtain ⟨C, hC1, hmain⟩ := term1_final_hMinusFree d _hd Cloc Cc
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hLocMin hJensen hConcDepth hPigeon
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    (aemeasurable_vecCubeH1ENorm_grad_canonicalResponseHessian _hd S nu P e hw)
    hLocMin hJensen hConcDepth hPigeon

/-! ## The same target at the primitive form of `_hJensen`

`RHSTerm1Residues.hJensen_printedProxy_of_integrable` proves the `_hJensen`
binder of `term1_finalB` at the printed proxy from the componentwise
integrability of the two annealed `cu_ℓ`-averages of `a_ℓ ∇ũ_ℓ` and of
`a_ℓ ∇ũ_{L'}`.  The wrapper below states the conclusion at that primitive
form, so the residual content of the difference-Jensen obligation is named as
two integrability statements rather than as a display bound.  This replaces one
binder by two, so it is a *reduction* of `_hJensen` to its primitive inputs, not
a net discharge of the binder count. -/

end

end SuperdiffusionCLT.Section3.Terms
