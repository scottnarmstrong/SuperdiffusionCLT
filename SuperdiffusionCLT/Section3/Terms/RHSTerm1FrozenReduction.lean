/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1StepTwoBridgeB

/-!
# `l.RHS.term1`, reduced to the named obligations

The statement `SuperdiffusionCLT.Frozen.Section3.rhs_term1` (`e.RHS.term1` of
the paper) is the target: the constant `C(d)` is quantified before every piece of
section data and the statement carries only the printed hypotheses — the five
standing shell laws, `0 < ν ≤ 1`, the scale selection with `ScalesOrdering`,
the unit direction `e`, the response `w` with its defining weak-form condition,
and the pigeonhole comparability `2 * S.h ≤ S.m`.

## What the chain proves, and what it still carries

The chain `l_RHS_term1_of_anchors_constFirst_memLp` (in `RHSTerm1StepTwoBridgeB`)
has the same conclusion, with every glued field and
both flux vectors left as binders.  The reduction below pins the four
objects of the statement at their definitions —

* `p = testVector nu S.LPrime P S.n e` (the print's `p = shom_{L',*}^{-1/2} e`),
* `∇u_n = gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)`,
* `q = qVector hnu P S.LPrime S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`,
* `∇ũ_n = gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`

— and supplies every one of the chain's remaining hypotheses **either from the
statement's own binders or from an explicit obligation binder**.  The
result `term1_of_obligations` is therefore exactly the statement plus
the obligation list, and nothing else: each obligation binder is reproduced
below verbatim from the chain it was carried in, with the pinned objects
substituted.

## The obligations

Before the `∃ C` (section-wide constants):

* `Cloc`, `hCloc` — the constant of the clause `hLocMin` of
  `Frozen.Section2.cutoff_localization`.  That statement produces the clause
  at its own constant, but that constant carries no normalization, and
  upgrading it to a `Cloc` with `1 ≤ Cloc` needs the J-sum of the clause to be
  nonnegative (otherwise no constant at least one can work, because the clause's
  right side would be negative while its left side is not).
* `Cc`, `hCc` — the constant of the sublattice concentration `hConcDepth`.

Inside the section data (each stated for the pinned `∇u_n`, `∇ũ_n`, `q` and the
free `qTilde`):

* `HD` — a weak Hessian witness for the response `w`: the `H²(cu_m)` regularity
  of `e.def.w`.  The
  `HilbertMat`-carrier measurability the chain also consumes is **not** an
  obligation: `aestronglyMeasurable_hessCarrier` below derives it from `HD`
  through `HasWeakHessianOn.hess_memLp_normalizedCubeMeasure`, the same three
  steps that prove `aestronglyMeasurable_honestJacobianHilbertMat`.
* `_hMeasGradW`, `_hMeasH1`, `_hMeasStep2` — the `ω`-measurability of the
  three `w`-dependent quantities the chain consumes.
* `_hMeasFlux`, `_hMeasHminus`, `_hMeasDepth`, `_hMeasL2` — the
  `ω`-measurability of the four glued-field quantities; the glued-field development
  gives only the pointwise (`x`-wise) measurability of `gluedGradientField`, not the
  `ω`-measurability the chain needs.
* `hLocMin` — the clause of `Frozen.Section2.cutoff_localization`,
  at the constant `Cloc`.
* `hMeasCoeff`, `hMeasDeriv` — the `ω`-measurability of the two `L^∞` window
  carriers `coeffCubeLinftyENorm` and `shellDerivCubeLinftyENorm`.
* `hJensen`, `hQTilde` — the two duality inputs, in the exact shape the chain
  consumes them.  They are stated here for an arbitrary `qTilde`; at
  `qTilde = q` the first is trivial, at `qTilde = 0` the second is.
* `hConcDepth` — the sublattice concentration of `a_ℓ ∇ũ_n − q̃`.

## Main results

* `term1_of_obligations`: the statement
  `SuperdiffusionCLT.Frozen.Section3.rhs_term1`, proved from the
  chain plus exactly the obligation list above.
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
open SuperdiffusionCLT.Section2.Norms
  (vecHatNegENormOrderOne)

noncomputable section

/-! ## The measurability of the weak Hessian carrier -/

/-- **The `HilbertMat` carrier of a weak Hessian is a.e. measurable** on the
normalized cube measure: each coordinate of a weak Hessian witness is in
normalized `L²` (`HasWeakHessianOn.hess_memLp_normalizedCubeMeasure`, hence
a.e. strongly measurable), the matrix is assembled entrywise
(`aemeasurable_pi_iff`), and `HilbertMat.ofMat` is the inverse of a continuous
linear equivalence (`HilbertMat.continuousLinearEquivMat`).  The same three
steps prove `aestronglyMeasurable_honestJacobianHilbertMat`; this is the instance of that
pattern at a weak Hessian witness. -/
private theorem aestronglyMeasurable_hessCarrier {d : ℕ} (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)} (HD : HasWeakHessianOn (openCubeSet Q) v) :
    AEStronglyMeasurable
      (fun x : Vec d => HilbertMat.ofMat (fun i j => HD.hess i j x))
      (normalizedCubeMeasure Q) := by
  have hentry : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x : Vec d => HD.hess i j x)
        (normalizedCubeMeasure Q) :=
    fun i j => (HD.hess_memLp_normalizedCubeMeasure Q i j).aestronglyMeasurable
  have hmat : AEStronglyMeasurable
      (fun x : Vec d => (fun i j => HD.hess i j x : Mat d))
      (normalizedCubeMeasure Q) := by
    rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
    intro i
    rw [aemeasurable_pi_iff]
    intro j
    exact (hentry i j).aemeasurable
  exact (HilbertMat.continuousLinearEquivMat d).symm.continuous.comp_aestronglyMeasurable
    hmat

/-- **`l.RHS.term1` from the chain, with the obligations named.**

The binders down to `_hw` are the statement's own binders
(the declaration name and the two section-wide constants are the only additions
before them); every binder after `_hw` is an obligation, reproduced verbatim
from `l_RHS_term1_of_anchors_constFirst_memLp` with the pinned objects
`testVector nu S.LPrime P S.n e`,
`gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e)`,
`gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)` and
`qVector hnu P S.LPrime S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)`
substituted for the chain's `p`, `uNGlued`, `uTildeGlued` and `q`. -/
theorem term1_of_obligations (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
    (Cloc : ℝ) (hCloc : 1 ≤ Cloc) (Cc : ℝ) (hCc : 1 ≤ Cc) :
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
        (HD : ∀ omega : ShellSeq d,
          HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
            (w omega).toH1Function)
        (qTilde : Vec d)
        (_hMeasGradW : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2 (w omega).toH1Function.grad)
          P.toMeasure)
        (_hMeasFlux : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.LPrime S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x -
                gluedGradientField hnu S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) omega x))) P.toMeasure)
        (_hMeasH1 : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeH1ENorm (originCube d (S.m : ℤ)) (w omega).toH1Function.grad
            (fun x => fun i j => (HD omega).hess i j x)) P.toMeasure)
        (_hMeasHminus : AEMeasurable (fun omega : ShellSeq d =>
          vecHatNegENormOrderOne (originCube d (S.m : ℤ))
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde)) P.toMeasure)
        (_hMeasDepth : ∀ j : ℕ, AEMeasurable (fun omega : ShellSeq d =>
          ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde))) P.toMeasure)
        (_hMeasL2 : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde)) P.toMeasure)
        (_hMeasStep2 : AEMeasurable (fun omega : ShellSeq d =>
          ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde))|)
          P.toMeasure)
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
        (_hMeasCoeff : Measurable fun omega : ShellSeq d =>
          coeffCubeLinftyENorm nu S.ell S.ell omega)
        (_hMeasDeriv : Measurable fun omega : ShellSeq d =>
          shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega)
        (_hJensen : ENNReal.ofReal (Real.sqrt (vecNormSq
              (qTilde - qVector hnu P S.LPrime S.ell S.n S.m
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
        (_hQTilde : ENNReal.ofReal (Real.sqrt (vecNormSq qTilde)) ≤
          (∫⁻ omega : ShellSeq d,
              (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x))) ^ (2 : ℕ)
            ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
        (_hConcDepth : ∀ j : ℕ,
          (∫⁻ omega : ShellSeq d,
              ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde))
            ∂P.toMeasure : ℝ≥0∞) ≤
            ENNReal.ofReal (Cc *
                (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
              (∫⁻ omega : ShellSeq d,
                  ENNReal.ofReal (vecSqAvg (originCube d (S.m : ℤ))
                    (fun x => matVecMul
                      ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (gluedGradientField hnu S.ell S.n S.m
                        (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde))
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
  obtain ⟨C, hC1, hmain⟩ :=
    l_RHS_term1_of_anchors_constFirst_memLp d _hd Cloc hCloc Cc hCc
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    HD qTilde hMeasGradW hMeasFlux hMeasH1 hMeasHminus hMeasDepth
    hMeasL2 hMeasStep2 hLocMin hMeasCoeff hMeasDeriv hJensen hQTilde hConcDepth
    hPigeon
  exact hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder hPigeon e he
    (testVector nu S.LPrime P S.n e) rfl w hw HD
    (fun omega : ShellSeq d =>
      aestronglyMeasurable_hessCarrier (originCube d (S.m : ℤ)) (HD omega))
    (gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (gluedGradientField hnu S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e))
    (qVector hnu P S.LPrime S.ell S.n S.m (fluxSlot nu S.LPrime P S.n e)) qTilde
    hMeasGradW hMeasFlux hMeasH1 hMeasHminus hMeasDepth hMeasL2 hMeasStep2
    hLocMin hMeasCoeff hMeasDeriv hJensen hQTilde hConcDepth rfl rfl

end

end SuperdiffusionCLT.Section3.Terms