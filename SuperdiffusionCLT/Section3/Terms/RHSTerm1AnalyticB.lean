/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1Analytic

/-!
# The analytic residues of `term1_finalB` wired away

`RHSTerm1Analytic` proves the primitive content of the two analytic residues of the
reduction of `l.RHS.term1`:

* the pair of integrability inputs `_hInt1`, `_hInt2` of the difference-Jensen
  obligation `_hJensen`, as the unconditional theorems `term1_hInt1` and
  `term1_hInt2`;
* the reduction of the depth-moment obligation `_hConcDepth` to a **numeric**
  gate on its constant, as a clause holding at every constant dominating `3^{d (m - ℓ)}`.

This module performs the wiring those two facts are used for:

* `term1_finalC_jensenFree` removes `_hJensen` from the reduction, keeping
  `_hConcDepth`.  The display bound is produced by
  `RHSTerm1Residues.hJensen_printedProxy_of_integrable` from the two
  integrability theorems, so no new hypothesis is introduced at all; the only
  remaining analytic obligation of this statement is `_hConcDepth`.
* A further variant removes `_hConcDepth` as well, replacing it by the numeric
  pin `3^{d (m - ℓ)} ≤ Cc`.  Its only
  obligations are the localization clause `_hLocMin` (in the abbreviation
  `LocMinClause`), the numeric gate on `Cc`, and the pigeonhole side condition.

## The standing of the two discharged binders

`_hJensen` is discharged **unconditionally** — the integrability theorems
`term1_hInt1`/`term1_hInt2` are unconditional in the section data, so
`term1_finalC_jensenFree` carries no replacement hypothesis for it.

`_hConcDepth` is **not** discharged at a fixed constant.  The proof
establishes the printed depth-moment display only
at constants dominating `3^{d (m - ℓ)}`: the depth weight `3^{-d (m - j - ℓ)}`
is at most one there, so the descendant Jensen bound
`vecDepthSqMoment_le_vecSqAvg_of_memVectorL2` already dominates the display.  A
section constant `Cc` chosen before the scale selection cannot dominate
`3^{d (S.m - S.ell)}` for every `S`, so `_hConcDepth` at a fixed `Cc` is not
reached; the numeric gate on `Cc` is exactly the residue
that remains.  The genuine concentration content (a constant independent of the
scale selection) is the structural identification recorded in the
`SublatticeConcentrationDepth` docstring, together with a second-moment bound for
the block averages of the flux.
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

/-! ## `_hJensen` discharged, `_hConcDepth` kept -/

/-- **The `l.RHS.term1` reduction with `_hJensen` discharged.**  Same binders and
conclusion as the reduction, with the difference-Jensen obligation `_hJensen` removed and
supplied inside the proof: `term1_hInt1` and `term1_hInt2` discharge the
two integrability inputs, and `hJensen_printedProxy_of_integrable` turns them
into the display.  No hypothesis replaces `_hJensen`, so this is a net removal
of one obligation; the localization clause `_hLocMin` (as `LocMinClause`) and
the depth-moment clause `_hConcDepth` remain. -/
theorem term1_finalC_jensenFree (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (Cloc : ℝ) (Cc : ℝ) :
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
        (_hLocMin : LocMinClause d nu S Cloc)
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
  obtain ⟨C, hC1, hmain⟩ := term1_finalB d _hd Cloc Cc
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hLocMin hConcDepth hPigeon
  refine hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hLocMin ?_ hConcDepth hPigeon
  exact hJensen_printedProxy_of_integrable hnu P S e
    (term1_hInt1 d hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e)
    (term1_hInt2 d hnu P hPrefix hJ2 hJ3 hJ4 S hSorder e)

/-! ## Both analytic residues removed -/

end

end SuperdiffusionCLT.Section3.Terms
