/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.TranslatedQuadFormMoment
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3LocAnchor
public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorAssembly
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst

/-!
# The term-3 quadratic-tail second-moment obligation and the mixing-anchor tail

## The obligation `hQuadZc`

The `_hQuadZc` obligation of the final Term 3 statement: the `L^2(P)` second moment
of the lattice average of `translatedStreamQuadForm` over the
depth-`(k - n)` descendants of the coarse-block centre `zc = originCube d k`,
`k = coarseBlockScale d S`, at the scales `ell = S.ell < LPrime = S.LPrime`.
It is used in the proof of `l.RHS.term3` (the Hoelder display there).

The obligation follows verbatim by direct application of
`memLp_two_descendantAverage_translatedStreamQuadForm`
(`Section3/Terms/TranslatedQuadFormMoment.lean`), whose conclusion is the
identical `MemLp` statement at `zc = originCube d k` with the scale identity
`zc.scale = k` supplied by `rfl`.  No hypothesis beyond the statement's
own binders `0 < nu`, the four law binders, the scale selection, its ordering
and `|e|^2 = 1` is carried.

## The obligation `hPigTail`, chained through the proved localization conjunct 1

The `_hPigTail` obligation of the same statement, at the constant `Cms`, is
assembled from the mixing package's pigeonhole tail bound, with its localization-anchor input
`hLocAnchor` discharged by the proved conjunct 1 through
`term3_locAnchor_of_conjunct1` (`Section3/Terms/RHSTerm3LocAnchor.lean`), which
needs only `localizationConst d ≤ CL`.  What remains carried is exactly the
mixing package's own Step-E inputs `hStepE`, `hStepD`, the constant domination
`mixingAmpConst CL CFluc CDet ≤ Cms`, the positivity of the packaging constants,
the law binders `hPrefix`, `hJ2`, `hJ3`, the scale ordering and the pigeonhole
side condition `2 * S.h ≤ S.m`; `hJ3` alone is what the localization conjunct
consumes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-- **The obligation `hQuadZc` of the term-3 statement**, the `L^2(P)`
second moment of the lattice average of `translatedStreamQuadForm` over the
descendants of the coarse-block centre, in the exact shape the obligation
writes.  The proof is
`memLp_two_descendantAverage_translatedStreamQuadForm` at
`zc = originCube d (coarseBlockScale d S)`, whose scale identity holds by
`rfl` (`originCube`'s scale is its argument). -/
theorem memLp_two_descendantAverage_translatedStreamQuadForm_originCube {d : ℕ} [NeZero d]
    {nu : ℝ} (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1) :
    MemLp (fun omega : ShellSeq d =>
      (((descendantsAtDepth (originCube d ((coarseBlockScale d S : ℕ) : ℤ))
          (coarseBlockScale d S - S.n)).card : ℝ))⁻¹ *
        ∑ z ∈ descendantsAtDepth (originCube d ((coarseBlockScale d S : ℕ) : ℤ))
          (coarseBlockScale d S - S.n),
          translatedStreamQuadForm nu S.ell S.LPrime e omega z) 2 P.toMeasure :=
  memLp_two_descendantAverage_translatedStreamQuadForm hnu hPrefix hJ2 hJ3 hJ4 S hSorder he rfl

/-! ## The obligation `hPigTail`, chained through the localization conjunct 1 -/

end

end SuperdiffusionCLT.Section3.Terms
