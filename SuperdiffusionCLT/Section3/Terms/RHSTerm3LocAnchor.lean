/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffLoewnerClauses
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3

/-!
# The term-3 localization-anchor obligation

The `_hLocAnchor` obligation of the term-3 statement: the two `MatLoewnerLE`
clauses of the localization anchor on `sigmaStarInvCoarse`, at the constant
`CL` carried by the term-3 statement's own constant binders, in the exact
binder shape the obligation writes (the universal quantifiers over the triple
`mm nn LL` and the domain `U` first, the existential witness last).

The source is `l.localization` in the paper, first summand
`e.localization.s.star` in the sandwich reading, clause (ii): with
`A = s_{L,*}^{-1}(U) = sigmaStarInvCoarse` at `L` and
`M = sigmaStarInvCoarse` at `m`, the comparison
`|A^{-1/2} M A^{-1/2} - Id| ≤ t` becomes the two-sided Loewner pair
`(1 - X) sStarInv_m ≤ sStarInv_L ≤ (1 + X) sStarInv_m`, the second and fourth
of the four clauses the proved conjunct 1
`cutoffLocalizationConjunct1`
(`Section2/Localization/CutoffLoewnerClauses.lean`) delivers -- the first
two of its four clauses are the companion pair on `sigmaCoarse`, which the
term-3 chain does not read and which this module simply drops.

## What is proved here

`term3_locAnchor_of_conjunct1`: the obligation, verbatim, from the proved
conjunct 1.  The derivation is a two-line composition:

* the witness `X` of the conjunct and its last two `MatLoewnerLE` clauses are
  taken as they stand (the clause conjunction of the conjunct is right
  associative, so `.2.2` is exactly the `sigmaStarInvCoarse` pair, with the
  conjunct's `n, m, L` read as the obligation's `nn, mm, LL`);
* the amplitude constant is bridged from the packaging constant
  `localizationConst d` of the conjunct to the obligation's own `CL` by
  `IsBigO.mono_scale`, the hypothesis being
  `localizationConst d ≤ CL` and the factors `nu ^ (-2)` and
  `3 ^ (-(mm - nn))` nonnegative.

The `mono_scale` bridge needs `localizationConst d ≤ CL`; the obligation's
other constant datum `0 < CL` is carried alongside but not needed for it
(`localizationConst d` is nonnegative, so the comparison hypothesis already
forces `CL ≥ 0`).  A term-3 consumer that picks its localization constant
`CL` at least `localizationConst d` -- the natural choice, since the swap
constant `swapConst d C_reg CL` that consumes the anchor grows in `CL` --
obtains the obligation by direct application.
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

/-- **The term-3 localization-anchor obligation, from the proved conjunct 1.**
The two `MatLoewnerLE` clauses of the localization anchor on
`sigmaStarInvCoarse`, in the exact binder shape of the `_hLocAnchor`
obligation of the term-3 statement, at the obligation's own
constant `CL`.  The constant comparison is `localizationConst d ≤ CL`: the
proved conjunct `cutoffLocalizationConjunct1`
(`Section2/Localization/CutoffLoewnerClauses.lean`) gives the same
sandwich pair at the packaging constant `localizationConst d`, and the tail
bound is upgraded to `CL` by `IsBigO.mono_scale`, the rate factors
`nu ^ (-2)` and `3 ^ (-(mm - nn))` being nonnegative.  The obligation's
companion constant datum `0 < CL` (carried by the consuming statements) is
not needed by the bridge: the comparison hypothesis already forces
`CL ≥ localizationConst d ≥ 0`. -/
theorem term3_locAnchor_of_conjunct1
    (d : ℕ) (CL : ℝ)
    (hloc : SuperdiffusionCLT.Section2.Localization.localizationConst d ≤ CL)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
    (hJ3 : ShellLawJ3 d P) :
    ∀ mm nn LL : ℕ, nn ≤ mm → mm ≤ LL →
      ∀ U : Book.Ch02.Domain d,
        (U : Set (Vec d)) ⊆ openCubeSet (originCube d (nn : ℤ)) →
        ∃ X : ShellSeq d → ℝ,
          Measurable X ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
              (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - nn : ℕ) : ℝ))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                  ((1 - X omega) •
                    sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega mm).toCoeffField)
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega LL).toCoeffField) ∧
                MatLoewnerLE
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega LL).toCoeffField)
                  ((1 + X omega) •
                    sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega mm).toCoeffField) := by
  intro mm nn LL hnm hmL U hU
  -- the proved conjunct 1, at the packaging constant `localizationConst d`
  obtain ⟨X, hXmeas, hXbigO, hXclauses⟩ :=
    SuperdiffusionCLT.Section2.Localization.cutoffLocalizationConjunct1
      P hJ3 nu hnu hnu1 nn mm LL hnm hmL U hU
  -- the two `sigmaStarInvCoarse` clauses, verbatim the obligation's pair
  refine ⟨X, hXmeas, ?_, fun omega => (hXclauses omega).2.2⟩
  -- the constant bridge: the packaging constant is dominated by `CL`, and the
  -- rate factors are nonnegative
  exact hXbigO.mono_scale (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hloc (Real.rpow_nonneg (le_of_lt hnu) _))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))

end

end SuperdiffusionCLT.Section3.Terms