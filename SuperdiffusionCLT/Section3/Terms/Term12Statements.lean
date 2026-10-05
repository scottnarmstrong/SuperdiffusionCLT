/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationUnconditional
public import SuperdiffusionCLT.Section3.Terms.ConcHbd
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2LocMin
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Statement

/-!
# The forms of `l.RHS.term1` and `l.RHS.term2` that follow from the localization anchor

The localization anchor `Frozen/Section2/CutoffLocalization.lean` is proved: its conclusion is
the theorem
`SuperdiffusionCLT.Section2.Localization.cutoff_localization_unconditional`
(in `Section2/Localization/LocalizationUnconditional.lean`), which carries nothing
beyond `d`, `[NeZero d]` and `hd : 2 ≤ d`.  Term 2 needs only `hLocMinEx`; term
1 needs only `_hLocMin` together with the pigeonhole side condition
`_hPigeon`.  This module extracts the shared clause from the anchor and proves the
two statements verbatim.

## The shape of the clause the two terms read

The anchor's conclusion is

`∃ C, ∀ nu, 0 < nu → nu ≤ 1 → ∀ P, laws → ∀ m n L, n ≤ m → m ≤ L → ∀ U ⊆ cu_n,
conj1 ∧ conj2 ∧ conj3`

with

* `conj1` — the symmetric sandwich `e.localization.s.star`:
  `∃ X, Measurable X ∧ IsBigO … X … ∧ ∀ omega, (four Loewner comparisons)`;
* `conj2` — the unsymmetric sandwich `e.skbounds`:
  `∃ Y, Measurable Y ∧ IsBigO … Y … ∧ ∀ omega p q, 2 p·H q ≤ Y omega (…)`;
* `conj3` — the maximizers `e.localization.minimizers`:
  `∀ omega p q u v, hu → hv →
  volumeAverage ‖∇u − ∇v‖² ≤ C ν⁻² 3ⁿ · (sSup window) · (J + J + 2 p·q)`.

Neither term reads `conj1` or `conj2`.  Both read exactly `conj3`, at the anchor's
own constant and at the anchor's own scales, specialized to the scale triple
`(m, n, L) = (S.ell, S.n, S.LPrime)`: the scale relation `S.n ≤ S.ell ≤ S.LPrime`
is read off `ScalesOrdering S`, and the anchor's literal `sSup` window is the
carrier `anchorDerivSup S.ell S.LPrime S.n omega'`, which is `rfl`-equal to that
`sSup` render (`anchorDerivSup_eq`), so no premise changes hands in the reading.

That extraction is the reduction
`RHSTerm2LocMin.term2_hLocMin_of_localization`, applied here to
`cutoff_localization_unconditional`.  Its conclusion is, on the term-2 side, verbatim
the hypothesis `hLocMinEx` of
`RHSTerm2Statement.rhs_term2_statement_of_localization`, and, on the term-1
side, verbatim the `_hLocMin` obligation of
`ConcHbd.term1_close_of_shellLaws` at the anchor's own constant.  The two terms
read the identical clause — there are no term-specific carriers — so the same
extraction serves both.  The only asymmetry is that `term1_close_of_shellLaws`
takes the localization constant `Cloc` as a parameter, so the anchor's
existential constant is introduced before it, never assumed.

## Main results

* `rhs_term2_statement` — the `l.RHS.term2` conclusion, no premise
  beyond `d`, `[NeZero d]`, `hd : 2 ≤ d`.
* `rhs_term1_statement` — the `l.RHS.term1` conclusion, no premise
  beyond `d`, `[NeZero d]`, `hd : 2 ≤ d`, including the pigeonhole side
  condition `_hPigeon`, which stays a premise of the printed statement.

Dimension one is out of scope; everything stays averaged.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-- **The `l.RHS.term2` conclusion.**

The statement of `Frozen/Section3/RHSTerm2.lean`
with only the declaration name changed.  `hLocMinEx` is supplied by the anchor:
`RHSTerm2LocMin.term2_hLocMin_of_localization` turns the conclusion of
`cutoff_localization_unconditional` — the anchor's third conjunct `conj3`, at the
scales `(m, n, L) = (S.ell, S.n, S.LPrime)` — into that clause, and
`RHSTerm2Statement.rhs_term2_statement_of_localization` consumes it.  The
anchor's existential constant is the `Cloc` of the clause, and the outer
`∃ C` with `1 ≤ C` is the one of the printed statement.  Nothing beyond `d`,
`[NeZero d]` and `hd : 2 ≤ d` stands before `∃ C`. -/
theorem rhs_term2_statement (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
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
  rhs_term2_statement_of_localization d hd
    (term2_hLocMin_of_localization d hd
      (SuperdiffusionCLT.Section2.Localization.cutoff_localization_unconditional d hd))

/-- **The `l.RHS.term1` conclusion.**

The statement of `Frozen/Section3/RHSTerm1.lean`
with only the declaration name changed, including the pigeonhole side condition
`_hPigeon : 2 * S.h ≤ S.m` of the printed statement.  The single obligation of
`ConcHbd.term1_close_of_shellLaws`, its `_hLocMin`, is discharged from the
anchor: the anchor's existential constant is taken as `Cloc`, and its third
conjunct — the maximizer clause, at the scales `(m, n, L) = (S.ell, S.n,
S.LPrime)` — is the clause itself, the anchor's `sSup` window being the
`rfl`-equal carrier `anchorDerivSup`.  Nothing beyond `d`, `[NeZero d]` and
`hd : 2 ≤ d` stands before `∃ C`. -/
theorem rhs_term1_statement (d : ℕ) [NeZero d] (_hd : 2 ≤ d) :
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
  obtain ⟨Cloc, hCloc⟩ :=
    term2_hLocMin_of_localization d _hd
      (SuperdiffusionCLT.Section2.Localization.cutoff_localization_unconditional d _hd)
  obtain ⟨C, hC1, hmain⟩ := term1_close_of_shellLaws d _hd Cloc
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw hPigeon
  refine hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw ?_ hPigeon
  intro U hU omega' p q u v hu hv
  exact hCloc nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder U hU omega' p q u v hu hv

end

end SuperdiffusionCLT.Section3.Terms
