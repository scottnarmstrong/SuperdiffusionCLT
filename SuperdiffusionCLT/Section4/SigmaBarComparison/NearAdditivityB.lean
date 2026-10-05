/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityA
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# The witness `n` and its bookkeeping

In the proof of `l.shomm.vs.shomell` (near-additivity step) the witness is
`n := ell - ⌈200 log L⌉` (truncated at `0`); this
file names it (`sbNear_witness`) and proves the two bookkeeping conjuncts of
`hGoodN` (see `sbIndep_mainB` in `IndependenceRatioF.lean`) it must satisfy unconditionally
(`sbNear_witness_le`, `sbNear_witness_gap_le`).

## The conjuncts of `hGoodN`

`hGoodN`'s seven conjuncts are, in order: near-additivity, `hCI3`, the scalar
`sigmaBarStarInvScalar` nonnegativity, its `≤ C2 shom_ell⁻¹` comparison, the
`7/8` lower bound on `sigmaBarSeq ... n`, `n ≤ ell`, and the gap bound. Four of
these seven are discharged here unconditionally: `hCI3` (`sbNear_hCI3`,
`NearAdditivityA.lean`), the nonnegativity (`sigmaBarStarInvScalar_pos`),
and the two bookkeeping conjuncts (below).

The remaining three (near-additivity itself, and the two `p.homog.below`-pair
comparisons) are carried as two explicit hypotheses, `hNearAdd` and `hHomogPair`:

* Near-additivity rests on `e.localization.ml` (the gauge-conjugation identity from the
  *proof* of `l.localization`), which gives a two-sided quadratic-form comparison
  with an explicit quadratic and cross term. (The Loewner-sandwich consequence of
  `e.localization.s.star` in `cutoff_localization` does not suffice: near-additivity needs
  the sharper additive display with an explicit quadratic term, later bounded by the `p=2`
  moment `e.kmn.bounds`. And `localization_average` has the wrong shape: it compares the fine
  matrix on many small subcubes tiling a larger cube `cu_m` with a single annealed reference,
  with scale hypothesis `n ≤ l ≤ m`, so it cannot degenerate to the single-cube comparison
  `m = n` that `hGoodN` needs, where `n ≤ ell`.) The hypothesis `hNearAdd` is discharged
  by `sbNear_nearAdd` (`NearAdditivityD5.lean`), after `e.localization.ml` is specialized
  in `NearAdditivityC.lean`.
* The `p.homog.below`-pair conjuncts need not just the `homogenization_below_cutoff` body but
  also the smallness threshold work of `l.shomm.vs.shomell#homog-below-bound` to read the
  `ε ≤ 1/8` condition off the raw display at the specific gap `ell - n`; `hHomogPair` states the
  pair's conclusion directly. It is obtained from `homogenization_below_cutoff` in
  `HomogPairOfHomog.lean`.

`sbNear_goodNB` (`NearAdditivityD6.lean`) therefore reduces `hGoodN`'s seven conjuncts to
exactly these two hypotheses, both baked to the same concrete witness
`sbNear_witness ell L`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The witness `n := ell - ⌈200 log L⌉` -/

/-- The witness `n := ell - ⌈200 log L⌉`, truncated at `0`. -/
noncomputable def sbNear_witness (ell L : ℕ) : ℕ :=
  ell - ⌈200 * Real.log (L : ℝ)⌉₊

theorem sbNear_witness_le (ell L : ℕ) : sbNear_witness ell L ≤ ell :=
  Nat.sub_le _ _

theorem sbNear_witness_gap_le (ell L : ℕ) :
    (ell : ℝ) - (sbNear_witness ell L : ℝ) ≤ 200 * Real.log (L : ℝ) + 1 := by
  unfold sbNear_witness
  have hlogL0 : (0 : ℝ) ≤ 200 * Real.log (L : ℝ) := by
    have := Real.log_natCast_nonneg L
    linarith only [this]
  have hceil : (⌈200 * Real.log (L : ℝ)⌉₊ : ℝ) < 200 * Real.log (L : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlogL0
  rcases le_or_gt (⌈200 * Real.log (L : ℝ)⌉₊) ell with hc | hc
  · rw [Nat.cast_sub hc]
    linarith only [hceil]
  · rw [Nat.sub_eq_zero_of_le hc.le]
    have hcle : (ell : ℝ) < (⌈200 * Real.log (L : ℝ)⌉₊ : ℝ) := by exact_mod_cast hc
    push_cast
    linarith only [hcle, hceil]

/-! ## The scalar nonnegativity conjunct -/

theorem sbNear_sigmaBarStarInvScalar_nonneg {P : ProbabilityMeasure (ShellSeq d)}
    {nu : ℝ} (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (ell n : ℕ) :
    0 ≤ sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) := by
  have hInt := SuperdiffusionCLT.Section2.Annealed.integrable_coarseBlockMatrix_lowerRight
    hnu ell (originCube d (n : ℤ)) hPrefix hJ2 hJ3 hJ4
  exact (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar_pos
    hnu ell hJ4 (n : ℤ) hInt).le

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
