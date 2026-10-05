/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorFinal
public import SuperdiffusionCLT.Section3.Setup.Parameters

/-!
# `_hPigTail` at the mixing statement's own constant, named at `d`

## The two statements, side by side

The mixing statement `sigmaStarInv_mixing_minscale_closed`
(`Section2/Annealed/MixingAnchorFinal.lean`, first conjunct) is

> `∃ CM, 0 < CM ∧ ∀ nu, 0 < nu → nu ≤ 1 → ∀ P, <the five shell laws> →`
> `  ∀ h n l, h < n → n ≤ l →`
> `    ∃ X, Measurable X ∧ IsBigO P.toMeasure (gammaSigma 2) X`
> `        (CM * nu ^ (-2) * 3 ^ (-((n - h) / 4))) ∧`
> `    ∀ omega, MatLoewnerLE`
> `      (sigmaStarInvCoarse (cubeSet (originCube d n)) (coefficientCutoff nu omega l).toCoeffField)`
> `      (sigmaBarStarInv nu l P (cubeSet (originCube d h)) + X omega • 1)`

and the obligation `_hPigTail` of the final Term 3 statement is, at the telescope above it,

> `∃ Xms, Measurable Xms ∧ IsBigO P.toMeasure (gammaSigma 2) Xms`
> `    (Cms * nu ^ (-2) * 3 ^ (-(((S.n - (S.m - 2 * S.h)) / 4)))) ∧`
> `  ∀ omega, MatLoewnerLE`
> `    (sigmaStarInvCoarse (cubeSet (originCube d S.n)) (coefficientCutoff nu omega S.LPrime).toCoeffField)`
> `    (sigmaBarStarInv nu S.LPrime P (cubeSet (originCube d (S.m - 2 * S.h))) + Xms omega • 1)`

Read the mixing statement at the triple `(h, n, l) := (S.m - 2 * S.h, S.n, S.LPrime)`,
and the correspondence is exact item by item:

| item | mixing statement | `_hPigTail` | verdict |
|---|---|---|---|
| cube scale of `sigmaStarInvCoarse` | `n` | `S.n` | same |
| cutoff of `coefficientCutoff` | `l` | `S.LPrime` | same |
| cube scale of `sigmaBarStarInv` | `h` | `S.m - 2 * S.h` | same |
| Orlicz index | `gammaSigma 2` | `gammaSigma 2` | same |
| exponent | `((n - h : ℕ) : ℝ) / 4` | `(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ)) / 4` | same |
| amplitude | `CM` | `Cms` | **only mismatch** |
| Loewner direction | `sigmaStarInvCoarse ≤ sigmaBarStarInv + X • 1` | identical | same |
| side conditions | `h < n`, `n ≤ l` | `S.m - 2 * S.h < S.n`, `S.n ≤ S.LPrime` | supplied below |

The two exponents agree **as written**, not merely up to a rewriting: both are
the `ℕ`-truncated difference cast to `ℝ`, and the anchor's conclusion is a
function of its `h`, so plugging in the numeral `S.m - 2 * S.h` reproduces the
obligation's exponent and the obligation's `sigmaBarStarInv` cube together.

## The single mismatch: the amplitude constant

`CM` is existential at `d`; `Cms` is a free binder of the final Term 3 statement
carrying only `hCms : 0 < Cms`, and it sits **above** the whole telescope
(before `nu`, `P` and `S`).  The conclusion is
monotone in that constant — a larger amplitude weakens the `IsBigO` conjunct
and leaves the pointwise Loewner conjunct unchanged — so the mixing statement yields
`_hPigTail` at any `Cms` dominating `CM`, and gives nothing at a smaller one.

This module therefore does not *choose* the constant per instance: it names the
constant of the mixing statement at `d` alone, in `term3PigTailMixConst d`, normalised to be
positive.  `term3_pigTail_of_mixAnchor` is the `_hPigTail` conclusion verbatim
at that named constant, with the telescope as its only binders, so it can be
instantiated directly at the `Cms` of the final Term 3 statement when `Cms` is that value,
and `term3_pigTail_of_mixAnchor_le` is the same conclusion at every larger
`Cms`.  No domination hypothesis and no localization hypothesis remains — and
no `2 ≤ d` either: the mixing statement needs only `[NeZero d]`, so the
discharge carries strictly fewer hypotheses than the binder of the final Term 3 statement
needs.

## The scale bookkeeping, and a required binder

The anchor's side condition `h < n` becomes `S.m - 2 * S.h < S.n`.
`ScalesOrdering` does **not** give this: its first field is the addition-only
`S.m < S.n + 2 * S.h` (the printed `m - 2h < n` moved to `ℤ`), and the printed
truncated form is recovered only under `2 * S.h ≤ S.m`, by
`ScalesOrdering.m_sub_two_mul_h_lt_n`.  The binder `_hTwoHLeM` is exactly
that hypothesis, so it is **load-bearing here**:
`exists_scalesOrdering_not_m_sub_two_mul_h_lt_n` below exhibits a `ScaleSelection`
that satisfies `ScalesOrdering` in full and for which `S.m - 2 * S.h < S.n` is
FALSE.  The binders `_hHundredALeH` and `_hWindowVsOffset` play no role in this
discharge; they are carried by the final Term 3 statement for other obligations.

The anchor's second side condition `n ≤ l` becomes `S.n ≤ S.LPrime`, which does
follow from `ScalesOrdering` alone through `n < ℓ < ℓ' < m < L'`.
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
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## The anchor's constant, named at `d` alone -/

/-- **The mixing statement's constant, named.**  It is the existential constant of
`sigmaStarInv_mixing_minscale_closed`, normalised to be positive by `max · 1`;
it depends on `d` alone, hence can be substituted into the `Cms` binder of
the final Term 3 statement, which is quantified above the whole telescope `nu`, `P`, `S`. -/
noncomputable def term3PigTailMixConst (d : ℕ) [NeZero d] : ℝ :=
  max (Classical.choose
    (SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed d)) 1

/-- The defining equation of the named constant, so that no consumer has to
unfold the definition to see which constant it is. -/
theorem term3PigTailMixConst_def (d : ℕ) [NeZero d] :
    term3PigTailMixConst d =
      max (Classical.choose
        (SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed d)) 1 :=
  rfl

/-- The named constant is positive. -/
theorem term3PigTailMixConst_pos (d : ℕ) [NeZero d] : 0 < term3PigTailMixConst d := by
  rw [term3PigTailMixConst_def]
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

/-- The named constant dominates the anchor's own constant, which is the form in
which the anchor's conclusion is read below. -/
theorem choose_le_term3PigTailMixConst (d : ℕ) [NeZero d] :
    Classical.choose
        (SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed d) ≤
      term3PigTailMixConst d := by
  rw [term3PigTailMixConst_def]
  exact le_max_left _ _

/-! ## The scale bookkeeping of `_hSorder` and `_hTwoHLeM` -/

/-- **The first side condition of the mixing statement.**  The printed `m - 2h < n`
at the binders of the final Term 3 statement: from the addition-only field `S.m < S.n + 2 * S.h` of
`ScalesOrdering` together with `_hTwoHLeM : 2 * S.h ≤ S.m`.  The second binder
is not decoration, as the witness further down shows. -/
theorem term3PigTail_m_sub_two_mul_h_lt_n {S : ScaleSelection}
    (hSorder : ScalesOrdering S) (hm2h : 2 * S.h ≤ S.m) :
    S.m - 2 * S.h < S.n :=
  hSorder.m_sub_two_mul_h_lt_n hm2h

/-- **The anchor's second side condition.**  `n ≤ l` at `l := S.LPrime`,
straight from the strict chain `n < ℓ < ℓ' < m < L'` of `ScalesOrdering`; no
further binder is needed. -/
theorem term3PigTail_n_le_LPrime {S : ScaleSelection} (hSorder : ScalesOrdering S) :
    S.n ≤ S.LPrime := by
  have h1 := hSorder.n_lt_ell
  have h2 := hSorder.ell_lt_ellPrime
  have h3 := hSorder.ellPrime_lt_m
  have h4 := hSorder.m_lt_LPrime
  omega

/-- **`ScalesOrdering` alone does NOT give the printed `m - 2h < n`.**  The
selection `L = 10`, `m = 7`, `h = 5`, `a = 1` satisfies every field of
`ScalesOrdering` — `7 < 0 + 2 · 5`, `0 < 1 < 2 < 7 < 9 < 10` — and has
`S.m - 2 * S.h = 7 - 10 = 0` and `S.n = 0`, so the printed inequality is false
there.  This is what makes `_hTwoHLeM : 2 * S.h ≤ S.m` a required input of the
scale bookkeeping rather than a convenience: the strict chain constrains `m`
from above only, while `m - 2h` is a truncated difference. -/
theorem exists_scalesOrdering_not_m_sub_two_mul_h_lt_n :
    ∃ S : ScaleSelection, ScalesOrdering S ∧ ¬ (S.m - 2 * S.h < S.n) := by
  refine ⟨ScaleSelection.ofBase 10 7 5 1 (by norm_num), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ScaleSelection.ofBase] <;> norm_num
  · simp only [ScaleSelection.ofBase]
    norm_num

/-! ## `_hPigTail` at the named constant, and at every larger one -/

/-- **`_hPigTail` at the mixing statement's own constant, from that statement
alone.**  The conclusion is the `_hPigTail` binder of the final Term 3 statement verbatim, at
`Cms := Cms` for any `Cms` dominating the named constant
`term3PigTailMixConst d`: the mixing statement is read at
the triple `(h, n, l) = (S.m - 2 * S.h, S.n, S.LPrime)`, whose two side
conditions are `term3PigTail_m_sub_two_mul_h_lt_n` (using `_hTwoHLeM`) and
`term3PigTail_n_le_LPrime`, and its `IsBigO` amplitude is enlarged to `Cms`.
Nothing beyond `d`, `[NeZero d]` and the telescope is carried; in particular
there is no localization hypothesis. -/
theorem term3_pigTail_of_mixAnchor_le {d : ℕ} [NeZero d] {Cms : ℝ}
    (hCms : term3PigTailMixConst d ≤ Cms) :
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
        ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ S : ScaleSelection, ScalesOrdering S → 2 * S.h ≤ S.m →
          ∃ Xms : ShellSeq d → ℝ, Measurable Xms ∧
            IsBigO P.toMeasure (gammaSigma 2) Xms
              (Cms * nu ^ (-(2 : ℝ)) *
                (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ) / 4))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                (sigmaStarInvCoarse (cubeSet (originCube d (S.n : ℤ)))
                  (coefficientCutoff nu omega S.LPrime).toCoeffField)
                (sigmaBarStarInv nu S.LPrime P
                    (cubeSet (originCube d ((S.m - 2 * S.h : ℕ) : ℤ))) +
                  Xms omega • (1 : Mat d)) := by
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 S hSorder hm2h
  have hh : S.m - 2 * S.h < S.n := term3PigTail_m_sub_two_mul_h_lt_n hSorder hm2h
  have hnl : S.n ≤ S.LPrime := term3PigTail_n_le_LPrime hSorder
  have hanchor :=
    (Classical.choose_spec
      (SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed d))
  obtain ⟨X, hXm, hXbig, hXconj⟩ :=
    (hanchor nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4).1
      (S.m - 2 * S.h) S.n S.LPrime hh hnl
  refine ⟨X, hXm, hXbig.mono_scale ?_, hXconj⟩
  have hcle : Classical.choose
      (SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed d) ≤
      Cms := le_trans (choose_le_term3PigTailMixConst d) hCms
  have h1 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ) / 4)) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcle h1) h2

/-- **The obligation `_hPigTail` at the named constant, VERBATIM.**  This is
`term3_pigTail_of_mixAnchor_le` at `Cms := term3PigTailMixConst d`, i.e. the
`_hPigTail` binder of the final Term 3 statement with its amplitude constant instantiated at
the constant of the mixing statement, named at `d` alone.  Its binders are exactly
`d`, `[NeZero d]` and the ambient telescope.  **`hd : 2 ≤ d` is not carried**, and
cannot be: the mixing statement needs only `[NeZero d]`, so this discharge is
strictly weaker in its hypotheses than the `_hPigTail` binder of the final Term 3 statement
requires, and so applies inside that statement's telescope at every `d ≥ 2`. -/
theorem term3_pigTail_of_mixAnchor (d : ℕ) [NeZero d] :
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
        ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ S : ScaleSelection, ScalesOrdering S → 2 * S.h ≤ S.m →
          ∃ Xms : ShellSeq d → ℝ, Measurable Xms ∧
            IsBigO P.toMeasure (gammaSigma 2) Xms
              (term3PigTailMixConst d * nu ^ (-(2 : ℝ)) *
                (3 : ℝ) ^ (-(((S.n - (S.m - 2 * S.h) : ℕ) : ℝ) / 4))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                (sigmaStarInvCoarse (cubeSet (originCube d (S.n : ℤ)))
                  (coefficientCutoff nu omega S.LPrime).toCoeffField)
                (sigmaBarStarInv nu S.LPrime P
                    (cubeSet (originCube d ((S.m - 2 * S.h : ℕ) : ℤ))) +
                  Xms omega • (1 : Mat d)) :=
  term3_pigTail_of_mixAnchor_le (d := d) le_rfl

/-! ## Witnesses -/

/-- Witness at `d = 2`: the named constant is positive. -/
example : 0 < term3PigTailMixConst 2 := term3PigTailMixConst_pos 2

/-- Witness at `d = 2`: the named constant dominates the anchor's own constant,
so `term3_pigTail_of_mixAnchor` is the mixing statement read at its own value and not at
an inflated one. -/
example : Classical.choose
    (SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed 2) ≤
    term3PigTailMixConst 2 :=
  choose_le_term3PigTailMixConst 2

/-- Witness: the two scale conditions of the mixing statement at the binders of
the final Term 3 statement are not the same statement — the first needs `_hTwoHLeM`, the second
does not. -/
example : ∃ S : ScaleSelection, ScalesOrdering S ∧ ¬ (S.m - 2 * S.h < S.n) :=
  exists_scalesOrdering_not_m_sub_two_mul_h_lt_n

end

end SuperdiffusionCLT.Section3.Terms
