/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarLowerBoundWorkB
public import SuperdiffusionCLT.Section3.Terms.SstarLowerBoundWork
public import SuperdiffusionCLT.Section2.Localization.LocalizationUnconditional
public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorFinal

/-!
# Consuming the two Section 2 anchors, and the named packaged constant

This file belongs to the proof of `p.sstar.lower.bound` (Section 3), whose statement is
`Frozen.Section3.sigmaBarStar_lower_bound`.  The files `Terms/SstarLowerBoundWork.lean` and
`Terms/SstarLowerBoundWorkB.lean` give its first conjunct
`sigmaBarStarScalar nu L P (cu_m) <= sigmaBarInfinite nu L P` and the assembly's packaged
constant.

The two Section 2 anchors used by the assembly are theorems: the localization anchor
`hLocAnchor` is
`Section2.Localization.cutoff_localization_unconditional (d) [NeZero d] (hd : 2 <= d)`, and the mixing
anchor `hMix` is `Section2.Annealed.sigmaStarInv_mixing_minscale_closed (d) [NeZero d]` (no
`2 <= d` is needed).  This file consumes both in the exact binder shapes that
the assembly and `sstar_lower_bound_quenched_of_anchors` (of
`Section3/Setup/RootLocalizationBridgesB.lean`) want, so neither anchor is a hypothesis any
more.

## Main results

* `sstarClose_locAnchor_unconditional` — the localization anchor, discharged;
* `sstarClose_mixAnchor_unconditional` — the mixing anchor, discharged;
* `sstarCloseConst` — the packaged constant, named, depending only on `d` and a pair of anchor
  bounds, together with `sstarCloseConst_pos`, `sstarCloseConst_le_half`,
  `sstarCloseConst_le_packConst` and the transfer
  `sstarCloseConst_mul_le_of_packConst_mul_le`;
* `sstarCloseThrConst` — the proposition's threshold constant, named, with
  `one_le_sstarCloseThrConst`;
* `sstarCloseCL` — the localization constant, reachable at `d` alone by `Classical.choose`, with
  its positivity.

## The constant-first packaging

The proposition quantifies its constant `c` before every datum, so the constant has to be a
function of `d` alone.  The assembly's constant `sstarPackConst d CM CB` depends on the two anchor
constants `CM` (the master-inequality constant) and `CB` (the homogenization constant); the named
constant `sstarCloseConst d cbMax cmMax` is the same assembly constant evaluated at a pair of
*bounds* `cbMax` for `CB` and `cmMax` for `CM`, with `cmMax` in the first slot and `cbMax` in the
second.  Its only free variables are `d`, `cbMax` and `cmMax`: `nu`, `cStar`, the J5 constant `K`,
the law `P` and the scales `L`, `m` do not occur.  A bound for the anchors suffices, and at the
anchors' own values the transfer is trivial.

Anchors stated `∃ C, 0 < C ∧ ∀ data, …` at fixed `d` hand over their constant by
`Classical.choose`; `sstarCloseCL` does this for the localization anchor.  The constants `CM` and
`CT` are produced only inside the Section 3 final statement as
`∃ CB CM CT : ℝ, …` below fifteen data-dependent constants, so they are not reachable at `d`
alone by this method; this is a matter of the placement of the existential rather than of the
size of the anchors.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## Consuming the localization anchor

`cutoff_localization_unconditional` gives `exists C, forall ...`; the assembly wants
the third and fourth Loewner conjuncts of the first component of that conclusion
at a *positive* constant.  The anchor's conclusion is monotone in its constant
`C` — only the Orlicz amplitudes carry it, and increasing them weakens the
assertion while the pointwise Loewner conjuncts are unchanged — so taking
`max C 1` gives the positivity the assembly asks for. -/

/-- **The localization anchor `hLocAnchor`, discharged.**  The third and fourth
Loewner conjuncts of the conclusion of
`Frozen.Section2.cutoff_localization`, at a positive constant `CL`, with the
anchor's own shell-law binders, obtained from
`Section2.Localization.cutoff_localization_unconditional`.  **No residual
hypothesis** beyond `d`, `[NeZero d]` and `hd : 2 <= d`. -/
theorem sstarClose_locAnchor_unconditional (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ CL : ℝ, 0 < CL ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d), ShellLawPrefix d P →
          ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ mm nn LL : ℕ, nn ≤ mm → mm ≤ LL →
            ∀ U : Book.Ch02.Domain d, (U : Set (Vec d)) ⊆ openCubeSet (originCube d (nn : ℤ)) →
              ∃ X : ShellSeq d → ℝ, Measurable X ∧
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
  obtain ⟨C, hC⟩ :=
    SuperdiffusionCLT.Section2.Localization.cutoff_localization_unconditional d hd
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 mm nn LL hnm hmL U hU
  obtain ⟨X, hXm, hXbig, hXconj⟩ :=
    (hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 mm nn LL hnm hmL U hU).1
  refine ⟨X, hXm, hXbig.mono_scale ?_, fun omega =>
    ⟨(hXconj omega).2.2.1, (hXconj omega).2.2.2⟩⟩
  have h1 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((mm - nn : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h2

/-! ## Consuming the mixing anchor -/

/-- **The mixing anchor `hMix`, discharged.**  The first conjunct of the
conclusion of `Frozen.Section2.sigmaStarInv_mixing_minscale`, at a positive
constant `CM`, obtained from
`Section2.Annealed.sigmaStarInv_mixing_minscale_closed`.  **No residual
hypothesis** beyond `d` and `[NeZero d]`; in particular no `2 <= d`, matching that
theorem. -/
theorem sstarClose_mixAnchor_unconditional (d : ℕ) [NeZero d] :
    ∃ CM : ℝ, 0 < CM ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d), ShellLawPrefix d P →
          ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ h n l : ℕ, h < n → n ≤ l →
            ∃ X : ShellSeq d → ℝ, Measurable X ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
                  (CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
              ∀ omega : ShellSeq d,
                MatLoewnerLE
                    (sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
                      (coefficientCutoff nu omega l).toCoeffField)
                    (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                      X omega • (1 : Mat d)) := by
  obtain ⟨C, hC⟩ :=
    SuperdiffusionCLT.Section2.Annealed.sigmaStarInv_mixing_minscale_closed d
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 h n l hhn hnl
  obtain ⟨X, hXm, hXbig, hXconj⟩ :=
    (hC nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4).1 h n l hhn hnl
  refine ⟨X, hXm, hXbig.mono_scale ?_, hXconj⟩
  have h1 : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
    Real.rpow_nonneg (by norm_num) _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) h1) h2

/-! ## The named packaged constant

`Terms/SstarLowerBoundWorkB.lean` packaged the assembly's constant as
`sstarPackConst d CM CB`, a function of the two *anchor* constants.  The
statement quantifies its `c` before every datum, so the constant that can serve
as the proposition's `c` must be a function of `d` alone; the only missing input
is an elementary (`d`-only) upper bound for the two anchors.  The constant below
is the same assembly constant evaluated at a *named pair of bounds*, and
`sstarCloseConst_le_packConst` proves that such a pair is exactly what suffices.

The argument order is worth stating explicitly, because `sstarLowerBoundConst`'s
first argument is the homogenization constant `CB` while `sstarPackConst`'s first
is the master-inequality constant `CM`: here `cbMax` is the bound for `CB` and
`cmMax` the bound for `CM`.  The constant is `sstarPackConst d cmMax cbMax`,
with the bound for `CM` in the first slot and the bound for `CB` in the second.  By
inspection the definition's only free variables are `d`, `cbMax` and `cmMax`: `nu`, `cStar`,
the J5 binder `K`, the law `P` and the scales `L`, `m` do not occur. -/

/-- **The packaged lower-bound constant of `p.sstar.lower.bound`, named.**  The
assembly's `sstarLowerBoundConst CB (logEnvelopeConst Kfree) 2
(optimalWindowConst Cenv c₀) (2 CM + 1) / 2` with the free scale constant
`Kfree = sstarWorkScaleConst`, the envelope constant
`Cenv = sstarWorkEnvelopeConst d`, `c₀ = sstarWorkC0 cmMax`, and the two anchors
replaced by the bounds `cbMax`, `cmMax`; truncated at `1/2` so that it lies in
the proposition's range `(0, 1/2]`. -/
def sstarCloseConst (d : ℕ) (cbMax cmMax : ℝ) : ℝ :=
  min (sstarLowerBoundConst cbMax (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax))
        (2 * cmMax + 1) / 2) (1 / 2)

theorem sstarCloseConst_pos (d : ℕ) {cbMax cmMax : ℝ} (hcb : 0 < cbMax)
    (hcm : 0 < cmMax) : 0 < sstarCloseConst d cbMax cmMax := by
  refine lt_min ?_ (by norm_num)
  have h := sstarLowerBoundConst_pos hcb logEnvelopeConst_sstarWorkScaleConst_pos
    (show (0 : ℝ) < 2 by norm_num)
    (optimalWindowConst_pos (sstarWorkEnvelopeConst_pos d) (sstarWorkC0_pos hcm))
    (show (0 : ℝ) < 2 * cmMax + 1 by linarith only [hcm])
  linarith only [h]

theorem sstarCloseConst_le_half (d : ℕ) (cbMax cmMax : ℝ) :
    sstarCloseConst d cbMax cmMax ≤ 1 / 2 :=
  min_le_right _ _

/-! ## The monotonicities the packaging rests on

Three of the four are proved here (`sstarWorkC0` is antitone in `CM` because its second
branch is `(1/(8CM))²`; `optimalWindowConst C c₀ = c₀/(4C)` is increasing in `c₀`;
`sstarLowerBoundConst` is antitone in its last argument and increasing in `c₁`,
which sits in its numerator).  The fourth, antitonicity in `CB`, is
`sstarLowerBoundConst_antitone_CB` of `Terms/SstarLowerBoundWorkB.lean`. -/

/-- `sstarWorkC0` is antitone in `CM` on the positives. -/
theorem sstarWorkC0_antitone {CM cmMax : ℝ} (hCM : 0 < CM) (hle : CM ≤ cmMax) :
    sstarWorkC0 cmMax ≤ sstarWorkC0 CM := by
  have h8CM : (0 : ℝ) < 8 * CM := by linarith only [hCM]
  have h8 : 8 * CM ≤ 8 * cmMax := by linarith only [hle]
  have hb : (0 : ℝ) ≤ 1 / (8 * CM) := (one_div_pos.mpr h8CM).le
  have ha : (0 : ℝ) ≤ 1 / (8 * cmMax) :=
    (one_div_pos.mpr (lt_of_lt_of_le h8CM h8)).le
  have h1 : 1 / (8 * cmMax) ≤ 1 / (8 * CM) := one_div_le_one_div_of_le h8CM h8
  have hsq : (1 / (8 * cmMax)) ^ (2 : ℕ) ≤ (1 / (8 * CM)) ^ (2 : ℕ) :=
    sq_le_sq.mpr (by rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact h1)
  rw [sstarWorkC0, sstarWorkC0]
  exact min_le_min le_rfl hsq

/-- `optimalWindowConst C c₀ = c₀/(4C)` is increasing in `c₀`. -/
theorem optimalWindowConst_mono {C c₁ c₂ : ℝ} (hC : 0 < C) (hle : c₁ ≤ c₂) :
    optimalWindowConst C c₁ ≤ optimalWindowConst C c₂ := by
  rw [optimalWindowConst, optimalWindowConst]
  exact div_le_div_of_nonneg_right hle (by linarith only [hC])

/-- `sstarLowerBoundConst` is antitone in its last argument. -/
theorem sstarLowerBoundConst_antitone_CDE {CB Cq Clog c₁ CDE₁ CDE₂ : ℝ}
    (hCB : 0 < CB) (hCq : 0 < Cq) (hClog : 0 < Clog) (hc₁ : 0 < c₁)
    (hCDE₁ : 0 < CDE₁) (hle : CDE₁ ≤ CDE₂) :
    sstarLowerBoundConst CB Cq Clog c₁ CDE₂ ≤ sstarLowerBoundConst CB Cq Clog c₁ CDE₁ := by
  have hd₁ : (0 : ℝ) < 64 * CB * Cq * Clog ^ (9 : ℕ) * CDE₁ := by positivity
  have hdle : 64 * CB * Cq * Clog ^ (9 : ℕ) * CDE₁ ≤ 64 * CB * Cq * Clog ^ (9 : ℕ) * CDE₂ :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  rw [sstarLowerBoundConst, sstarLowerBoundConst]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hc₁.le hd₁ hdle)

/-- `sstarLowerBoundConst` is increasing in its fourth argument `c₁`, which sits
in its numerator. -/
theorem sstarLowerBoundConst_mono_c₁ {CB Cq Clog c₁ c₂ CDE : ℝ}
    (hCB : 0 < CB) (hCq : 0 < Cq) (hClog : 0 < Clog) (hCDE : 0 < CDE)
    (hle : c₁ ≤ c₂) :
    sstarLowerBoundConst CB Cq Clog c₁ CDE ≤ sstarLowerBoundConst CB Cq Clog c₂ CDE := by
  rw [sstarLowerBoundConst, sstarLowerBoundConst]
  exact Real.sqrt_le_sqrt
    (div_le_div_of_nonneg_right hle (by positivity))

/-- **Comparison of the named constant with the assembly's constant.**  If the two
anchor constants are bounded by `cbMax` and `cmMax`, the named constant
`sstarCloseConst d cbMax cmMax` is below the assembly's own constant
`sstarPackConst d CM CB`.  Since the latter is the constant at which the
assembly produces its bracket, this
lemma is precisely what turns "the anchors exist" into "this `d`-only constant
works".

The four arguments are used in the order the assembly uses them: `CB` enters
`sstarLowerBoundConst`'s first slot, `CM` its last and `c₀`'s definition, and
`c₀ = sstarWorkC0 CM` is *antitone* in `CM`, so the bound `CM ≤ cmMax` pushes
`sstarLowerBoundConst` in the small direction at both places. -/
theorem sstarCloseConst_le_packConst {d : ℕ} {CM CB cbMax cmMax : ℝ}
    (hCM : 0 < CM) (hCB : 0 < CB) (hcm : 0 < cmMax)
    (hleCB : CB ≤ cbMax) (hleCM : CM ≤ cmMax) :
    sstarCloseConst d cbMax cmMax ≤ sstarPackConst d CM CB := by
  have hc₀ : sstarWorkC0 cmMax ≤ sstarWorkC0 CM := sstarWorkC0_antitone hCM hleCM
  have hc₁ : optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax) ≤
      optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 CM) :=
    optimalWindowConst_mono (sstarWorkEnvelopeConst_pos d) hc₀
  have hA₁ : sstarLowerBoundConst cbMax (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax)) (2 * cmMax + 1) ≤
      sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax)) (2 * cmMax + 1) :=
    sstarLowerBoundConst_antitone_CB hCB
      (lt_of_lt_of_le hCB hleCB) hleCB logEnvelopeConst_sstarWorkScaleConst_pos
      (by norm_num)
      (optimalWindowConst_pos (sstarWorkEnvelopeConst_pos d) (sstarWorkC0_pos hcm))
      (by linarith only [hcm])
  have hA₂ : sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax)) (2 * cmMax + 1) ≤
      sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax)) (2 * CM + 1) :=
    sstarLowerBoundConst_antitone_CDE hCB logEnvelopeConst_sstarWorkScaleConst_pos
      (by norm_num)
      (optimalWindowConst_pos (sstarWorkEnvelopeConst_pos d) (sstarWorkC0_pos hcm))
      (by linarith only [hCM]) (by linarith only [hleCM])
  have hA₃ : sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax)) (2 * CM + 1) ≤
      sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 CM)) (2 * CM + 1) :=
    sstarLowerBoundConst_mono_c₁ hCB logEnvelopeConst_sstarWorkScaleConst_pos
      (by norm_num) (by linarith only [hCM]) hc₁
  have hA : sstarLowerBoundConst cbMax (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 cmMax)) (2 * cmMax + 1) ≤
      sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
        (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 CM)) (2 * CM + 1) :=
    le_trans (le_trans hA₁ hA₂) hA₃
  rw [sstarCloseConst, sstarPackConst, sstarWorkAssembledConst]
  exact min_le_min (div_le_div_of_nonneg_right hA (by norm_num)) le_rfl

/-! ## The two lemmas that make an anchor bound usable

With `sstarCloseConst_le_packConst` the packaged constant is available, but the
assembly's bracket is stated at `sstarPackConst d CM CB`; the multiplier
`cStar^{3/2} ν² m^{1/2} log^{-9/2}(ν⁻¹m)` is nonnegative in Lean's `rpow`
convention, so the transfer is a multiplication by a nonnegative factor. -/

/-- **The transfer of the assembled bracket to the named constant.**  A bracket
at the assembly's constant `sstarPackConst d CM CB` gives the same bracket at
`sstarCloseConst d cbMax cmMax` as soon as the two anchor bounds hold. -/
theorem sstarCloseConst_mul_le_of_packConst_mul_le {d : ℕ} {CM CB cbMax cmMax : ℝ}
    {nu cStar A : ℝ} {m : ℕ}
    (hCM : 0 < CM) (hCB : 0 < CB) (hcm : 0 < cmMax)
    (hleCB : CB ≤ cbMax) (hleCM : CM ≤ cmMax)
    (hcStar : 0 < cStar) (hnu : 0 < nu) (hm : 0 ≤ (m : ℝ))
    (hlog : 0 ≤ Real.log (nu⁻¹ * (m : ℝ)))
    (h : sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
        (m : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤ A) :
    sstarCloseConst d cbMax cmMax * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
        (m : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤ A := by
  have hY₁ : (0 : ℝ) ≤ cStar ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hcStar.le _
  have hY₂ : (0 : ℝ) ≤ nu ^ (2 : ℝ) := Real.rpow_nonneg hnu.le _
  have hY₃ : (0 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hm _
  have hY₄ : (0 : ℝ) ≤ Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) :=
    Real.rpow_nonneg hlog _
  have h₁ : sstarCloseConst d cbMax cmMax * cStar ^ ((3 : ℝ) / 2) ≤
      sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right
      (sstarCloseConst_le_packConst hCM hCB hcm hleCB hleCM) hY₁
  have h₂ : sstarCloseConst d cbMax cmMax * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) ≤
      sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) :=
    mul_le_mul_of_nonneg_right h₁ hY₂
  have h₃ : sstarCloseConst d cbMax cmMax * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
        (m : ℝ) ^ ((1 : ℝ) / 2) ≤
      sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
        (m : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right h₂ hY₃
  exact le_trans (mul_le_mul_of_nonneg_right h₃ hY₄) h

/-! ## The named threshold constant

The threshold `e.L.vs.nu` and the conclusion's quenched estimate
carry the *same* constant `C` (the paper increases the constant in `e.L.vs.nu` if
necessary).  With `sstarWorkThrConst d = max 10⁶ (2 Env(d) + 1)` the
assembly's envelope conditions `cutoffEnvelopeConst d ≤ C`, `64 ≤ C` and
`1 ≤ C` all hold, so the same named constant serves both roles. -/

/-- **The named threshold constant of the statement**: the work threshold
constant `sstarWorkThrConst d`, read here in its role as the `C` of
`e.L.vs.nu` and of `e.sstar.lower.bound.quenched`. -/
def sstarCloseThrConst (d : ℕ) : ℝ := sstarWorkThrConst d

theorem one_le_sstarCloseThrConst (d : ℕ) : (1 : ℝ) ≤ sstarCloseThrConst d :=
  one_le_sstarWorkThrConst d

/-! ## Where the anchor constants are `d`-only

What a constant-first `∃ C c` needs is a `d`-only *value* for each anchor constant (a bound would
do, but a value suffices).  Since the anchors are stated `∃ C, 0 < C ∧ ∀ data, …` at fixed `d`,
their constants can be named by `Classical.choose` whenever the existential is the outermost
binder.

* `CL` — the localization anchor, whose `∃ CL` is outermost, so `sstarCloseCL d hd` below is
  `d`-only;
* `CM` and `CT` — produced only as `∃ CB CM CT : ℝ, …` inside
  `Setup.sstar_lower_bound_of_section3_final (d) [NeZero d] (hd) (Cl4 … Cw) (hCl4 … hCw)`, i.e.
  after fifteen data-dependent constants and their hypotheses.  No `Classical.choose` at `d`
  alone reaches them: the issue is the *placement* of the existential, not the size of the
  anchors. -/

/-- **The localization anchor's constant `CL`, named as a `d`-only value.**
`Classical.choose` of the localization anchor, whose `∃ CL` is outermost. -/
noncomputable def sstarCloseCL (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  Classical.choose (sstarClose_locAnchor_unconditional d hd)

theorem sstarCloseCL_pos (d : ℕ) [NeZero d] (hd : 2 ≤ d) : 0 < sstarCloseCL d hd :=
  (Classical.choose_spec (sstarClose_locAnchor_unconditional d hd)).1

end

end SuperdiffusionCLT.Section3.Terms
