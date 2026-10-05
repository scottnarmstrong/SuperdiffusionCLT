/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridgesB
public import SuperdiffusionCLT.Section3.Setup.ThresholdTranslation
public import SuperdiffusionCLT.Section3.Terms.MasterInequality

/-!
# The `K`-uniform constant of `p.sstar.lower.bound` and the threshold discharges

The statement `Frozen.Section3.sigmaBarStar_lower_bound` of the paper's `p.sstar.lower.bound`
concludes `∃ C c` and then quantifies the J5 non-degeneracy constants `cStar, K` universally
*before* the data.  The assembled brackets of `Section3/Setup/ScaleAssemblyB.lean` and
`Section3/Setup/QuenchedLowerBoundB.lean` produce a constant

`logEnvelopeConst (Kfree) = (Kfree + 2)^4` from `sstarLowerBoundConst`,

where `Kfree` is the **free scale-separation constant** of the proof; a `K`-uniform conclusion
therefore requires that `Kfree` be fixed once and for all at a `d`-only value.  This file does that
(`sstarWorkScaleConst`) and names the resulting packaged constant (`sstarPackConst`).

## Main results

* the three `d`-only constants `sstarWorkScaleConst`, `sstarWorkEnvelopeConst`,
  `sstarWorkThrConst` and the `CM`-only smallness constant `sstarWorkC0`,
  together with the largeness conditions they satisfy (`1 ≤ K`, `8056 ≤ K log 3`,
  `cutoffEnvelopeConst d ≤ C`, `64 ≤ C`, `CM √c₀ ≤ 1/8`);
* the **named packaged constant** `sstarPackConst d CM CB`, its bound by `1/2`, and its bound by
  the assembly's own constant
  `sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
  (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 CM)) (2 * CM + 1) / 2`;
* the nonnegativity `log(ν⁻¹L) ≥ 0` for `ν ≤ 1` (`log_nonneg_inv_mul_nat`);
* the monotonicity of `sstarLowerBoundConst` in `CB`
  (`sstarLowerBoundConst_antitone_CB`): the packaged constant is antitone in `CB`, so an upper
  bound on `CB` depending on `d` alone converts the existential `∃ CB` of
  the assembly into a lower bound for the constant;
* the packaged bracket `sstarPackConst_bracket_of_assembled`.

## The constants of the anchors

`sstar_lower_bound_assembled_of_anchors d` produces its constant only as `∃ CB, 0 < CB ∧ …`
(from the homogenization anchor `Setup.ScaleAssemblyB.exists_bell_bound d`, which exposes no upper
bound), and the master inequality produces `CM` in the same way.  Since the packaged constant is
`2^{-1} √(c₁ / (64 · CB · logEnvelopeConst sstarWorkScaleConst · 2⁹ · (2 CM + 1)))`, a
constant-first `∃ c` requires an *elementary* (`d`-only) upper bound for `CB` and `CM`; this is
a question about the anchor constants, not about `K`-uniformity (`K` is fixed here at
`sstarWorkScaleConst`) and not about the threshold.

## The threshold

The threshold `e.L.vs.nu` is the standing largeness hypothesis of this very proposition
(`Section3/Setup/ThresholdTranslation.lean`), so carrying it is faithful; it is read with the
correction of the printed text (see `ERRATA.md`).  The printed statement is
"*There exist `C(d) ∈ [1,∞)` and `c(d) ∈ (0,½]` such that, for every `L, m ∈ ℕ`
satisfying `L ≥ m ≥ ½L` and `m ≥ C cStar^{-3}(log³(3+ν^{-1}) loglog(3+ν^{-1}) +
(1+nondegconst) log(3+ν^{-1}+nondegconst))` …*", with `C` of the threshold the
same `d`-only constant as the `C` of the conclusion — which is why the two
constants introduced here (`sstarWorkThrConst`, `sstarWorkEnvelopeConst`) are
`d`-only and why `sstarWorkScaleConst`, which replaces the proof's free scale
constant `K`, is taken `d`-free.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The two arithmetic facts about `log 3` -/

/-- `8056 / 10000 < log 3`, the quantitative form of the largeness
`8056 ≤ K log 3` of the composition at the fixed constant `K = 10000`. -/
theorem log_three_gt_d8056 : (0.8056 : ℝ) < Real.log 3 := by
  have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2 : ℝ) := by
    have hm := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
      (show (3 / 2 : ℝ) ≠ 0 by norm_num)
    rw [show (2 : ℝ) * (3 / 2) = 3 by norm_num] at hm
    exact hm
  have hinv : (3 / 2 : ℝ)⁻¹ = 2 / 3 := by norm_num
  have h32 : (1 : ℝ) - (3 / 2 : ℝ)⁻¹ ≤ Real.log (3 / 2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  linarith only [h3, hinv, h32, Real.log_two_gt_d9]

/-! ## The `d`-only constants -/

/-- **The free scale-separation constant `K` of the proof, fixed at a
value that depends on no datum at all.**  The paper says "*Choose the parameter
`K` sufficiently large, depending only on `d`, for the scale-separation
estimates below*", so a `K`-uniform conclusion may fix `K` once and
for all.  The composition — the assembly's own numeric hypotheses and the
`ThresholdTranslation` lemmas — asks only `1 ≤ K` and `8056 ≤ K log 3`, which
`10000` satisfies; `K`'s remaining use is *inside* the two anchor blocks
(`hLocAnchor`, `hMaster`), and the statement's own `K` (the J5 constant) is a
*different* binder that does not enter the constant at all. -/
def sstarWorkScaleConst : ℝ := 10000

theorem one_le_sstarWorkScaleConst : (1 : ℝ) ≤ sstarWorkScaleConst := by
  norm_num [sstarWorkScaleConst]

theorem sstarWorkScaleConst_klog3 : (8056 : ℝ) ≤ sstarWorkScaleConst * Real.log 3 := by
  have h : (8056 : ℝ) = 10000 * 0.8056 := by norm_num
  rw [h, sstarWorkScaleConst]
  exact mul_le_mul_of_nonneg_left log_three_gt_d8056.le (by norm_num)

/-- **The cutoff-envelope constant `C` of the composition, at a `d`-only
value**: `cutoffEnvelopeConst d` raised to the printed lower bound
`64`. -/
def sstarWorkEnvelopeConst (d : ℕ) : ℝ := max (cutoffEnvelopeConst d) 64

theorem le_sstarWorkEnvelopeConst (d : ℕ) :
    cutoffEnvelopeConst d ≤ sstarWorkEnvelopeConst d :=
  le_max_left _ _

theorem sstarWorkEnvelopeConst_large (d : ℕ) : (64 : ℝ) ≤ sstarWorkEnvelopeConst d :=
  le_max_right _ _

theorem sstarWorkEnvelopeConst_pos (d : ℕ) : (0 : ℝ) < sstarWorkEnvelopeConst d :=
  lt_of_lt_of_le (by norm_num) (sstarWorkEnvelopeConst_large d)

/-- **The threshold constant, at a `d`-only value** large enough for every
constant-choice condition the composition imposes: `10⁶ ≤ C` (the correction of the printed text
in the threshold translation) and
`2 · sstarWorkEnvelopeConst d ≤ C`. -/
def sstarWorkThrConst (d : ℕ) : ℝ := max 1000000 (2 * sstarWorkEnvelopeConst d + 1)

theorem one_le_sstarWorkThrConst (d : ℕ) : (1 : ℝ) ≤ sstarWorkThrConst d :=
  le_trans (by norm_num) (le_max_left _ _)

/-- **The smallness constant `c₀` as a function of the master-inequality
constant `CM` alone**: `min (1/2) (1/(8CM))²`.  It is the witness of
the smallness lemma of the threshold translation with the free choice made
explicit.  It depends on `CM`, which is a `d`-only constant of the
master inequality, and on nothing else. -/
def sstarWorkC0 (CM : ℝ) : ℝ := min (1 / 2) ((1 / (8 * CM)) ^ (2 : ℕ))

theorem sstarWorkC0_nonneg (CM : ℝ) : (0 : ℝ) ≤ sstarWorkC0 CM :=
  le_min (by norm_num) (sq_nonneg _)

theorem sstarWorkC0_pos {CM : ℝ} (hCM : (0 : ℝ) < CM) : (0 : ℝ) < sstarWorkC0 CM :=
  lt_min (by norm_num)
    (pow_pos (div_pos one_pos (mul_pos (by norm_num) hCM)) (2 : ℕ))

/-- the relative smallness `CM √c₀ ≤ 1/8` at the fixed `c₀`. -/
theorem sstarWorkC0_sqrt_le {CM : ℝ} (hCM : (0 : ℝ) < CM) :
    CM * Real.sqrt (sstarWorkC0 CM) ≤ 1 / 8 := by
  have hle : sstarWorkC0 CM ≤ (1 / (8 * CM)) ^ (2 : ℕ) := min_le_right _ _
  have h8 : (0 : ℝ) < 1 / (8 * CM) := div_pos one_pos (mul_pos (by norm_num) hCM)
  have hs : Real.sqrt (sstarWorkC0 CM) ≤ Real.sqrt ((1 / (8 * CM)) ^ (2 : ℕ)) :=
    Real.sqrt_le_sqrt hle
  have hsqrt : Real.sqrt ((1 / (8 * CM)) ^ (2 : ℕ)) = 1 / (8 * CM) :=
    Real.sqrt_sq h8.le
  calc CM * Real.sqrt (sstarWorkC0 CM) ≤ CM * (1 / (8 * CM)) :=
        mul_le_mul_of_nonneg_left (hs.trans_eq hsqrt) hCM.le
    _ = 1 / 8 := by field_simp [hCM.ne']

/-! ## Threshold discharges

A consequence of the threshold `e.L.vs.nu` used by the composition: the logarithm
`log(ν⁻¹L)` is nonnegative. -/

/-- `log(ν⁻¹L) ≥ 0` for `ν ≤ 1` (the case `L = 0` is `log 0 = 0`). -/
theorem log_nonneg_inv_mul_nat {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (L : ℕ) :
    (0 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · rw [hL, Nat.cast_zero, mul_zero, Real.log_zero]
  · have h1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    refine Real.log_nonneg ?_
    have h := mul_le_mul h1 hL1 (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [h1] : (0 : ℝ) ≤ nu⁻¹)
    simpa using h

/-! ## The packaged constant -/

/-- **The packaged lower-bound constant**, named explicitly.  It is the
assembly's constant `sstarLowerBoundConst CB (logEnvelopeConst K) 2
(optimalWindowConst C c₀) (2 CM + 1) / 2` with the free scale constant `K`
fixed to `sstarWorkScaleConst`, the envelope constant `C` to
`sstarWorkEnvelopeConst d`, and `c₀` to `sstarWorkC0 CM`, truncated at `1/2`
so that it can play the role of the proposition's `c ∈ (0,1/2]`.

By inspection its only free arguments are `d`, `CM` (the master-inequality
constant) and `CB` (the pigeonhole/envelope constant); neither the J5
binder `K`, nor the scales `L, m`, nor `ν`, nor `cStar` occurs.  The three
constants `logEnvelopeConst sstarWorkScaleConst`,
`sstarWorkEnvelopeConst d`, `sstarWorkC0 CM` are the `K`-uniform
replacements, and `min · (1/2)` is the passage from an arbitrary positive
constant to the proposition's range `(0, 1/2]`. -/
def sstarWorkAssembledConst (d : ℕ) (CM CB : ℝ) : ℝ :=
  sstarLowerBoundConst CB (logEnvelopeConst sstarWorkScaleConst) 2
    (optimalWindowConst (sstarWorkEnvelopeConst d) (sstarWorkC0 CM))
    (2 * CM + 1) / 2

/-- The packaged constant: the assembly's constant, truncated at `1/2`. -/
def sstarPackConst (d : ℕ) (CM CB : ℝ) : ℝ :=
  min (sstarWorkAssembledConst d CM CB) (1 / 2)

theorem logEnvelopeConst_sstarWorkScaleConst_pos :
    (0 : ℝ) < logEnvelopeConst sstarWorkScaleConst :=
  logEnvelopeConst_pos (le_of_lt (lt_of_lt_of_le zero_lt_one one_le_sstarWorkScaleConst))

/-- `sstarPackConst` never exceeds the assembly's own constant: this is the
inequality that transfers the assembled bound to the packaged one. -/
theorem sstarPackConst_le_assembled (CM CB : ℝ) :
    sstarPackConst d CM CB ≤ sstarWorkAssembledConst d CM CB :=
  min_le_left _ _

/-! ## Constant-first packaging from free anchors

The assembly exposes its two constants only existentially
(`sstar_lower_bound_assembled_of_anchors d` gives `∃ CB, 0 < CB ∧ …`, and the
master inequality gives `∃ CM, 1 ≤ CM ∧ …`).  The proposition's `c`, however,
is quantified *before* every datum, so a constant-first packaging must bound
the assembly constant from below by a value depending on `d` alone.  The
constant decays like the inverse square root of the product `CB · (2 CM + 1)`,
so such a bound needs upper bounds for the anchor constants. -/

/-! ## An upper bound on the anchor constants suffices

The packaged constant is antitone in `CB`, so a *data-independent upper bound*
`CB ≤ CBmax` (with `CBmax` a `d`-only quantity) is exactly what a constant-first
packaging needs: it converts the existential `∃ CB` of
the assembly into the lower bound
`sstarPackConst d CM CBmax ≤ sstarPackConst d CM CB`. -/

/-- **`sstarLowerBoundConst` is antitone in `CB`.** -/
theorem sstarLowerBoundConst_antitone_CB {CB₁ CB₂ Cq Clog c1 CDE : ℝ}
    (hCB₁ : (0 : ℝ) < CB₁) (hCB₂ : (0 : ℝ) < CB₂) (hle : CB₁ ≤ CB₂)
    (hCq : (0 : ℝ) < Cq) (hClog : (0 : ℝ) < Clog) (hc1 : (0 : ℝ) < c1)
    (hCDE : (0 : ℝ) < CDE) :
    sstarLowerBoundConst CB₂ Cq Clog c1 CDE ≤ sstarLowerBoundConst CB₁ Cq Clog c1 CDE := by
  have hd₁ : (0 : ℝ) < 64 * CB₁ * Cq * Clog ^ (9 : ℕ) * CDE := by positivity
  have hd₂ : (0 : ℝ) < 64 * CB₂ * Cq * Clog ^ (9 : ℕ) * CDE := by positivity
  have hdle : 64 * CB₁ * Cq * Clog ^ (9 : ℕ) * CDE ≤
      64 * CB₂ * Cq * Clog ^ (9 : ℕ) * CDE := by
    have h := mul_le_mul_of_nonneg_right hle
      (by positivity : (0 : ℝ) ≤ 64 * Cq * Clog ^ (9 : ℕ) * CDE)
    linarith only [h]
  rw [sstarLowerBoundConst, sstarLowerBoundConst]
  refine Real.sqrt_le_sqrt ?_
  exact div_le_div_of_nonneg_left hc1.le hd₁ hdle

/-! ## The packaged form of the assembled bracket

The lemma below relates the named constant `sstarPackConst`
to the *shape* of the proposition's conclusion: the assembly's own bracket at
`(CB, CM)` and the work constants (whose constant is `sstarWorkAssembledConst d
CM CB`) transfers verbatim to `sstarPackConst d CM CB`, together with the first
conjunct `σ̄_L ≥ σ̄_{L,*}`. -/

/-- **The packaged bracket.**  The assembly's conclusion at the work constants,
with `sstarPackConst d CM CB` in place of the assembly's own constant, and with
the first conjunct `σ̄_L ≥ σ̄_{L,*}(cu_m)` carried along. -/
theorem sstarPackConst_bracket_of_assembled [NeZero d] {CB CM nu cStar : ℝ} {L : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)} {mbar : ℕ}
    (hnu : (0 : ℝ) < nu) (hcStar : (0 : ℝ) < cStar) (hmbar : (0 : ℝ) < (mbar : ℝ))
    (hlog : (1 : ℝ) ≤ Real.log (nu⁻¹ * (mbar : ℝ)))
    (hann : sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) ≤
      sigmaBarInfinite nu L P)
    (hqu : sstarWorkAssembledConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
        (mbar : ℝ) ^ ((1 : ℝ) / 2) * Real.log (nu⁻¹ * (mbar : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
      sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ)))) :
    sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) ≤ sigmaBarInfinite nu L P ∧
      sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
          (mbar : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (nu⁻¹ * (mbar : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
        sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) := by
  refine ⟨hann, ?_⟩
  have hF1 : (0 : ℝ) < cStar ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hcStar _
  have hF2 : (0 : ℝ) < nu ^ (2 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hF3 : (0 : ℝ) < (mbar : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hmbar _
  have hF4 : (0 : ℝ) < Real.log (nu⁻¹ * (mbar : ℝ)) ^ (-((9 : ℝ) / 2)) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog) _
  have h1 : sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) ≤
      sstarWorkAssembledConst d CM CB * cStar ^ ((3 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (sstarPackConst_le_assembled CM CB) hF1.le
  have h2 := mul_le_mul_of_nonneg_right h1 hF2.le
  have h3 := mul_le_mul_of_nonneg_right h2 hF3.le
  have h4 := mul_le_mul_of_nonneg_right h3 hF4.le
  exact le_trans h4 hqu

end

end SuperdiffusionCLT.Section3.Terms
