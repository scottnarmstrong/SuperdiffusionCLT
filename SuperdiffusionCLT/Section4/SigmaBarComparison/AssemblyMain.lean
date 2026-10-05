/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.GrowthUpper
public import SuperdiffusionCLT.Section4.LNaught.Monotone
public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section4.LNaught.LogCompare
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import SuperdiffusionCLT.Section4.SigmaBarComparison.ComparisonBound

/-!
# Assembling `sbAsm_main`

Elementary numeric helper lemmas used to thread the shared witness `n` of
`#homog-below-bound`/`#independence-and-ratio` through `hHomog`, and to reach
the `≤ 1/8` refinement via the `M`-inflation mechanism
(`lNaught_mul_M_le`, from `Section4/LNaught/LogCompare.lean`).
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open SuperdiffusionCLT.Section4.LNaught (lNaught_mono_const lNaught_mono_M)

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-! ## Elementary numeric lemmas -/

/-- `200 log L + 1 ≤ 201 L^α log³L` for `L ≥ 3`, `α ≥ 0`. -/
theorem sbAsm_tail_le {L : ℕ} (hL : 3 ≤ L) {alpha : ℝ} (halpha : 0 ≤ alpha) :
    200 * Real.log (L : ℝ) + 1 ≤ 201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    linarith only [Real.exp_one_lt_d9]
  have hlogL : (1 : ℝ) < Real.log (L : ℝ) := lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hL3)
  have hLalpha : (1 : ℝ) ≤ (L : ℝ) ^ alpha :=
    Real.one_le_rpow (by linarith only [hL3]) halpha
  have hlogsq : (1 : ℝ) < Real.log (L : ℝ) ^ (2 : ℝ) := by
    have h1 : (1 : ℝ) ^ (2 : ℝ) < Real.log (L : ℝ) ^ (2 : ℝ) :=
      Real.rpow_lt_rpow (by norm_num) hlogL (by norm_num)
    simpa using h1
  have hlogpos : (0 : ℝ) < Real.log (L : ℝ) := by linarith only [hlogL]
  have hlogcube_eq : Real.log (L : ℝ) ^ (3 : ℝ) =
      Real.log (L : ℝ) ^ (2 : ℝ) * Real.log (L : ℝ) := by
    have h : Real.log (L : ℝ) ^ ((2 : ℝ) + (1 : ℝ)) =
        Real.log (L : ℝ) ^ (2 : ℝ) * Real.log (L : ℝ) ^ (1 : ℝ) := Real.rpow_add hlogpos 2 1
    rw [Real.rpow_one] at h
    rwa [show (2 : ℝ) + (1 : ℝ) = (3 : ℝ) by norm_num] at h
  have hlogcube_gt : Real.log (L : ℝ) < Real.log (L : ℝ) ^ (3 : ℝ) := by
    rw [hlogcube_eq]
    have hh := mul_lt_mul_of_pos_right hlogsq hlogpos
    rwa [one_mul] at hh
  have hlogcube_gt1 : (1 : ℝ) < Real.log (L : ℝ) ^ (3 : ℝ) := lt_trans hlogL hlogcube_gt
  have hstep : 200 * Real.log (L : ℝ) + 1 ≤ 201 * Real.log (L : ℝ) ^ (3 : ℝ) := by
    nlinarith only [hlogcube_gt, hlogcube_gt1]
  have hLalpha_nonneg : (0 : ℝ) ≤ (L : ℝ) ^ alpha := le_trans zero_le_one hLalpha
  have hlogcube_nonneg : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := le_trans zero_le_one hlogcube_gt1.le
  have hfinal : 201 * Real.log (L : ℝ) ^ (3 : ℝ) ≤ 201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 : (1 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_right hLalpha hlogcube_nonneg
    nlinarith only [h1]
  linarith only [hstep, hfinal]

/-- `L^α ≤ 2 ell^α` when `ell ≤ L ≤ 2 ell` (as naturals cast to `ℝ`), `0 ≤ α < 1`,
`1 ≤ ell`. -/
theorem sbAsm_ratio_alpha_le {L ell : ℕ} (hellpos : 1 ≤ ell) (hle : ell ≤ L)
    (hge : (L : ℝ) ≤ 2 * (ell : ℝ)) {alpha : ℝ} (_halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    (L : ℝ) ^ alpha ≤ 2 * (ell : ℝ) ^ alpha := by
  have hellR : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hellpos
  have hellpos' : (0 : ℝ) < (ell : ℝ) := lt_of_lt_of_le one_pos hellR
  have hleR : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hle
  have hge1 : (1 : ℝ) ≤ (L : ℝ) / (ell : ℝ) := by
    rw [le_div_iff₀ hellpos']; linarith only [hleR]
  have hratio_le2 : (L : ℝ) / (ell : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hellpos']; linarith only [hge]
  have hpow_le : ((L : ℝ) / (ell : ℝ)) ^ alpha ≤ (L : ℝ) / (ell : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hge1 halpha1.le |>.trans_eq (Real.rpow_one _)
  have heq2 : (L : ℝ) ^ alpha = (ell : ℝ) ^ alpha * ((L : ℝ) / (ell : ℝ)) ^ alpha := by
    rw [← Real.mul_rpow hellpos'.le (div_nonneg (Nat.cast_nonneg L) hellpos'.le)]
    congr 1
    field_simp
  rw [heq2]
  have hellalpha_nonneg : (0 : ℝ) ≤ (ell : ℝ) ^ alpha := Real.rpow_nonneg hellpos'.le _
  calc (ell : ℝ) ^ alpha * ((L : ℝ) / (ell : ℝ)) ^ alpha ≤
        (ell : ℝ) ^ alpha * ((L : ℝ) / (ell : ℝ)) := mul_le_mul_of_nonneg_left hpow_le hellalpha_nonneg
    _ ≤ (ell : ℝ) ^ alpha * 2 := mul_le_mul_of_nonneg_left hratio_le2 hellalpha_nonneg
    _ = 2 * (ell : ℝ) ^ alpha := by ring

/-- `log³L ≤ 8 log³(ell)` when `ell ≥ L/2` (as naturals cast to `ℝ`) and
`4 ≤ L`. -/
theorem sbAsm_ratio_log_le {L ell : ℕ} (hL4 : 4 ≤ L)
    (hge : (L : ℝ) ≤ 2 * (ell : ℝ)) :
    Real.log (L : ℝ) ^ (3 : ℝ) ≤ 8 * Real.log (ell : ℝ) ^ (3 : ℝ) := by
  have hL4R : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
  have hellR2 : (2 : ℝ) ≤ (ell : ℝ) := by linarith only [hge, hL4R]
  have hellpos : (0 : ℝ) < (ell : ℝ) := by linarith only [hellR2]
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL4R]
  have hlogell2 : Real.log 2 ≤ Real.log (ell : ℝ) := Real.log_le_log (by norm_num) hellR2
  have hlog2ell : Real.log (L : ℝ) ≤ Real.log (2 * (ell : ℝ)) := Real.log_le_log hLpos hge
  have hlogmul : Real.log (2 * (ell : ℝ)) = Real.log 2 + Real.log (ell : ℝ) :=
    Real.log_mul (by norm_num) hellpos.ne'
  have hlogL_le : Real.log (L : ℝ) ≤ 2 * Real.log (ell : ℝ) := by
    rw [hlogmul] at hlog2ell; linarith only [hlog2ell, hlogell2]
  have hlogL_nonneg : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg (by linarith only [hL4R])
  have hcube_le : Real.log (L : ℝ) ^ (3 : ℝ) ≤ (2 * Real.log (ell : ℝ)) ^ (3 : ℝ) :=
    Real.rpow_le_rpow hlogL_nonneg hlogL_le (by norm_num)
  have hlogell_nonneg : (0 : ℝ) ≤ Real.log (ell : ℝ) := le_trans (Real.log_nonneg (by norm_num)) hlogell2
  have heq3 : (2 * Real.log (ell : ℝ)) ^ (3 : ℝ) = 8 * Real.log (ell : ℝ) ^ (3 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hlogell_nonneg]
    congr 1
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rwa [heq3] at hcube_le

/-! ## The `M`-inflation mechanism (via `lNaught_mul_M_le`) -/

/-- Pattern A (used for `hLvsLnaught`, at both `h := L` and `L' := ell`):
from `lNaught_mul_M_le` (`Section4/LNaught/LogCompare.lean`) and
`lNaught_mono_const`, the *given* threshold `lNaught C (C·M) α cStar ν K ≤
ell` dominates `lNaught C₀ (K'·(C·M)) α cStar ν K` once `C ≥
C₀·K'·(1+\log K'/\log 2)^{12}`. -/
theorem sbAsm_inflate_A
    {C0 K' C M alpha cStar nu K : ℝ}
    (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hC : 0 ≤ C) (halpha : alpha < 1) (hcStar : 0 < cStar)
    (hnu : 0 < nu) (hK : 0 ≤ K) (hK' : 1 ≤ K')
    (hCbig : C0 * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) ≤ C) :
    lNaught C0 (K' * (C * M)) alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K := by
  have h1 := SuperdiffusionCLT.Section4.LNaught.lNaught_mul_M_le
    C0 (C * M) alpha cStar nu K K' hC0 (mul_nonneg hC hM) halpha hcStar hnu hK hK'
  have hCmid : (0 : ℝ) ≤ C0 * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) := by
    have h1le : (1:ℝ) ≤ 1 + Real.log K' / Real.log 2 := by
      have hK'pos : (0:ℝ) < K' := lt_of_lt_of_le one_pos hK'
      rcases eq_or_lt_of_le hK' with heq | hlt
      · rw [← heq]; norm_num
      · have hlogpos : (0:ℝ) < Real.log K' := Real.log_pos hlt
        have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have : (0:ℝ) ≤ Real.log K' / Real.log 2 := div_nonneg hlogpos.le hlog2pos.le
        linarith only [this]
    have hpow_nonneg : (0:ℝ) ≤ (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) :=
      Real.rpow_nonneg (by linarith only [h1le]) _
    have : (0:ℝ) ≤ C0 * K' := mul_nonneg hC0 (le_trans zero_le_one hK')
    exact mul_nonneg this hpow_nonneg
  exact h1.trans (lNaught_mono_const hCmid hCbig (mul_nonneg hC hM) hK hcStar hnu halpha)

/-- Pattern B (used for `hHomog`): from `lNaught_mul_M_le`,
`lNaught_mono_const` and `lNaught_mono_M`, `lNaught C (C·M) α cStar ν K ≤ ell`
dominates `lNaught Ch (Ch·(K'·M)) α cStar ν K` once `Ch ≤ C` and
`Ch·K'·(1+\log K'/\log 2)^{12} ≤ C`. -/
theorem sbAsm_inflate_B
    {Ch K' C M alpha cStar nu K : ℝ}
    (hCh : 0 ≤ Ch) (hM : 0 ≤ M) (hC : 0 ≤ C) (halpha : alpha < 1) (hcStar : 0 < cStar)
    (hnu : 0 < nu) (hK : 0 ≤ K) (hK' : 1 ≤ K') (hChC : Ch ≤ C)
    (hCbig : Ch * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) ≤ C) :
    lNaught Ch (Ch * (K' * M)) alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K := by
  have h1 := SuperdiffusionCLT.Section4.LNaught.lNaught_mul_M_le
    Ch (Ch * M) alpha cStar nu K K' hCh (mul_nonneg hCh hM) halpha hcStar hnu hK hK'
  have harg_eq : Ch * (K' * M) = K' * (Ch * M) := by ring
  rw [harg_eq]
  have hCmid : (0 : ℝ) ≤ Ch * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) := by
    have h1le : (1:ℝ) ≤ 1 + Real.log K' / Real.log 2 := by
      have hK'pos : (0:ℝ) < K' := lt_of_lt_of_le one_pos hK'
      rcases eq_or_lt_of_le hK' with heq | hlt
      · rw [← heq]; norm_num
      · have hlogpos : (0:ℝ) < Real.log K' := Real.log_pos hlt
        have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have : (0:ℝ) ≤ Real.log K' / Real.log 2 := div_nonneg hlogpos.le hlog2pos.le
        linarith only [this]
    have hpow_nonneg : (0:ℝ) ≤ (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) :=
      Real.rpow_nonneg (by linarith only [h1le]) _
    have : (0:ℝ) ≤ Ch * K' := mul_nonneg hCh (le_trans zero_le_one hK')
    exact mul_nonneg this hpow_nonneg
  have h2 : lNaught (Ch * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ)) (Ch * M) alpha cStar nu K ≤
      lNaught C (Ch * M) alpha cStar nu K :=
    lNaught_mono_const hCmid hCbig (mul_nonneg hCh hM) hK hcStar hnu halpha
  have h3 : lNaught C (Ch * M) alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K :=
    lNaught_mono_M hC (mul_nonneg hCh hM) (mul_le_mul_of_nonneg_right hChC hM) hK hcStar hnu halpha
  exact h1.trans (h2.trans h3)

/-- The trivial case of the inflation mechanism (`K' = 1`): `lNaught Cx
(Cx·M) ≤ lNaught C (C·M)` whenever `Cx ≤ C`, via `lNaught_mono_M` then
`lNaught_mono_const`. -/
theorem sbAsm_lNaught_mono_simple {Cx C M alpha cStar nu K : ℝ}
    (hCx : 0 ≤ Cx) (hM : 0 ≤ M) (hCxC : Cx ≤ C) (hK : 0 ≤ K) (hcStar : 0 < cStar)
    (hnu : 0 < nu) (halpha : alpha < 1) :
    lNaught Cx (Cx * M) alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K := by
  have hC : (0:ℝ) ≤ C := le_trans hCx hCxC
  have h1 : lNaught Cx (Cx * M) alpha cStar nu K ≤ lNaught Cx (C * M) alpha cStar nu K :=
    lNaught_mono_M hCx (mul_nonneg hCx hM) (mul_le_mul_of_nonneg_right hCxC hM) hK hcStar hnu halpha
  have h2 : lNaught Cx (C * M) alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K :=
    lNaught_mono_const hCx hCxC (mul_nonneg hC hM) hK hcStar hnu halpha
  exact h1.trans h2

/-! ## `lNaught` grows past any multiple of its own leading constant `C`,
provided its `M`-argument is inflated by a FIXED multiple of `C` (no lower
bound like `128 ≤ C` needed, unlike the analogous fact used elsewhere for a
freely-chosen outer constant: here `C` will play the role of `hHomog`'s own
*externally supplied* constant, which cannot be assumed large). -/

/-- `2048 / (log 2)^12 + 1`: a fixed positive real with `B * (log 2)^12 ≥
2048`, used only as a scale factor below. -/
noncomputable def sbAsmGrowthB : ℝ := 2048 / (Real.log 2) ^ (12 : ℝ) + 1

/-- `64 / sbAsmGrowthB`: the fixed positive coefficient in `sbAsm_L_forced_large`
(`AssemblyLForced.lean`), `L ≥ sbAsmGrowthCoeff * C / nu^4`. -/
noncomputable def sbAsmGrowthCoeff : ℝ := 64 / sbAsmGrowthB

theorem sbAsmGrowthB_mul_log2pow :
    (2048 : ℝ) ≤ sbAsmGrowthB * (Real.log 2) ^ (12 : ℝ) := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  have heq : sbAsmGrowthB * (Real.log 2) ^ (12 : ℝ) =
      2048 + (Real.log 2) ^ (12 : ℝ) := by
    unfold sbAsmGrowthB
    field_simp
  rw [heq]
  linarith only [hpow_pos]

/-- **`lNaught` dominates `64 C` once its own `M`-argument is at least
`C * sbAsmGrowthB`.** No hypothesis on the size of `C` itself (unlike the
analogous freely-chosen-constant fact used elsewhere): the growth is driven
entirely by the `M`-argument, via the outer `rpow` exponent `1/(1-alpha) ≥
1` boosting an already-`≥1` inner quantity. -/
theorem sbAsm_lNaught_ge_C_of_M_ge {C M alpha cStar nu K : ℝ}
    (hC1 : 1 ≤ C) (hM : C * sbAsmGrowthB ≤ M)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hK : 0 ≤ K) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    (64 : ℝ) * C ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hBpos : (0 : ℝ) < sbAsmGrowthB := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
    unfold sbAsmGrowthB
    positivity
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (mul_pos hCpos hBpos) hM
  have hcStar3ge : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hcStar hcStar2 (by norm_num : (-(3 : ℝ)) ≤ 0)
    have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [h2] at h; exact h
  have hcStar3pos : (0 : ℝ) < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hMK1 : M ≤ M + 1 + K := by linarith only [hK]
  -- `inner_numer := C * (M+1+K) * cStar^{-3} ≥ C^2 * sbAsmGrowthB / 8`.
  have hNumGe : C * C * sbAsmGrowthB * (1 / 8 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have step1 : C * M * cStar ^ (-(3 : ℝ)) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMK1 hCpos.le) hcStar3pos.le
    have step2 : C * (C * sbAsmGrowthB) * (1 / 8 : ℝ) ≤ C * M * cStar ^ (-(3 : ℝ)) := by
      have h1 : C * (C * sbAsmGrowthB) * (1 / 8 : ℝ) ≤ C * M * (1 / 8 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hM hCpos.le
        nlinarith only [this]
      have h2 : C * M * (1 / 8 : ℝ) ≤ C * M * cStar ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcStar3ge (mul_pos hCpos hMpos).le
      linarith only [h1, h2]
    nlinarith only [step1, step2]
  -- `1/(denom) ≥ 1` and `log(arg) ≥ log 2`.
  have halphapos : (0 : ℝ) < 1 - alpha := by linarith only [halpha1]
  have halphale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
  have hD1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow halphapos.le halphale1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hD1pos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos halphapos _
  have hD2 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hD2pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hDpos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := mul_pos hD1pos hD2pos
  have hDle1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * 1 :=
          mul_le_mul hD1 hD2 hD2pos.le (by norm_num)
      _ = 1 := by norm_num
  have hNumNonneg : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMpos.le, hK]
    positivity
  have hFracGe : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    rw [le_div_iff₀ hDpos]
    exact mul_le_of_le_one_right hNumNonneg hDle1
  have hFracGe2 : C * C * sbAsmGrowthB * (1 / 8 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    le_trans hNumGe hFracGe
  have hargGe2 : (2 : ℝ) ≤
      2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hnua_pos : (0 : ℝ) < nu * (1 - alpha) := mul_pos hnu halphapos
    have : (0 : ℝ) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
      have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMpos.le, hK]
      positivity
    linarith only [this]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogargGe : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hargGe2
  have hlogpow_ge : (Real.log 2) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2pos.le hlogargGe (by norm_num)
  have hinner_ge : C * C * sbAsmGrowthB * (1 / 8 : ℝ) * (Real.log 2) ^ (12 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have hlhs_nonneg : (0 : ℝ) ≤ C * C * sbAsmGrowthB * (1 / 8 : ℝ) := by positivity
    exact mul_le_mul hFracGe2 hlogpow_ge (by positivity) (by positivity)
  have h256 : (256 : ℝ) * C ≤ C * C * sbAsmGrowthB * (1 / 8 : ℝ) * (Real.log 2) ^ (12 : ℝ) := by
    have hB := sbAsmGrowthB_mul_log2pow
    have hCCge : C ≤ C * C := by nlinarith only [hC1, hCpos]
    nlinarith only [hB, hCCge, hCpos]
  set inner : ℝ :=
    C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) with hinnerdef
  have hinner256C : (256 : ℝ) * C ≤ inner := le_trans h256 hinner_ge
  have hinner1 : (1 : ℝ) ≤ inner := le_trans (by linarith only [hC1] : (1:ℝ) ≤ 256 * C) hinner256C
  have hexp1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ halphapos]; linarith only [halphale1]
  have hpow_ge : inner ^ (1 : ℝ) ≤ inner ^ ((1 : ℝ) / (1 - alpha)) :=
    Real.rpow_le_rpow_of_exponent_le hinner1 hexp1
  rw [Real.rpow_one] at hpow_ge
  have h64C : (64 : ℝ) * C ≤ inner := by linarith only [hinner256C, hCpos]
  exact le_trans h64C hpow_ge

/-- **`nu`-dependent strengthening of `sbAsm_lNaught_ge_C_of_M_ge`:** `lNaught`
dominates `64 C / nu^4` (not merely `64 C`) once its own `M`-argument is at
least `C * sbAsmGrowthB`. Needed to dominate a residual `L^{-99}`-type term
via the crude growth bound `shom_r ≤ C nu⁻¹(1+r)` uniformly in `nu ∈ (0,1]`:
as `nu → 0` the threshold itself forces `L` correspondingly larger, since
`lNaught`'s own closed form divides by `nu^4`. Same proof as
`sbAsm_lNaught_ge_C_of_M_ge`, only keeping the `nu^4` factor instead of
discarding it via `nu ≤ 1`. -/
theorem sbAsm_lNaught_ge_C_div_nu4 {C M alpha cStar nu K : ℝ}
    (hC1 : 1 ≤ C) (hM : C * sbAsmGrowthB ≤ M)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hK : 0 ≤ K) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    (64 : ℝ) * C / nu ^ (4 : ℝ) ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hBpos : (0 : ℝ) < sbAsmGrowthB := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
    unfold sbAsmGrowthB
    positivity
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (mul_pos hCpos hBpos) hM
  have hcStar3ge : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hcStar hcStar2 (by norm_num : (-(3 : ℝ)) ≤ 0)
    have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [h2] at h; exact h
  have hcStar3pos : (0 : ℝ) < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hMK1 : M ≤ M + 1 + K := by linarith only [hK]
  have hNumGe : C * C * sbAsmGrowthB * (1 / 8 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have step1 : C * M * cStar ^ (-(3 : ℝ)) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMK1 hCpos.le) hcStar3pos.le
    have step2 : C * (C * sbAsmGrowthB) * (1 / 8 : ℝ) ≤ C * M * cStar ^ (-(3 : ℝ)) := by
      have h1 : C * (C * sbAsmGrowthB) * (1 / 8 : ℝ) ≤ C * M * (1 / 8 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hM hCpos.le
        nlinarith only [this]
      have h2 : C * M * (1 / 8 : ℝ) ≤ C * M * cStar ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcStar3ge (mul_pos hCpos hMpos).le
      linarith only [h1, h2]
    nlinarith only [step1, step2]
  have halphapos : (0 : ℝ) < 1 - alpha := by linarith only [halpha1]
  have halphale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
  have hD1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow halphapos.le halphale1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hD1pos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos halphapos _
  have hD2pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hDpos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := mul_pos hD1pos hD2pos
  have hDlenu4 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ nu ^ (4 : ℝ) := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * nu ^ (4 : ℝ) :=
          mul_le_mul_of_nonneg_right hD1 hD2pos.le
      _ = nu ^ (4 : ℝ) := by ring
  have hNumNonneg : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMpos.le, hK]
    positivity
  have hFracGe : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / nu ^ (4 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_le_div_of_nonneg_left hNumNonneg hDpos hDlenu4
  have hFracGe2 : C * C * sbAsmGrowthB * (1 / 8 : ℝ) / nu ^ (4 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    have hdivmono : C * C * sbAsmGrowthB * (1 / 8 : ℝ) / nu ^ (4 : ℝ) ≤
        C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / nu ^ (4 : ℝ) :=
      div_le_div_of_nonneg_right hNumGe hD2pos.le
    exact le_trans hdivmono hFracGe
  have hargGe2 : (2 : ℝ) ≤
      2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hnua_pos : (0 : ℝ) < nu * (1 - alpha) := mul_pos hnu halphapos
    have : (0 : ℝ) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
      have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMpos.le, hK]
      positivity
    linarith only [this]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogargGe : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hargGe2
  have hlogpow_ge : (Real.log 2) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2pos.le hlogargGe (by norm_num)
  have hinner_ge : C * C * sbAsmGrowthB * (1 / 8 : ℝ) / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have hlhs_nonneg : (0 : ℝ) ≤ C * C * sbAsmGrowthB * (1 / 8 : ℝ) / nu ^ (4 : ℝ) := by positivity
    exact mul_le_mul hFracGe2 hlogpow_ge (by positivity) (by positivity)
  have h256 : (256 : ℝ) * C / nu ^ (4 : ℝ) ≤
      C * C * sbAsmGrowthB * (1 / 8 : ℝ) / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ) := by
    have hB := sbAsmGrowthB_mul_log2pow
    have hCCge : C ≤ C * C := by nlinarith only [hC1, hCpos]
    have hkey : (256 : ℝ) * C ≤ C * C * sbAsmGrowthB * (1 / 8 : ℝ) * (Real.log 2) ^ (12 : ℝ) := by
      nlinarith only [hB, hCCge, hCpos]
    have hdiv := div_le_div_of_nonneg_right hkey hD2pos.le
    have heq : C * C * sbAsmGrowthB * (1 / 8 : ℝ) * (Real.log 2) ^ (12 : ℝ) / nu ^ (4 : ℝ) =
        C * C * sbAsmGrowthB * (1 / 8 : ℝ) / nu ^ (4 : ℝ) * (Real.log 2) ^ (12 : ℝ) := by ring
    rwa [heq] at hdiv
  set inner : ℝ :=
    C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) with hinnerdef
  have hinner256C : (256 : ℝ) * C / nu ^ (4 : ℝ) ≤ inner := le_trans h256 hinner_ge
  have hnu4le1 : nu ^ (4 : ℝ) ≤ 1 :=
    le_trans (Real.rpow_le_rpow hnu.le hnu1 (by norm_num)) (le_of_eq (Real.one_rpow _))
  have hinv_ge : (1 : ℝ) ≤ 1 / nu ^ (4 : ℝ) := by
    rw [le_div_iff₀ hD2pos]; linarith only [hnu4le1]
  have hinner1 : (1 : ℝ) ≤ inner := by
    have h1 : (1 : ℝ) ≤ 256 * C / nu ^ (4 : ℝ) := by
      have h2 : (1 : ℝ) * 1 ≤ 256 * C * (1 / nu ^ (4 : ℝ)) := by
        apply mul_le_mul (by linarith only [hC1]) hinv_ge (by norm_num) (by nlinarith only [hC1])
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 256 * C * (1 / nu ^ (4 : ℝ)) := h2
        _ = 256 * C / nu ^ (4 : ℝ) := by ring
    linarith only [h1, hinner256C]
  have hexp1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ halphapos]; linarith only [halphale1]
  have hpow_ge : inner ^ (1 : ℝ) ≤ inner ^ ((1 : ℝ) / (1 - alpha)) :=
    Real.rpow_le_rpow_of_exponent_le hinner1 hexp1
  rw [Real.rpow_one] at hpow_ge
  have h64C : (64 : ℝ) * C / nu ^ (4 : ℝ) ≤ inner := by
    have hle : (64 : ℝ) * C / nu ^ (4 : ℝ) ≤ 256 * C / nu ^ (4 : ℝ) := by
      apply div_le_div_of_nonneg_right _ hD2pos.le
      linarith only [hCpos]
    linarith only [hle, hinner256C]
  exact le_trans h64C hpow_ge

/-- Variant of `sbAsm_inflate_A` without the extra `C` multiplying `M` on the
left: `lNaught C0 (K'*M) ... ≤ lNaught C (C*M) ...`, given `1 ≤ C` (so
`M ≤ C*M`). -/
theorem sbAsm_inflate_C
    {C0 K' C M alpha cStar nu K : ℝ}
    (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hC1 : 1 ≤ C) (halpha : alpha < 1) (hcStar : 0 < cStar)
    (hnu : 0 < nu) (hK : 0 ≤ K) (hK' : 1 ≤ K')
    (hCbig : C0 * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) ≤ C) :
    lNaught C0 (K' * M) alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K := by
  have hC : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have h1 := sbAsm_inflate_A hC0 hM hC halpha hcStar hnu hK hK' hCbig
  have h2 : K' * M ≤ K' * (C * M) := by
    have hMCM : M ≤ C * M := le_mul_of_one_le_left hM hC1
    exact mul_le_mul_of_nonneg_left hMCM (le_trans zero_le_one hK')
  have hK'Mnn : (0 : ℝ) ≤ K' * M := mul_nonneg (le_trans zero_le_one hK') hM
  exact le_trans (lNaught_mono_M hC0 hK'Mnn h2 hK hcStar hnu halpha) h1

/-- Threshold transfer at a FIXED (not `M`-proportional) second argument
`Mfix`: `lNaught C0 Mfix ... ≤ lNaught C (C*M) ...`, given `C0 ≤ C`,
`Mfix ≤ C`, `1 ≤ M`, `1 ≤ C`. -/
theorem sbAsm_inflate_fixed
    {C0 Mfix C M alpha cStar nu K : ℝ}
    (hC0 : 0 ≤ C0) (hMfix : 0 ≤ Mfix) (hM : 1 ≤ M) (hC1 : 1 ≤ C)
    (halpha : alpha < 1) (hcStar : 0 < cStar) (hnu : 0 < nu) (hK : 0 ≤ K)
    (hC0C : C0 ≤ C) (hMfixC : Mfix ≤ C) :
    lNaught C0 Mfix alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K := by
  have hC : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
  have h1 : lNaught C0 Mfix alpha cStar nu K ≤ lNaught C Mfix alpha cStar nu K :=
    lNaught_mono_const hC0 hC0C hMfix hK hcStar hnu halpha
  have hCM : C ≤ C * M := le_mul_of_one_le_right hC hM
  have h2 : lNaught C Mfix alpha cStar nu K ≤ lNaught C (C * M) alpha cStar nu K :=
    lNaught_mono_M hC hMfix (le_trans hMfixC hCM) hK hcStar hnu halpha
  exact h1.trans h2

/-- **A fast-decaying residual `Cres * t^{-p}` is dominated by `ε * M * L^α *
shom_L^{-2} * log³L`**, given: `t` is at least `L/rho` (`rho ≥ 1`); `p ≥ 97`
(covers both the `L^{-99}` residual of `#independence-and-ratio` and the
`n^{-3000}` residual of `#homog-below-bound`); `σ̄_L` obeys the crude
UNCONDITIONAL upper bound `σ̄_L ≤ Ccrude nu⁻¹(1+L)`
(`sbAsm_crude_growth_bound`); and `L` is forced large relative to a FIXED
`T ≥ 1` via `T / nu^4 ≤ L` (as `sbAsm_lNaught_ge_C_div_nu4` gives from the
threshold, `nu`-dependently). The only real content: since `T ≥ 1` and the
exponent `p + alpha - 2 ≥ p - 2 ≥ 1`, `T^{p+alpha-2} ≥ T^{p-2} ≥ T` (`rpow`
monotone in the exponent for a base `≥ 1`), so a LINEAR requirement on `T`
(`hTbig`) suffices — no exponential growth of the outer constant is needed. -/
theorem sbAsm_residual_dominate {d : ℕ} [NeZero d]
    {nu alpha M rho p Cres eps T Ccrude : ℝ} {L t : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hM : 1 ≤ M) (hα0 : 0 ≤ alpha) (_hα1 : alpha < 1)
    (hL3 : 3 ≤ L) (hrho1 : 1 ≤ rho) (ht_ge : (L : ℝ) ≤ rho * (t : ℝ))
    (hp97 : (97 : ℝ) ≤ p) (hCresnn : 0 ≤ Cres) (hepspos : 0 < eps)
    (hCcrude1 : 1 ≤ Ccrude)
    (hCrude : sigmaBarInfinite nu L P ≤ Ccrude * nu⁻¹ * (1 + (L : ℝ)))
    (hT1 : 1 ≤ T) (hTL : T / nu ^ (4 : ℝ) ≤ (L : ℝ))
    (hTbig : rho ^ p * 4 * Ccrude ^ 2 * Cres ≤ eps * T) :
    Cres * (t : ℝ) ^ (-p) ≤
      eps * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
  have hL3R : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL3
  have hLRpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL3R]
  have htpos : (0 : ℝ) < (t : ℝ) := by
    have hrhopos : (0 : ℝ) < rho := lt_of_lt_of_le one_pos hrho1
    nlinarith only [ht_ge, hLRpos, hrhopos]
  have hLrhot : (L : ℝ) / rho ≤ (t : ℝ) := by
    rw [div_le_iff₀ (lt_of_lt_of_le one_pos hrho1)]; linarith only [ht_ge]
  have hLrhotpos : (0 : ℝ) < (L : ℝ) / rho := by positivity
  -- Step 1: `t^{-p} ≤ rho^p * L^{-p}`.
  have hppos : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp97
  have hstep1 : (t : ℝ) ^ (-p) ≤ ((L : ℝ) / rho) ^ (-p) := by
    rw [Real.rpow_neg htpos.le, Real.rpow_neg hLrhotpos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hLrhotpos _) (Real.rpow_le_rpow hLrhotpos.le hLrhot hppos.le)
  have hLrhoeq : ((L : ℝ) / rho) ^ (-p) = rho ^ p * (L : ℝ) ^ (-p) := by
    rw [Real.div_rpow hLRpos.le (le_trans zero_le_one hrho1), Real.rpow_neg hLRpos.le,
      Real.rpow_neg (le_trans zero_le_one hrho1)]
    field_simp
  rw [hLrhoeq] at hstep1
  have hCresnnrho : (0 : ℝ) ≤ Cres * rho ^ p := by positivity
  have hstep2 : Cres * (t : ℝ) ^ (-p) ≤ Cres * (rho ^ p * (L : ℝ) ^ (-p)) :=
    mul_le_mul_of_nonneg_left hstep1 hCresnn
  -- Step 2 (crude growth): `shom_L^{-2} ≥ nu^2 / (4 Ccrude^2 L^2)`, in the
  -- cross-multiplied division form (robust for `rw`/`div_le_div_iff`).
  have hSLpos : (0 : ℝ) < sigmaBarInfinite nu L P := sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
  have hCcrudepos : (0 : ℝ) < Ccrude := lt_of_lt_of_le one_pos hCcrude1
  have hSLle : sigmaBarInfinite nu L P ≤ 2 * Ccrude * nu⁻¹ * (L : ℝ) := by
    have h1L : (1 : ℝ) + (L : ℝ) ≤ 2 * (L : ℝ) := by linarith only [hL3R]
    have h2 : Ccrude * nu⁻¹ * (1 + (L : ℝ)) ≤ Ccrude * nu⁻¹ * (2 * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left h1L (by positivity)
    calc sigmaBarInfinite nu L P ≤ Ccrude * nu⁻¹ * (1 + (L : ℝ)) := hCrude
      _ ≤ Ccrude * nu⁻¹ * (2 * (L : ℝ)) := h2
      _ = 2 * Ccrude * nu⁻¹ * (L : ℝ) := by ring
  have hSLsqle : sigmaBarInfinite nu L P ^ 2 ≤ (2 * Ccrude * nu⁻¹ * (L : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hSLpos.le hSLle 2
  have hnu2pos : (0 : ℝ) < nu ^ 2 := by positivity
  have hSLsqEq : (2 * Ccrude * nu⁻¹ * (L : ℝ)) ^ 2 =
      4 * Ccrude ^ 2 * (L : ℝ) ^ 2 / nu ^ 2 := by
    field_simp; ring
  rw [hSLsqEq] at hSLsqle
  have hSLsqpos : (0 : ℝ) < sigmaBarInfinite nu L P ^ 2 := pow_pos hSLpos 2
  have hcross : sigmaBarInfinite nu L P ^ 2 * nu ^ 2 ≤ 4 * Ccrude ^ 2 * (L : ℝ) ^ 2 := by
    rw [le_div_iff₀ hnu2pos] at hSLsqle
    exact hSLsqle
  have hL2pos : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  have hSLinvsq_ge2 : nu ^ 2 / (L : ℝ) ^ 2 ≤ 4 * Ccrude ^ 2 / sigmaBarInfinite nu L P ^ 2 := by
    rw [le_div_iff₀ hSLsqpos, div_mul_eq_mul_div, div_le_iff₀ hL2pos]
    nlinarith only [hcross]
  have hSLnegrpow : (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) = (sigmaBarInfinite nu L P ^ 2)⁻¹ := by
    rw [Real.rpow_neg hSLpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- Step 3: `nu^2 * L^{p+alpha-2} ≥ T`, from `L ≥ T / nu^4` and `nu ≤ 1`
  -- (the negative-exponent power of `nu` this produces is itself `≥ 1`).
  have hnu4pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hTdivpos : (0 : ℝ) < T / nu ^ (4 : ℝ) := by positivity
  have hexp1 : (0 : ℝ) ≤ p + alpha - 2 := by linarith only [hp97, hα0]
  have hLpowge : (T / nu ^ (4 : ℝ)) ^ (p + alpha - 2) ≤ (L : ℝ) ^ (p + alpha - 2) :=
    Real.rpow_le_rpow hTdivpos.le hTL hexp1
  have hnu2Lpow_ge : nu ^ (2 : ℝ) * (T / nu ^ (4 : ℝ)) ^ (p + alpha - 2) ≤
      nu ^ (2 : ℝ) * (L : ℝ) ^ (p + alpha - 2) :=
    mul_le_mul_of_nonneg_left hLpowge (Real.rpow_nonneg hnu.le _)
  have hcombine : nu ^ (2 : ℝ) * (T / nu ^ (4 : ℝ)) ^ (p + alpha - 2) =
      T ^ (p + alpha - 2) * nu ^ (2 - 4 * (p + alpha - 2)) := by
    rw [Real.div_rpow (le_trans zero_le_one hT1) hnu4pos.le, ← Real.rpow_mul hnu.le]
    rw [Real.rpow_sub hnu 2 (4 * (p + alpha - 2))]
    field_simp
  have hexpneg : 2 - 4 * (p + alpha - 2) ≤ (0 : ℝ) := by linarith only [hp97, hα0]
  have hnupow_ge1 : (1 : ℝ) ≤ nu ^ (2 - 4 * (p + alpha - 2)) := by
    calc (1 : ℝ) = nu ^ (0 : ℝ) := (Real.rpow_zero nu).symm
      _ ≤ nu ^ (2 - 4 * (p + alpha - 2)) :=
        Real.rpow_le_rpow_of_exponent_ge hnu hnu1 hexpneg
  have hTppos : (0 : ℝ) < T ^ (p + alpha - 2) := Real.rpow_pos_of_pos (by linarith only [hT1]) _
  have hTexpp2ge : (T : ℝ) ^ (p - 2) ≤ T ^ (p + alpha - 2) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hα0])
  have hTge1 : T ≤ T ^ (p - 2) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ T ^ (p - 2) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hp97])
  have hKeyR : T ^ (p + alpha - 2) ≤ nu ^ (2 : ℝ) * (L : ℝ) ^ (p + alpha - 2) := by
    have hstepA : T ^ (p + alpha - 2) ≤ nu ^ (2 : ℝ) * (T / nu ^ (4 : ℝ)) ^ (p + alpha - 2) := by
      rw [hcombine]
      calc T ^ (p + alpha - 2) = T ^ (p + alpha - 2) * 1 := by ring
        _ ≤ T ^ (p + alpha - 2) * nu ^ (2 - 4 * (p + alpha - 2)) :=
            mul_le_mul_of_nonneg_left hnupow_ge1 hTppos.le
    exact le_trans hstepA hnu2Lpow_ge
  have hKey0 : T ≤ nu ^ (2 : ℝ) * (L : ℝ) ^ (p + alpha - 2) := le_trans hTge1
    (le_trans hTexpp2ge hKeyR)
  have hnu2eq : nu ^ (2 : ℝ) = nu ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hKey0' : T ≤ nu ^ 2 * (L : ℝ) ^ (p + alpha - 2) := by rw [← hnu2eq]; exact hKey0
  -- Step 4: the target real-power inequality `Cres*rho^p*4*Ccrude² ≤ eps*(nu²*L^{p+α-2})`.
  have hKeyMain : Cres * rho ^ p * 4 * Ccrude ^ 2 ≤ eps * (nu ^ 2 * (L : ℝ) ^ (p + alpha - 2)) := by
    have hTbigEq : Cres * rho ^ p * 4 * Ccrude ^ 2 = rho ^ p * 4 * Ccrude ^ 2 * Cres := by ring
    rw [hTbigEq]
    calc rho ^ p * 4 * Ccrude ^ 2 * Cres ≤ eps * T := hTbig
      _ ≤ eps * (nu ^ 2 * (L : ℝ) ^ (p + alpha - 2)) :=
          mul_le_mul_of_nonneg_left hKey0' hepspos.le
  -- Step 5: multiply through by `L^{-p} ≥ 0` and simplify the `L`-power.
  have hLnegp : (0 : ℝ) < (L : ℝ) ^ (-p) := Real.rpow_pos_of_pos hLRpos _
  have hKeyMul : Cres * rho ^ p * 4 * Ccrude ^ 2 * (L : ℝ) ^ (-p) ≤
      eps * (nu ^ 2 * (L : ℝ) ^ (p + alpha - 2)) * (L : ℝ) ^ (-p) :=
    mul_le_mul_of_nonneg_right hKeyMain hLnegp.le
  have hLprodEq : (L : ℝ) ^ (p + alpha - 2) * (L : ℝ) ^ (-p) = (L : ℝ) ^ (alpha - 2) := by
    rw [← Real.rpow_add hLRpos]; congr 1; ring
  have hRHSeq : eps * (nu ^ 2 * (L : ℝ) ^ (p + alpha - 2)) * (L : ℝ) ^ (-p) =
      eps * nu ^ 2 * (L : ℝ) ^ (alpha - 2) := by
    rw [show eps * (nu ^ 2 * (L : ℝ) ^ (p + alpha - 2)) * (L : ℝ) ^ (-p) =
        eps * nu ^ 2 * ((L : ℝ) ^ (p + alpha - 2) * (L : ℝ) ^ (-p)) by ring, hLprodEq]
  rw [hRHSeq] at hKeyMul
  have hLalpha2eq : (L : ℝ) ^ alpha / (L : ℝ) ^ 2 = (L : ℝ) ^ (alpha - 2) := by
    rw [Real.rpow_sub hLRpos, show (L : ℝ) ^ (2 : ℝ) = (L : ℝ) ^ 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
  rw [← hLalpha2eq] at hKeyMul
  have hEqL : Cres * rho ^ p * 4 * Ccrude ^ 2 * (L : ℝ) ^ (-p) =
      Cres * (rho ^ p * (L : ℝ) ^ (-p)) * (4 * Ccrude ^ 2) := by ring
  have hEqR : eps * nu ^ 2 * ((L : ℝ) ^ alpha / (L : ℝ) ^ 2) =
      eps * (L : ℝ) ^ alpha * (nu ^ 2 / (L : ℝ) ^ 2) := by ring
  rw [hEqL, hEqR] at hKeyMul
  -- Step 6: combine with `nu²/L² ≤ 4Ccrude²/shom_L²` (`hSLinvsq_ge2`), divide
  -- out the shared `4 Ccrude²` factor, and finish with `M ≥ 1`, `log³L ≥ 1`.
  have hLalphann : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg hLRpos.le _
  have hKeyMul2 : Cres * (rho ^ p * (L : ℝ) ^ (-p)) * (4 * Ccrude ^ 2) ≤
      eps * (L : ℝ) ^ alpha * (4 * Ccrude ^ 2 / sigmaBarInfinite nu L P ^ 2) := by
    have hstep : eps * (L : ℝ) ^ alpha * (nu ^ 2 / (L : ℝ) ^ 2) ≤
        eps * (L : ℝ) ^ alpha * (4 * Ccrude ^ 2 / sigmaBarInfinite nu L P ^ 2) :=
      mul_le_mul_of_nonneg_left hSLinvsq_ge2 (by positivity)
    exact le_trans hKeyMul hstep
  have hEqR2 : eps * (L : ℝ) ^ alpha * (4 * Ccrude ^ 2 / sigmaBarInfinite nu L P ^ 2) =
      eps * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P ^ 2)⁻¹ * (4 * Ccrude ^ 2) := by
    rw [div_eq_mul_inv]; ring
  rw [hEqR2] at hKeyMul2
  have h4Ccrudepos : (0 : ℝ) < 4 * Ccrude ^ 2 := by positivity
  have hKeyMul3 : Cres * (rho ^ p * (L : ℝ) ^ (-p)) ≤
      eps * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P ^ 2)⁻¹ :=
    le_of_mul_le_mul_right hKeyMul2 h4Ccrudepos
  have hKeyFinal : Cres * (t : ℝ) ^ (-p) ≤
      eps * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) := by
    rw [hSLnegrpow]; exact le_trans hstep2 hKeyMul3
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    linarith only [Real.exp_one_lt_d9]
  have hlogLgt1 : (1 : ℝ) < Real.log (L : ℝ) :=
    lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hL3R)
  have hlog3Lge1 : (1 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 : (1 : ℝ) ^ (3 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hlogLgt1.le (by norm_num)
    simpa using h1
  have hbase_nonneg : (0 : ℝ) ≤
      eps * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) := by
    have h2 : (0 : ℝ) ≤ (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) := Real.rpow_nonneg hSLpos.le _
    positivity
  have hlast : eps * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) ≤
      eps * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
        Real.log (L : ℝ) ^ (3 : ℝ) := by
    have hM_mono : eps * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) ≤
        eps * M * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) := by
      calc eps * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) =
            eps * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) * 1 := by ring
        _ ≤ eps * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) * M :=
            mul_le_mul_of_nonneg_left hM hbase_nonneg
        _ = eps * M * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) := by ring
    calc eps * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) =
          eps * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) * 1 := by ring
      _ ≤ eps * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) *
            Real.log (L : ℝ) ^ (3 : ℝ) := mul_le_mul_of_nonneg_left hlog3Lge1 hbase_nonneg
      _ ≤ eps * M * ((L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ))) *
            Real.log (L : ℝ) ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right hM_mono
            (Real.rpow_nonneg (by linarith only [hlogLgt1] : (0 : ℝ) ≤ Real.log (L : ℝ)) 3)
      _ = eps * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
            Real.log (L : ℝ) ^ (3 : ℝ) := by ring
  exact le_trans hKeyFinal hlast

end


end SuperdiffusionCLT.Section4.SigmaBarComparison
