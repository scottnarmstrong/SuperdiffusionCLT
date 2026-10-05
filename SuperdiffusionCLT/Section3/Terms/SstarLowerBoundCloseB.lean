/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarLowerBoundClose
public import SuperdiffusionCLT.Section3.Terms.SstarLowerBoundWorkB
public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridgesB
public import SuperdiffusionCLT.Section3.Setup.ThresholdTranslation
public import SuperdiffusionCLT.Section3.Setup.QuenchedLowerBound
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.Terms
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums

namespace SuperdiffusionCLT.Section3.Terms

/-! ## The threshold under the paper's own `cStar` range

The threshold lemmas of `Section3/Setup/ThresholdTranslation.lean`
(the five-le-`m`, eleven-le-log and quenched-inner-log-positivity bounds) all carry
`cStar <= 1`, but the
statement supplies only `0 < cStar` and J5 supplies only `cStar <= 2`
(`Frozen.Assumptions.ShellLawJ5.cStar_le_two`).  The lemmas below close that
gap: with `cStar <= 2` the scale factor `cStar ^ (-3)` is at least `1/8`, and
`eLvsNuTerm` is at least `1` on the standing range, so a threshold constant of at
least `10 ^ 8` forces `m >= 10 ^ 8 / 8 = 12500000`. -/

/-- `eLvsNuTerm >= 1` on the range `nu ∈ (0,1]`, `cStar > 0`, `K > 0`;
this replaces the `cStar <= 1` route. -/
theorem sstarCloseB_eLvsNuTerm_ge_one {nu cStar K : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hK : 0 < K) :
    (1 : ℝ) ≤ eLvsNuTerm nu cStar K := by
  have h1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h4 : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [h4]; linarith only [h2]
  have h4 : (4 : ℝ) ≤ 3 + nu⁻¹ + K := by linarith only [h1, hK]
  have hlogX : Real.log 4 ≤ Real.log (3 + nu⁻¹ + K) :=
    Real.log_le_log (by norm_num) h4
  have hlogXnn : (0 : ℝ) ≤ Real.log (3 + nu⁻¹ + K) := le_trans (by linarith only [hlog4]) hlogX
  have hlog4nn : (0 : ℝ) ≤ Real.log 4 := by linarith only [hlog4]
  have hK1 : (1 : ℝ) ≤ 1 + K := by linarith only [hK]
  have hterm2 : (1 : ℝ) ≤ (1 + K) * Real.log (3 + nu⁻¹ + K) := by
    have hmul := mul_le_mul hK1 hlogX hlog4nn (by linarith only [hK1])
    linarith only [hmul, hlog4]
  have hterm1 : (0 : ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) := eLvsNuTerm_term_one_nonneg hnu hcStar
  rw [eLvsNuTerm]
  linarith only [hterm1, hterm2]

/-- `cStar <= 2` forces `cStar ^ (-3) >= 1/8`. -/
theorem sstarCloseB_rpow_neg_three_ge {cStar : ℝ} (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2) :
    (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
  have hc3 : cStar ^ (3 : ℝ) ≤ 8 := by
    have h := (Real.rpow_le_rpow_iff hcStar.le (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (0 : ℝ) < 3)).mpr hcStar2
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
    rw [h8] at h; exact h
  have h3pos : (0 : ℝ) < cStar ^ (3 : ℝ) := Real.rpow_pos_of_pos hcStar 3
  rw [Real.rpow_neg hcStar.le]
  have h := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 8) h3pos).mpr hc3
  simpa only [one_div] using h

/-- **The threshold forces `m >= 12500000`** with only `cStar <= 2` and
`K > 0`, at any threshold constant `C >= 10 ^ 8`. -/
theorem sstarCloseB_scale_le_m {C nu cStar K : ℝ} {m : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hK : 0 < K) (hC : (100000000 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ)) :
    (12500000 : ℝ) ≤ (m : ℝ) := by
  have hE := sstarCloseB_eLvsNuTerm_ge_one hnu hnu1 hcStar hK
  have hscale := sstarCloseB_rpow_neg_three_ge hcStar hcStar2
  have h2 : (1 / 8 : ℝ) * 1 ≤ cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K :=
    mul_le_mul hscale hE (by norm_num) (by linarith only [hscale])
  have hmul := mul_le_mul hC h2 (by norm_num) (by linarith only [hC])
  have e : C * (cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K) =
      C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K := by ring
  rw [e] at hmul
  linarith only [hmul, hft]

theorem sstarCloseB_five_le_m {C nu cStar K : ℝ} {m : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hK : 0 < K) (hC : (100000000 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ)) :
    5 ≤ m := by
  have h := sstarCloseB_scale_le_m hnu hnu1 hcStar hcStar2 hK hC hft
  have hcast : (12500000 : ℕ) ≤ m := by exact_mod_cast h
  omega

theorem sstarCloseB_one_le_L {C nu cStar K : ℝ} {m L : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hK : 0 < K) (hC : (100000000 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ))
    (hmL : m ≤ L) :
    1 ≤ L := by
  have h5 := sstarCloseB_five_le_m hnu hnu1 hcStar hcStar2 hK hC hft
  omega

theorem sstarCloseB_eleven_le_log {C nu cStar K : ℝ} {m L : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hK : 0 < K) (hC : (100000000 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ))
    (hmL : m ≤ L) :
    (11 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by
  have h250 := sstarCloseB_scale_le_m hnu hnu1 hcStar hcStar2 hK hC hft
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith only [h250]
  have hm1 : (0 : ℕ) < m := Nat.cast_pos.1 hmpos
  have h1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hpos : (0 : ℝ) < nu⁻¹ * ((m : ℕ) : ℝ) :=
    mul_pos (inv_pos.2 hnu) (Nat.cast_pos.2 hm1)
  have hexp11 : Real.exp (11 : ℝ) = (Real.exp 1) ^ (11 : ℕ) := by
    rw [← Real.exp_nat_mul (x := (1 : ℝ)) (n := 11)]; norm_num
  have hexp1 : Real.exp 1 ≤ (3 : ℝ) :=
    le_trans (lt_trans Real.exp_one_lt_d9 (by norm_num)).le (le_refl 3)
  have hpowle : (Real.exp 1) ^ (11 : ℕ) ≤ ((3 : ℝ)) ^ (11 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_nonneg 1) hexp1 (11 : ℕ)
  have hbig : ((3 : ℝ)) ^ (11 : ℕ) = 177147 := by norm_num
  rw [hbig] at hpowle
  have hge : (177147 : ℝ) ≤ nu⁻¹ * ((m : ℕ) : ℝ) := by
    have hge' := mul_le_mul_of_nonneg_left h250 (by linarith only [h1])
    linarith only [hge', h1]
  have hbound : Real.exp 11 ≤ nu⁻¹ * ((m : ℕ) : ℝ) := by
    linarith only [hexp11, hpowle, hge]
  have h11m : (11 : ℝ) ≤ Real.log (nu⁻¹ * ((m : ℕ) : ℝ)) := by
    by_contra hlt
    have hgt : Real.log (nu⁻¹ * ((m : ℕ) : ℝ)) < 11 := not_le.mp hlt
    have hlt' : nu⁻¹ * ((m : ℕ) : ℝ) < Real.exp 11 :=
      (Real.log_lt_iff_lt_exp hpos).mp hgt
    exact hbound.not_gt hlt'
  have hmon := Real.log_le_log hpos (mul_le_mul_of_nonneg_left
    (Nat.cast_le.2 hmL) (inv_nonneg.2 hnu.le))
  exact le_trans h11m hmon

theorem sstarCloseB_quenchedInner_log_pos {C nu cStar K : ℝ} {m : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hK : 0 < K) (hC : (100000000 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ)) :
    (0 : ℝ) < Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) := by
  have h5 := sstarCloseB_five_le_m hnu hnu1 hcStar hcStar2 hK hC hft
  have hn0 : (2 : ℕ) ≤ quenchedInnerScale m := by
    simp only [quenchedInnerScale]; omega
  have h1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hcast : ((quenchedInnerScale m : ℕ) : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hn0
  have hprod : (2 : ℝ) ≤ nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ) :=
    calc (2 : ℝ) = (1 : ℝ) * (2 : ℝ) := by ring
      _ ≤ nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ) :=
          mul_le_mul h1 hcast (by norm_num) (by linarith only [h1])
  exact Real.log_pos (by linarith only [hprod])

/-- **The scale-absorption inequality `hk`** of
`Section3.Setup.sstar_lower_bound_quenched_of_anchors`, discharged from the
threshold with only `cStar <= 2`: the quenched inner scale
`quenchedInnerScale m = m/2` absorbs `6 log(ν⁻¹ L)`. -/
theorem sstarCloseB_six_log_le_inner {C nu cStar K : ℝ} {m L : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hK : 0 < K) (hC : (100000000 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ))
    (hmL : m ≤ L) (hmL2 : L ≤ 2 * m) :
    6 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((quenchedInnerScale m : ℕ) : ℝ) * Real.log 3 := by
  set T : ℝ := eLvsNuTerm nu cStar K with hTdef
  set n0 : ℕ := quenchedInnerScale m with hn0def
  have hT1 : (1 : ℝ) ≤ T := sstarCloseB_eLvsNuTerm_ge_one hnu hnu1 hcStar hK
  have hTpos : 0 < T := by linarith only [hT1]
  have hCpos : 0 < C := by linarith only [hC]
  have hm125 : (12500000 : ℝ) ≤ (m : ℝ) :=
    sstarCloseB_scale_le_m hnu hnu1 hcStar hcStar2 hK (by linarith only [hC]) hft
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by linarith only [hm125]
  -- `log(ν⁻¹) ≤ T`
  have hlogν : (0 : ℝ) ≤ Real.log (nu⁻¹) := Real.log_nonneg ((one_le_inv₀ hnu).2 hnu1)
  have hterm1 : (0 : ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) := eLvsNuTerm_term_one_nonneg hnu hcStar
  have hnuinv : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hX : nu⁻¹ ≤ 3 + nu⁻¹ + K := by linarith only [hK]
  have hlogX : Real.log (nu⁻¹) ≤ Real.log (3 + nu⁻¹ + K) :=
    Real.log_le_log (inv_pos.2 hnu) hX
  have h1K : (1 : ℝ) ≤ 1 + K := by linarith only [hK]
  have hterm2 : Real.log (nu⁻¹) ≤ (1 + K) * Real.log (3 + nu⁻¹ + K) := by
    have hmul := mul_le_mul h1K hlogX hlogν (by linarith only [h1K])
    simpa using hmul
  have hTexp : T = Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
        Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
      (1 + K) * Real.log (3 + nu⁻¹ + K) := by
    rw [hTdef, eLvsNuTerm]
  have hTlog : Real.log (nu⁻¹) ≤ T := by linarith only [hTexp, hterm1, hterm2]
  -- `6 T ≤ (1/12) n0`
  have hscale := sstarCloseB_rpow_neg_three_ge hcStar hcStar2
  have hU : (1 / 8) * T ≤ cStar ^ (-(3 : ℝ)) * T :=
    mul_le_mul_of_nonneg_right hscale hTpos.le
  have hCU : C * ((1 / 8) * T) ≤ C * (cStar ^ (-(3 : ℝ)) * T) :=
    mul_le_mul_of_nonneg_left hU hCpos.le
  have he : C * (cStar ^ (-(3 : ℝ)) * T) = C * cStar ^ (-(3 : ℝ)) * T := by ring
  rw [he] at hCU
  have hCT8 : C * T ≤ 8 * (m : ℝ) := by
    have h8 : 8 * (C * ((1 / 8) * T)) = C * T := by ring
    have hmon := mul_le_mul_of_nonneg_left (le_trans hCU hft) (by norm_num : (0 : ℝ) ≤ 8)
    rw [h8] at hmon
    exact hmon
  have h1e8T : (100000000 : ℝ) * T ≤ C * T := mul_le_mul_of_nonneg_right hC hTpos.le
  have hT48 : 6 * T ≤ 48 * (m : ℝ) / 100000000 := by linarith only [hCT8, h1e8T]
  have hm_le_n0 : m ≤ 2 * n0 + 1 := by
    rw [hn0def]; simp only [quenchedInnerScale]; omega
  have hn0low : (m : ℝ) / 2 - 1 / 2 ≤ (n0 : ℝ) := by
    have h := Nat.cast_le (α := ℝ).2 hm_le_n0
    push_cast at h
    linarith only [h]
  have hnum : 48 * (m : ℝ) / 100000000 ≤ (1 / 12) * ((m : ℝ) / 2 - 1 / 2) := by
    linarith only [hm125]
  have hA : 6 * T ≤ (1 / 12) * (n0 : ℝ) :=
    le_trans (le_trans hT48 hnum) (mul_le_mul_of_nonneg_left hn0low (by norm_num))
  -- `12 √6 √n0 ≤ (1/12) n0`
  have hL1 : 1 ≤ L := by
    have hcast : (12500000 : ℕ) ≤ m := by exact_mod_cast hm125
    omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hn0ge : (124609 : ℕ) ≤ n0 := by
    rw [hn0def]; simp only [quenchedInnerScale]
    have hcast : (12500000 : ℕ) ≤ m := by exact_mod_cast hm125
    omega
  have hsn0 : (353 : ℝ) ≤ Real.sqrt (n0 : ℝ) := by
    have h353 : Real.sqrt (124609 : ℝ) = 353 := by
      rw [show (124609 : ℝ) = 353 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h353]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn0ge)
  have hsqrt6 : Real.sqrt 6 ≤ (2.45 : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (6 : ℝ) ≤ 2.45 ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2.45)] at h
  have hsn0nn : (0 : ℝ) ≤ Real.sqrt (n0 : ℝ) := Real.sqrt_nonneg _
  have h12s6 : 12 * Real.sqrt 6 ≤ (29.4 : ℝ) := by linarith only [hsqrt6]
  have h29 : (29.4 : ℝ) ≤ (1 / 12) * Real.sqrt (n0 : ℝ) := by linarith only [hsn0]
  have hstep1 : (12 * Real.sqrt 6) * Real.sqrt (n0 : ℝ) ≤
      (29.4 : ℝ) * Real.sqrt (n0 : ℝ) := mul_le_mul_of_nonneg_right h12s6 hsn0nn
  have hstep2 : (29.4 : ℝ) * Real.sqrt (n0 : ℝ) ≤
      ((1 / 12) * Real.sqrt (n0 : ℝ)) * Real.sqrt (n0 : ℝ) :=
    mul_le_mul_of_nonneg_right h29 hsn0nn
  have hstep3 : ((1 / 12) * Real.sqrt (n0 : ℝ)) * Real.sqrt (n0 : ℝ) =
      (1 / 12) * (n0 : ℝ) := by
    rw [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n0)]
  have hB : (12 * Real.sqrt 6) * Real.sqrt (n0 : ℝ) ≤ (1 / 12) * (n0 : ℝ) := by
    rw [hstep3] at hstep2
    exact le_trans hstep1 hstep2
  -- `√(2m) ≤ √6 √n0`
  have hn0one : (1 : ℝ) ≤ (n0 : ℝ) := by
    have h := Nat.cast_le (α := ℝ).2 (le_trans (by norm_num : 1 ≤ 124609) hn0ge)
    push_cast at h; exact h
  have hm_ge_n0 : 2 * (m : ℝ) ≤ 6 * (n0 : ℝ) := by
    have h := Nat.cast_le (α := ℝ).2 hm_le_n0
    push_cast at h
    linarith only [h, hn0one]
  have hsqrt_mono : Real.sqrt (2 * (m : ℝ)) ≤ Real.sqrt (6 * (n0 : ℝ)) :=
    Real.sqrt_le_sqrt hm_ge_n0
  have hsqrt_split : Real.sqrt (6 * (n0 : ℝ)) = Real.sqrt 6 * Real.sqrt (n0 : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  have hB2 : 12 * Real.sqrt (2 * (m : ℝ)) ≤ (1 / 12) * (n0 : ℝ) := by
    have h1 : 12 * Real.sqrt (2 * (m : ℝ)) ≤ 12 * Real.sqrt (6 * (n0 : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt_mono (by norm_num)
    rw [hsqrt_split] at h1
    have he : (12 * Real.sqrt 6) * Real.sqrt (n0 : ℝ) =
        12 * (Real.sqrt 6 * Real.sqrt (n0 : ℝ)) := by ring
    rw [← he] at h1
    exact le_trans h1 hB
  -- the logarithm
  have hlogL : Real.log (L : ℝ) ≤ Real.log (2 * (m : ℝ)) := by
    refine Real.log_le_log hLpos ?_
    exact_mod_cast hmL2
  have hlog2m : Real.log (2 * (m : ℝ)) ≤ 2 * Real.sqrt (2 * (m : ℝ)) := by
    have h := Real.log_le_rpow_div (x := 2 * (m : ℝ)) (ε := (1 : ℝ) / 2)
      (by positivity) (by norm_num)
    have he : (2 * (m : ℝ)) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) =
        2 * Real.sqrt (2 * (m : ℝ)) := by
      rw [Real.sqrt_eq_rpow]; ring
    linarith only [h, he]
  have hlog3 : (1 / 6 : ℝ) ≤ Real.log 3 := by
    have h1 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith only [h1, h2]
  have hsplit : Real.log (nu⁻¹ * (L : ℝ)) = Real.log (nu⁻¹) + Real.log (L : ℝ) :=
    Real.log_mul (inv_ne_zero (ne_of_gt hnu)) (ne_of_gt hLpos)
  rw [hsplit]
  have k1 : 6 * Real.log (nu⁻¹) ≤ 6 * T := mul_le_mul_of_nonneg_left hTlog (by norm_num)
  have k2 : 6 * Real.log (L : ℝ) ≤ 6 * (2 * Real.sqrt (2 * (m : ℝ))) :=
    mul_le_mul_of_nonneg_left (le_trans hlogL hlog2m) (by norm_num)
  have k3 : 6 * (2 * Real.sqrt (2 * (m : ℝ))) = 12 * Real.sqrt (2 * (m : ℝ)) := by ring
  rw [k3] at k2
  have hsum : 6 * (Real.log (nu⁻¹) + Real.log (L : ℝ)) ≤ (1 / 6) * (n0 : ℝ) := by
    linarith only [k1, k2, hA, hB2]
  have hfin : (1 / 6) * (n0 : ℝ) ≤ (n0 : ℝ) * Real.log 3 := by
    have h := mul_le_mul_of_nonneg_left hlog3 (Nat.cast_nonneg n0)
    linarith only [h]
  exact le_trans hsum hfin

/-! ## Named `d`-only constants -/

/-- The mixing anchor's constant, named as a `d`-only value. -/
noncomputable def sstarCloseBMixConst (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (sstarClose_mixAnchor_unconditional d)

theorem sstarCloseBMixConst_pos (d : ℕ) [NeZero d] : 0 < sstarCloseBMixConst d :=
  (Classical.choose_spec (sstarClose_mixAnchor_unconditional d)).1

/-- The mixing anchor, at the named constant `sstarCloseBMixConst d`. -/
theorem sstarCloseBMixConst_anchor (d : ℕ) [NeZero d] :
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 → ∀ (P : ProbabilityMeasure (ShellSeq d)),
      ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
      ShellLawJ4 d P → ∀ (h n l : ℕ), h < n → n ≤ l →
        ∃ X : ShellSeq d → ℝ, Measurable X ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
              (sstarCloseBMixConst d * nu ^ (-(2 : ℝ)) *
                (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
          ∀ omega : ShellSeq d,
            MatLoewnerLE
              (sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
                (coefficientCutoff nu omega l).toCoeffField)
              (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                X omega • (1 : Mat d)) :=
  (Classical.choose_spec (sstarClose_mixAnchor_unconditional d)).2

/-- The localization anchor, at the named constant `sstarCloseCL d hd`. -/
theorem sstarCloseCL_anchor (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 → ∀ (P : ProbabilityMeasure (ShellSeq d)),
      ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
      ShellLawJ4 d P → ∀ (mm nn LL : ℕ), nn ≤ mm → mm ≤ LL →
        ∀ U : Book.Ch02.Domain d, (U : Set (Vec d)) ⊆ openCubeSet (originCube d (nn : ℤ)) →
          ∃ X : ShellSeq d → ℝ, Measurable X ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
                (sstarCloseCL d hd * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((mm - nn : ℕ) : ℝ)))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                  ((1 - X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega mm).toCoeffField)
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega LL).toCoeffField) ∧
                MatLoewnerLE
                  (sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega LL).toCoeffField)
                  ((1 + X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                    (coefficientCutoff nu omega mm).toCoeffField) :=
  (Classical.choose_spec (sstarClose_locAnchor_unconditional d hd)).2

/-- **The corrected `d`-only threshold constant.**  It dominates everything the
constant-first packaging needs the single constant `C` to dominate: the work
threshold `sstarCloseThrConst d`, the mixing anchor's constant
`sstarCloseBMixConst d`, the localization constant `sstarCloseCL d hd`
(via `γ₁ CL crude⁻¹`, which the annealing threshold `Ceta ≤ ν⁻¹L` forces), and
the quenched scalar constant `quenchedConst c`.  Its free variables are `d`,
`hd` and `c` only. -/
noncomputable def sstarCloseBThrConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) (c : ℝ) : ℝ :=
  max (max (100000000 + 16 * sstarCloseThrConst d) (sstarCloseBMixConst d))
    (max (quenchedConst c + 1)
      (max (16 * (IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd *
        (crudeLowerConst d)⁻¹) + 1) 1))

theorem hundred_million_le_sstarCloseBThrConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) (c : ℝ) :
    (100000000 : ℝ) ≤ sstarCloseBThrConst d hd c := by
  have h1 : (1 : ℝ) ≤ sstarCloseThrConst d := one_le_sstarCloseThrConst d
  refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_left _ _))
  linarith only [h1]

theorem one_le_sstarCloseBThrConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) (c : ℝ) :
    (1 : ℝ) ≤ sstarCloseBThrConst d hd c := by
  have h := hundred_million_le_sstarCloseBThrConst d hd c
  linarith only [h]

theorem sstarCloseBMixConst_le_BThrConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) (c : ℝ) :
    sstarCloseBMixConst d ≤ sstarCloseBThrConst d hd c :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem quenchedConst_le_BThrConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) (c : ℝ) :
    quenchedConst c ≤ sstarCloseBThrConst d hd c := by
  refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
  linarith only [show ((0 : ℝ)) ≤ 1 by norm_num]

theorem sixteen_mul_Ceta_le_BThrConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) (c : ℝ) :
    16 * (IndependentSums.gammaMomentConst 1 * sstarCloseCL d hd *
        (crudeLowerConst d)⁻¹) + 1 ≤ sstarCloseBThrConst d hd c :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)

/-! ## The quenched bracket from the single annealed residue -/

/-! ## The constant-first packaging -/

end SuperdiffusionCLT.Section3.Terms
