/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.NearAdditivityB
public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioC
public import SuperdiffusionCLT.Section4.LNaught.LogCompare
public import SuperdiffusionCLT.Section4.LNaught.Monotone
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5

/-!
# `sbHomogPair_of_homog`: `hHomogPair` from `hHomog` alone

`sbNear_goodNB`'s `hHomogPair` (`NearAdditivityD6.lean`) reads `p.homog.below`
"applied to the pair `(ell, n)`" with `n := sbNear_witness ell L`, at the
concrete witness the near-additivity argument fixes. The
`homogenization_below_cutoff` body itself (carried here as the hypothesis
`hHomog`, copied verbatim) is stated at a generic
`(L, m)` pair with its own threshold `lNaught C (C*M) ... ≤ L` — so applying
it at `(L', m') := (ell, n)` needs a threshold on `ell` at `hHomog`'s own
(opaque) witness constant `Chom`, not at the ambient `Cthresh`. This file
converts one into the other via `lNaught_mul_M_le` (`Section4/LNaught/
LogCompare.lean`) and `lNaught_mono_both` (`Section4/LNaught/Monotone.lean`,
which packages `lNaught_mono_const` with `lNaught_mono_M`), feeding `hHomog`'s
own `M`-slot the FIXED constant `401` (not the ambient `M`): since `hHomog`'s
conclusion carries no `M`-dependence at all, only its two hypotheses do, and
`401` is exactly enough to dominate the near-additivity gap
`ell - n ≤ 200 log L + 1` once `ell` is large (`sbNear_witness_gap_le`).

Once `hHomog` applies at `(ell, n)`, its conclusion's error term
`Chom * shom_ell^(-2) * (ell - n + Chom log(ell)^2) + Chom * n^(-3000)` is
shown `≤ 1/8` from an ell-dependent growth bound on `σ̄_ell` — read off
`sbIndep_absorption_le_eighth`'s (`IndependenceRatioC.lean`) own SECOND
conjunct at the ambient `Cthresh`, rearranged (`shom_ell^2 ≥
8 Cthresh M L^alpha log(L)^3`), plus `L^alpha ≥ 1`, `log(L) ≥ log(ell)`, and
`ell ≥ L/2` (`lNaught_absorbs`) — against a fixed numeric threshold on `C0`
depending only on `Chom` (never on `nu, cStar, K`). Splitting the resulting
`|A| + |B| ≤ 1/8` (both terms nonnegative) into `|A| ≤ 1/8` and `|B| ≤ 1/8`
gives the two printed conjuncts directly. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Two small self-contained log/sqrt bounds (private copies: the versions
in `Section4/LNaught/LogCompare.lean` are `private` to that file). -/

private lemma sbHP_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  set y := Real.sqrt x with hydef
  have hypos : 0 < y := Real.sqrt_pos.mpr hx
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hypos
  have hlogx_eq : Real.log x = 2 * Real.log y := by
    calc Real.log x = Real.log (y ^ 2) := by rw [hydef, Real.sq_sqrt hx.le]
      _ = 2 * Real.log y := by rw [Real.log_pow, Nat.cast_ofNat]
  rw [hlogx_eq]
  linarith only [hlogy]

private lemma sbHP_t_sqrt_le {t x : ℝ} (hx : 0 ≤ x) (hbound : t ^ 2 ≤ x) :
    t * Real.sqrt x ≤ x := by
  have hsqrt_ge : t ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hbound
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmul : t * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
    mul_le_mul_of_nonneg_right hsqrt_ge hsqrt_nonneg
  rwa [Real.mul_self_sqrt hx] at hmul

/-- **`sbHomogPair_of_homog`**: `hHomogPair` (`sbNear_goodNB`'s hypothesis,
`NearAdditivityD6.lean`) from the `homogenization_below_cutoff` body
(`hHomog`, copied verbatim) and `hd : 2 ≤ d` alone (the latter needed only to
invoke the root lower bound behind `sbIndep_absorption_le_eighth`). -/
theorem sbHomogPair_of_homog (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hHomog : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L m : ℕ,
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤
                  (L : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P m - 1| +
                  |sigmaBarInfinite nu L P * sigmaBarStarInvSeq nu L P m - 1| ≤
                C * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
                  C * (m : ℝ) ^ (-(3000 : ℝ))) :
    ∃ C2 C0 : ℝ, 1 ≤ C2 ∧ 1 ≤ C0 ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ Cthresh : ℝ, C0 ≤ Cthresh →
            ∀ L ell : ℕ, ell < L →
              SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
                (sigmaBarStarInvScalar nu ell P
                    (cubeSet (originCube d (sbNear_witness ell L : ℤ))) ≤
                  C2 * (sigmaBarInfinite nu ell P)⁻¹) ∧
                ((7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤
                  sigmaBarSeq nu ell P (sbNear_witness ell L)) := by
  obtain ⟨Chom, hChom1, hHomogBody⟩ := hHomog
  obtain ⟨CAbs0, hCAbs01, hAbsorbs⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_absorbs
  obtain ⟨CAE0, hCAE01, hAbsEighth⟩ := sbIndep_absorption_le_eighth hd
  have hChomnn : (0 : ℝ) ≤ Chom := le_trans zero_le_one hChom1
  have hK'1 : (1 : ℝ) ≤ Chom * 401 := by nlinarith only [hChom1]
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlogK'nn : (0 : ℝ) ≤ Real.log (Chom * 401) := Real.log_nonneg hK'1
  have hbaseK'pos : (0 : ℝ) < 1 + Real.log (Chom * 401) / Real.log 2 := by positivity
  have hpow12nn : (0 : ℝ) ≤ (1 + Real.log (Chom * 401) / Real.log 2) ^ (12 : ℝ) :=
    Real.rpow_nonneg hbaseK'pos.le _
  set Cmid : ℝ := Chom * (Chom * 401) * (1 + Real.log (Chom * 401) / Real.log 2) ^ (12 : ℝ)
    with hCmiddef
  have hCmidnn : (0 : ℝ) ≤ Cmid := by
    rw [hCmiddef]; positivity
  set C0 : ℝ := max 128 (max CAbs0 (max CAE0 (max Cmid
      (max (2 * (401 * Chom + Chom ^ 2)) (max 160801 (2 * Chom)))))) with hC0def
  have hC0_128 : (128 : ℝ) ≤ C0 := le_max_left _ _
  have hC0_CAbs0 : CAbs0 ≤ C0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC0_CAE0 : CAE0 ≤ C0 :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC0_Cmid : Cmid ≤ C0 :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hC0_termA : 2 * (401 * Chom + Chom ^ 2) ≤ C0 :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hC0_160801 : (160801 : ℝ) ≤ C0 :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
  have hC0_2Chom : 2 * Chom ≤ C0 :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _)
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))))
  have hC0_1 : (1 : ℝ) ≤ C0 := le_trans (by norm_num) hC0_128
  refine ⟨9 / 8, C0, by norm_num, hC0_1, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM Cthresh hCthresh
    L ell hlt hLnaught hscale
  have hCthresh128 : (128 : ℝ) ≤ Cthresh := le_trans hC0_128 hCthresh
  have hCthreshCAbs0 : CAbs0 ≤ Cthresh := le_trans hC0_CAbs0 hCthresh
  have hCthreshCAE0 : CAE0 ≤ Cthresh := le_trans hC0_CAE0 hCthresh
  have hCthreshCmid : Cmid ≤ Cthresh := le_trans hC0_Cmid hCthresh
  have hCthresh1 : (1 : ℝ) ≤ Cthresh := le_trans (by norm_num) hCthresh128
  have hellL : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlt.le
  have hLnaughtAtL :
      SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K ≤
        (L : ℝ) :=
    le_trans hLnaught hellL
  have hcStarpos := hJ5.cStar_pos
  have hcStar2 := hJ5.cStar_le_two
  have hKnn := hJ5.K_pos.le
  -- Step 1: `ell ≥ 16 * Cthresh ≥ 16 * C0` (`sbIndep_lNaught_ge_linear`).
  have hMC : Cthresh ≤ Cthresh * M := le_mul_of_one_le_right (le_trans zero_le_one hCthresh1) hM
  have hLinGe : 16 * Cthresh ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K :=
    sbIndep_lNaught_ge_linear hCthresh128 hMC hcStarpos hcStar2 hnu hnu1 hKnn hα0 hα1
  have hEll16C : 16 * Cthresh ≤ (ell : ℝ) := le_trans hLinGe hLnaught
  have hEll16C0 : 16 * C0 ≤ (ell : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hCthresh (by norm_num : (0 : ℝ) ≤ 16)) hEll16C
  have hEllBig : (2572816 : ℝ) ≤ (ell : ℝ) := by
    have h1 : (16 : ℝ) * 160801 ≤ 16 * C0 :=
      mul_le_mul_of_nonneg_left hC0_160801 (by norm_num : (0 : ℝ) ≤ 16)
    linarith only [h1, hEll16C0]
  have hellRpos : (0 : ℝ) < (ell : ℝ) := by linarith only [hEllBig]
  have hLRpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le hellRpos hellL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := le_trans (by linarith only [hEllBig] : (1 : ℝ) ≤ (ell : ℝ)) hellL
  -- Step 2: `L ≤ 2 * ell` (`lNaught_absorbs`, the same "crude absorption"
  -- pattern as `sbIndep_absorption_le_eighth`'s own Step 1).
  have hAbsorbsAtL := hAbsorbs Cthresh hCthreshCAbs0 (Cthresh * M)
    (le_trans hM (le_mul_of_one_le_left (le_trans zero_le_one hM) hCthresh1)) alpha hα0 hα1 cStar
    hcStarpos hcStar2 nu hnu hnu1 K hKnn L hLnaughtAtL
  have hML_le : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2 := by
    have heq : (Cthresh * M) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) =
        Cthresh * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    rw [heq] at hAbsorbsAtL
    have hMLnn : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
      have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
      have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
      positivity
    nlinarith only [hAbsorbsAtL, hCthresh1, hMLnn]
  have hell2L : (L : ℝ) / 2 ≤ (ell : ℝ) := by linarith only [hscale, hML_le]
  have hL2ell : (L : ℝ) ≤ 2 * (ell : ℝ) := by linarith only [hell2L]
  -- Step 3: `log ell ≥ 1` and `log L ≤ 2 log ell`.
  have he3 : Real.exp 1 < (3 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlogellgt1 : (1 : ℝ) < Real.log (ell : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1)
      (lt_of_lt_of_le he3 (by linarith only [hEllBig] : (3 : ℝ) ≤ (ell : ℝ)))
    rwa [Real.log_exp] at h
  have hlogellge1 : (1 : ℝ) ≤ Real.log (ell : ℝ) := hlogellgt1.le
  have hlogellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) := by linarith only [hlogellge1]
  have hlogL_le : Real.log (L : ℝ) ≤ Real.log 2 + Real.log (ell : ℝ) := by
    have h1 : Real.log (L : ℝ) ≤ Real.log (2 * (ell : ℝ)) := Real.log_le_log hLRpos hL2ell
    rwa [Real.log_mul (by norm_num) hellRpos.ne'] at h1
  have hlog2lt1 : Real.log (2 : ℝ) < 1 := by linarith only [Real.log_two_lt_d9]
  have hlogL_le2 : Real.log (L : ℝ) ≤ 2 * Real.log (ell : ℝ) := by
    linarith only [hlogL_le, hlog2lt1, hlogellge1]
  -- Step 4: `ell - n ≤ 401 log ell`, `n := sbNear_witness ell L`.
  set n : ℕ := sbNear_witness ell L with hndef
  have hgap : (ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1 := sbNear_witness_gap_le ell L
  have hnleell : n ≤ ell := sbNear_witness_le ell L
  have hgap2 : (ell : ℝ) - (n : ℝ) ≤ 401 * Real.log (ell : ℝ) := by
    linarith only [hgap, hlogL_le2, hlogellge1]
  -- Step 5: the ell-dependent growth bound `shom_ell² ≥ 8 * C0 * log(ell)³`,
  -- read off `sbIndep_absorption_le_eighth`'s second conjunct at `Cthresh`.
  have hAbsEighthAt := hAbsEighth Cthresh hCthreshCAE0 nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2
    hJ4 hJ5 alpha M hα0 hα1 hM L ell hlt.le hLnaught hscale
  obtain ⟨_hSigmaSq256, hAbsBound⟩ := hAbsEighthAt
  have hShomEllPos : (0 : ℝ) < sigmaBarInfinite nu ell P :=
    sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4
  have hShomEllSqPos : (0 : ℝ) < sigmaBarInfinite nu ell P ^ 2 := pow_pos hShomEllPos 2
  have hShomRpow : (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) =
      (sigmaBarInfinite nu ell P ^ 2)⁻¹ := by
    rw [Real.rpow_neg hShomEllPos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hterm2nn : (0 : ℝ) ≤ Cthresh * (L : ℝ) ^ (-(99 : ℝ)) :=
    mul_nonneg (le_trans zero_le_one hCthresh1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hterm1le : Cthresh * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤ 1 / 8 := by linarith only [hAbsBound, hterm2nn]
  rw [hShomRpow] at hterm1le
  have heqterm1 : Cthresh * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P ^ 2)⁻¹ *
      Real.log (L : ℝ) ^ (3 : ℝ) =
      (Cthresh * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) *
        (sigmaBarInfinite nu ell P ^ 2)⁻¹ := by ring
  rw [heqterm1] at hterm1le
  have hstep : (Cthresh * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) *
      (sigmaBarInfinite nu ell P ^ 2)⁻¹ * sigmaBarInfinite nu ell P ^ 2 ≤
      (1 / 8 : ℝ) * sigmaBarInfinite nu ell P ^ 2 :=
    mul_le_mul_of_nonneg_right hterm1le hShomEllSqPos.le
  have heqcancel : (Cthresh * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) *
      (sigmaBarInfinite nu ell P ^ 2)⁻¹ * sigmaBarInfinite nu ell P ^ 2 =
      Cthresh * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    rw [mul_assoc, inv_mul_cancel₀ hShomEllSqPos.ne', mul_one]
  rw [heqcancel] at hstep
  have hGrowth : 8 * (Cthresh * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
      sigmaBarInfinite nu ell P ^ 2 := by linarith only [hstep]
  have hLalphage1 : (1 : ℝ) ≤ (L : ℝ) ^ alpha := by
    calc (1 : ℝ) = (L : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (L : ℝ) ^ alpha := Real.rpow_le_rpow_of_exponent_le hL1 hα0
  have hlog3ellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogellnn _
  have hlog3Lge : Real.log (ell : ℝ) ^ (3 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := by
    have hlogLgeell : Real.log (ell : ℝ) ≤ Real.log (L : ℝ) := Real.log_le_log hellRpos hellL
    exact Real.rpow_le_rpow hlogellnn hlogLgeell (by norm_num)
  have hML_alpha_ge1 : (1 : ℝ) ≤ M * (L : ℝ) ^ alpha := by
    have h := mul_le_mul hM hLalphage1 (by norm_num) (le_trans zero_le_one hM)
    linarith only [h]
  have hCombine : C0 * Real.log (ell : ℝ) ^ (3 : ℝ) ≤
      Cthresh * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have hstep1 : C0 * Real.log (ell : ℝ) ^ (3 : ℝ) ≤ Cthresh * Real.log (ell : ℝ) ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_right hCthresh hlog3ellnn
    have hstep2 : Cthresh * Real.log (ell : ℝ) ^ (3 : ℝ) ≤ Cthresh * Real.log (L : ℝ) ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog3Lge (le_trans zero_le_one hCthresh1)
    have hlogL3nn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := le_trans hlog3ellnn hlog3Lge
    have hstep3 : Cthresh * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        Cthresh * (M * (L : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hML_alpha_ge1 (le_trans zero_le_one hCthresh1)
      have h2 := mul_le_mul_of_nonneg_right h hlogL3nn
      calc Cthresh * Real.log (L : ℝ) ^ (3 : ℝ)
          = Cthresh * 1 * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
        _ ≤ Cthresh * (M * (L : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) := h2
    calc C0 * Real.log (ell : ℝ) ^ (3 : ℝ) ≤ Cthresh * Real.log (ell : ℝ) ^ (3 : ℝ) := hstep1
      _ ≤ Cthresh * Real.log (L : ℝ) ^ (3 : ℝ) := hstep2
      _ ≤ Cthresh * (M * (L : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) := hstep3
      _ = Cthresh * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
  have hGrowth2 : 8 * C0 * Real.log (ell : ℝ) ^ (3 : ℝ) ≤ sigmaBarInfinite nu ell P ^ 2 := by
    have h8 := mul_le_mul_of_nonneg_left hCombine (by norm_num : (0 : ℝ) ≤ 8)
    have heq : 8 * (C0 * Real.log (ell : ℝ) ^ (3 : ℝ)) = 8 * C0 * Real.log (ell : ℝ) ^ (3 : ℝ) := by
      ring
    rw [heq] at h8
    linarith only [h8, hGrowth]
  -- Step 6: `n ≥ ell / 2` and `n ≥ 16 * Chom` (via `401 log ell ≤ ell / 2`,
  -- an elementary `log`-vs-`sqrt` bound, needing no relation to `Cthresh`).
  have hlog_le_sqrt : Real.log (ell : ℝ) ≤ 2 * Real.sqrt (ell : ℝ) := sbHP_log_le_two_sqrt hellRpos
  have h1604sq : (1604 : ℝ) ^ 2 ≤ (ell : ℝ) := by
    have : (1604 : ℝ) ^ 2 = 2572816 := by norm_num
    linarith only [hEllBig, this.le, this.ge]
  have h1604sqrt : (1604 : ℝ) * Real.sqrt (ell : ℝ) ≤ (ell : ℝ) :=
    sbHP_t_sqrt_le hellRpos.le h1604sq
  have h401log_le : 401 * Real.log (ell : ℝ) ≤ (ell : ℝ) / 2 := by
    linarith only [hlog_le_sqrt, h1604sqrt]
  have hn_ge_half : (ell : ℝ) / 2 ≤ (n : ℝ) := by linarith only [hgap2, h401log_le]
  have hn_ge_16Chom : (16 : ℝ) * Chom ≤ (n : ℝ) := by
    have h3 : 16 * (2 * Chom) ≤ 16 * C0 :=
      mul_le_mul_of_nonneg_left hC0_2Chom (by norm_num)
    linarith only [h3, hEll16C0, hn_ge_half]
  -- Step 7: the second error term, `Chom * n^(-3000) ≤ 1/16`.
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_ge_16Chom, hChom1]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith only [hn_ge_16Chom, hChom1]
  have hn3000ge_n : (n : ℝ) ≤ (n : ℝ) ^ (3000 : ℝ) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (3000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hnrpow3000pos : (0 : ℝ) < (n : ℝ) ^ (3000 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have h16Chom_le_n3000 : 16 * Chom ≤ (n : ℝ) ^ (3000 : ℝ) := le_trans hn_ge_16Chom hn3000ge_n
  have hterm2final : Chom * (n : ℝ) ^ (-(3000 : ℝ)) ≤ 1 / 16 := by
    rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, div_le_iff₀ hnrpow3000pos]
    linarith only [h16Chom_le_n3000]
  -- Step 8: the first error term, `Chom * shom_ell^(-2) * max 0 X ≤ 1/16`.
  have hXnn : (0 : ℝ) ≤ (ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (ell : ℝ) - (n : ℝ) := by
      have : (n : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hnleell
      linarith only [this]
    have hlog2nn : (0 : ℝ) ≤ Real.log (ell : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg hlogellnn _
    have h2 : (0 : ℝ) ≤ Chom * Real.log (ell : ℝ) ^ (2 : ℝ) := mul_nonneg hChomnn hlog2nn
    linarith only [h1, h2]
  have hmax0eq : max (0 : ℝ) ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ)) =
      (ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ) := max_eq_right hXnn
  have hlogellcube : Real.log (ell : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := by
    calc Real.log (ell : ℝ) = Real.log (ell : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlogellge1 (by norm_num)
  have hlogellsqcube : Real.log (ell : ℝ) ^ (2 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogellge1 (by norm_num)
  have hChomXle : Chom * ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ)) ≤
      (401 * Chom + Chom ^ 2) * Real.log (ell : ℝ) ^ (3 : ℝ) := by
    have hexpand : Chom * ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ)) =
        Chom * ((ell : ℝ) - (n : ℝ)) + Chom ^ 2 * Real.log (ell : ℝ) ^ (2 : ℝ) := by ring
    rw [hexpand]
    have hpart1 : Chom * ((ell : ℝ) - (n : ℝ)) ≤ 401 * Chom * Real.log (ell : ℝ) ^ (3 : ℝ) := by
      have hstepa : Chom * ((ell : ℝ) - (n : ℝ)) ≤ Chom * (401 * Real.log (ell : ℝ)) :=
        mul_le_mul_of_nonneg_left hgap2 hChomnn
      have h401 : (401 : ℝ) * Real.log (ell : ℝ) ≤ 401 * Real.log (ell : ℝ) ^ (3 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogellcube (by norm_num)
      have hstepb : Chom * (401 * Real.log (ell : ℝ)) ≤ Chom * (401 * Real.log (ell : ℝ) ^ (3 : ℝ)) :=
        mul_le_mul_of_nonneg_left h401 hChomnn
      calc Chom * ((ell : ℝ) - (n : ℝ)) ≤ Chom * (401 * Real.log (ell : ℝ)) := hstepa
        _ ≤ Chom * (401 * Real.log (ell : ℝ) ^ (3 : ℝ)) := hstepb
        _ = 401 * Chom * Real.log (ell : ℝ) ^ (3 : ℝ) := by ring
    have hpart2 : Chom ^ 2 * Real.log (ell : ℝ) ^ (2 : ℝ) ≤ Chom ^ 2 * Real.log (ell : ℝ) ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogellsqcube (by positivity)
    have heq : (401 * Chom + Chom ^ 2) * Real.log (ell : ℝ) ^ (3 : ℝ) =
        401 * Chom * Real.log (ell : ℝ) ^ (3 : ℝ) + Chom ^ 2 * Real.log (ell : ℝ) ^ (3 : ℝ) := by
      ring
    rw [heq]
    linarith only [hpart1, hpart2]
  have hC0half : 401 * Chom + Chom ^ 2 ≤ C0 / 2 := by linarith only [hC0_termA]
  have hChomXle2 : Chom * ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ)) ≤
      (C0 / 2) * Real.log (ell : ℝ) ^ (3 : ℝ) :=
    le_trans hChomXle (mul_le_mul_of_nonneg_right hC0half hlog3ellnn)
  have hterm1final : Chom * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ)) ≤ 1 / 16 := by
    rw [hShomRpow]
    rw [show Chom * (sigmaBarInfinite nu ell P ^ 2)⁻¹ *
        ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ)) =
        (Chom * ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ))) *
          (sigmaBarInfinite nu ell P ^ 2)⁻¹ from by ring]
    rw [← div_eq_mul_inv, div_le_iff₀ hShomEllSqPos]
    have h16 : (1 / 16 : ℝ) * (8 * C0 * Real.log (ell : ℝ) ^ (3 : ℝ)) ≤
        (1 / 16 : ℝ) * sigmaBarInfinite nu ell P ^ 2 :=
      mul_le_mul_of_nonneg_left hGrowth2 (by norm_num)
    have heq2 : (1 / 16 : ℝ) * (8 * C0 * Real.log (ell : ℝ) ^ (3 : ℝ)) =
        (C0 / 2) * Real.log (ell : ℝ) ^ (3 : ℝ) := by ring
    rw [heq2] at h16
    linarith only [hChomXle2, h16]
  -- Step 9: invoke `hHomog` at `(L', m') := (ell, n)`, `M'' := 401` (a fixed
  -- constant, unrelated to the ambient `M`) — the threshold at `Chom` via
  -- `lNaught_mul_M_le` + `lNaught_mono_both`, the scale gap via Step 4.
  have hMulM : SuperdiffusionCLT.Frozen.Section4.lNaught Chom (Chom * 401) alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught Cmid 1 alpha cStar nu K := by
    have h := SuperdiffusionCLT.Section4.LNaught.lNaught_mul_M_le Chom 1 alpha cStar nu K
      (Chom * 401) hChomnn zero_le_one hα1 hcStarpos hnu hKnn hK'1
    rwa [mul_one] at h
  have hCthreshM1 : (1 : ℝ) ≤ Cthresh * M := by nlinarith only [hCthresh1, hM]
  have hMono : SuperdiffusionCLT.Frozen.Section4.lNaught Cmid 1 alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh (Cthresh * M) alpha cStar nu K :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both hCmidnn hCthreshCmid zero_le_one
      hCthreshM1 hKnn hcStarpos hnu hα1
  have hH1 : SuperdiffusionCLT.Frozen.Section4.lNaught Chom (Chom * 401) alpha cStar nu K ≤
      (ell : ℝ) :=
    le_trans hMulM (le_trans hMono hLnaught)
  have hellalphage1 : (1 : ℝ) ≤ (ell : ℝ) ^ alpha := by
    calc (1 : ℝ) = (ell : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (ell : ℝ) ^ alpha := Real.rpow_le_rpow_of_exponent_le (by linarith only [hEllBig]) hα0
  have hH2 : (ell : ℝ) - 401 * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) := by
    have hstepA : 401 * Real.log (ell : ℝ) ≤ 401 * Real.log (ell : ℝ) ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogellcube (by norm_num)
    have hstepB : 401 * Real.log (ell : ℝ) ^ (3 : ℝ) ≤
        401 * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hellalphage1 hlog3ellnn
      calc 401 * Real.log (ell : ℝ) ^ (3 : ℝ) = 401 * (1 * Real.log (ell : ℝ) ^ (3 : ℝ)) := by ring
        _ ≤ 401 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
        _ = 401 * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by ring
    linarith only [hgap2, hstepA, hstepB]
  have hHomogAt := hHomogBody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha 401
    hα0 hα1 (by norm_num) ell n hH1 hH2
  rw [hmax0eq] at hHomogAt
  have hRHSle : Chom * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      ((ell : ℝ) - (n : ℝ) + Chom * Real.log (ell : ℝ) ^ (2 : ℝ)) +
      Chom * (n : ℝ) ^ (-(3000 : ℝ)) ≤ 1 / 8 := by linarith only [hterm1final, hterm2final]
  have hHomogAt' := le_trans hHomogAt hRHSle
  have hAnn : (0 : ℝ) ≤ |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| :=
    abs_nonneg _
  have hBnn : (0 : ℝ) ≤ |sigmaBarInfinite nu ell P * sigmaBarStarInvSeq nu ell P n - 1| :=
    abs_nonneg _
  have hAle : |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| ≤ 1 / 8 := by
    linarith only [hHomogAt', hBnn]
  have hBle : |sigmaBarInfinite nu ell P * sigmaBarStarInvSeq nu ell P n - 1| ≤ 1 / 8 := by
    linarith only [hHomogAt', hAnn]
  have hAge : -(1 / 8 : ℝ) ≤ (sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1 :=
    (abs_le.mp hAle).1
  have hSeqGe : (7 / 8 : ℝ) * sigmaBarInfinite nu ell P ≤ sigmaBarSeq nu ell P n := by
    have h1 : (7 / 8 : ℝ) ≤ (sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n := by
      linarith only [hAge]
    have h2 := mul_le_mul_of_nonneg_left h1 hShomEllPos.le
    rw [← mul_assoc, mul_inv_cancel₀ hShomEllPos.ne', one_mul] at h2
    linarith only [h2]
  have hBleUp : sigmaBarInfinite nu ell P * sigmaBarStarInvSeq nu ell P n - 1 ≤ 1 / 8 :=
    (abs_le.mp hBle).2
  have hStarLe : sigmaBarStarInvSeq nu ell P n ≤ (9 / 8 : ℝ) * (sigmaBarInfinite nu ell P)⁻¹ := by
    have h1 : sigmaBarInfinite nu ell P * sigmaBarStarInvSeq nu ell P n ≤ 9 / 8 := by
      linarith only [hBleUp]
    have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hShomEllPos.le)
    rw [← mul_assoc, inv_mul_cancel₀ hShomEllPos.ne', one_mul] at h3
    linarith only [h3]
  exact ⟨hStarLe, hSeqGe⟩

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
