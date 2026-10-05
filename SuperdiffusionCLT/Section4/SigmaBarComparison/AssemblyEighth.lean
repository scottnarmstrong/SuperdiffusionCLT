/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyMain
public import SuperdiffusionCLT.Section4.LNaught.SstarLowerB
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# The `#homog-below-bound` node's own `≤ 1/8` bound, from `hHomog` alone

This is the node `l.shomm.vs.shomell#homog-below-bound`: applying `p.homog.below`
(`homogenization_below_cutoff`, carried as a hypothesis `hHomog`) at the pairs `(L,n)` and
`(ell,n)` and summing.

`sbAsm_hb_eighth` proves this node's conclusion — the sum bound `≤ 1/8` at a
GIVEN shared witness `n` (with `n`'s own bookkeeping conjuncts `n ≤ ell`,
`(ell:ℝ) - (n:ℝ) ≤ 200 log L + 1`, matching the conclusion of `sbIndep_mainB`,
`IndependenceRatioF.lean`) — from `hHomog` alone, no other hypothesis: the
`M`-inflation mechanism (`lNaught_sstar_lower`,
`c = c_r²/2^10`) supplies the missing `e.L.vs.Lnaught` ingredient.

## The two residual terms, handled uniformly

`hHomog`'s own error bound at a pair `(X,m)` is
`C_H shom_X^{-2} max(0, X-m+C_H log²X) + C_H m^{-3000}`. Two facts make both
pieces small once the `M`-argument fed to `hHomog` is chosen `≥ 1`:

* `X-n+C_H log²X ≤ (1+C_H) * M_X * X^α log³X` (elementary: `X-n ≤ M_X X^α
  log³X` is exactly the scale condition `hHomog` needs, and `log²X ≤ M_X X^α
  log³X` from `log X ≥ 1` (`X ≥ 3`) and `M_X X^α ≥ 1`), so the first term
  reduces to controlling `M_X X^α log³X / shom_X²`, which `lNaught_sstar_lower`
  (at an inflated `M`-argument `K'' * M_X`, `K''` chosen once from `C_H`)
  makes `≤ 1/(32 C_H (1+C_H))`.
* `n ≥ ell/2` (from `ell - n ≤ 200 log L + 1 ≤ 3216 ell^α log³ell` — the tail
  bound `sbAsm_tail_le` plus the ratio bounds `sbAsm_ratio_alpha_le`/
  `sbAsm_ratio_log_le` at `ell ≥ L/2` — `≤ ell/2` via `lNaught_absorbs` at
  a FIXED multiple `3216` of OUR own outer constant), and `ell ≥ 64 C_H`
  (from `hHomog`'s own threshold at `X := ell` and the constant-`C_H`-agnostic
  growth fact `sbAsm_lNaught_ge_C_of_M_ge`), giving `n ≥ 32 C_H`, which
  dominates `C_H n^{-3000} ≤ 1/32` via `n ≤ n^{3000}` (`n ≥ 1`).

All witnesses (`C0star`, `c` from `lNaught_sstar_lower`; `CA0` from
`lNaught_absorbs`) are FIXED reals obtained once `hHomog`'s own `C_H` is
known; the outer constant `C` this theorem produces is a `max` dominating
every one of them plus `C_H` itself, exactly mirroring the pattern already
used for `sbIndep_absorption_le_eighth` (`IndependenceRatioC.lean`), applied
here to `hHomog` in place of `hIndep`.
-/

@[expose] public section

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open SuperdiffusionCLT.Section4.LNaught (lNaught_mono_const lNaught_mono_M)

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

noncomputable section

/-- **The `#homog-below-bound` node**, unconditional given `hHomog` alone. -/
theorem sbAsm_hb_eighth (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hHomog : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L m : ℕ,
              lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P m - 1| +
                  |sigmaBarInfinite nu L P * sigmaBarStarInvSeq nu L P m - 1| ≤
                C * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                    max 0 ((L : ℝ) - (m : ℝ) + C * Real.log (L : ℝ) ^ (2 : ℝ)) +
                  C * (m : ℝ) ^ (-(3000 : ℝ))) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              lNaught C (C * M) alpha cStar nu K ≤ (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              ∀ n : ℕ, n ≤ ell → (ell : ℝ) - (n : ℝ) ≤ 200 * Real.log (L : ℝ) + 1 →
                |(sigmaBarInfinite nu L P)⁻¹ * sigmaBarSeq nu L P n - 1| +
                    |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarSeq nu ell P n - 1| ≤
                  (1 : ℝ) / 8 := by
  obtain ⟨C_H, hCH1, hHomogBody⟩ := hHomog
  obtain ⟨C0star, hC0star1, c, hcpos, hSstarLower⟩ :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower d hd
  obtain ⟨CA0, hCA01, hAbsorbs⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_absorbs
  have hCHpos : (0 : ℝ) < C_H := lt_of_lt_of_le one_pos hCH1
  -- Fixed constants, computed once `C_H`, `c`, `C0star`, `CA0` are known.
  set K'' : ℝ := 32 * C_H * (1 + C_H) / c + 1 with hK''def
  have hK''1 : (1 : ℝ) ≤ K'' := by
    have h0 : (0 : ℝ) ≤ 32 * C_H * (1 + C_H) / c := by positivity
    rw [hK''def]; linarith only [h0]
  have hK''pos : (0 : ℝ) < K'' := lt_of_lt_of_le one_pos hK''1
  have hcK''big : 32 * C_H * (1 + C_H) ≤ c * K'' := by
    have heq : c * (32 * C_H * (1 + C_H) / c) = 32 * C_H * (1 + C_H) := by
      field_simp
    have hmono : c * (32 * C_H * (1 + C_H) / c) ≤ c * K'' := by
      apply mul_le_mul_of_nonneg_left _ hcpos.le
      rw [hK''def]; linarith only []
    linarith only [heq, hmono]
  set MXell : ℝ := C_H * sbAsmGrowthB + 3216 with hMXelldef
  have hsbAsmGrowthBpos : (0 : ℝ) < sbAsmGrowthB := by
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hpow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
    unfold sbAsmGrowthB; positivity
  have hMXell1 : (1 : ℝ) ≤ MXell := by
    have h0 : (0 : ℝ) ≤ C_H * sbAsmGrowthB := by positivity
    rw [hMXelldef]; linarith only [h0]
  set K'ratioL : ℝ := K'' * 202 with hK'ratioLdef
  have hK'ratioL1 : (1 : ℝ) ≤ K'ratioL := by
    rw [hK'ratioLdef]
    calc (1 : ℝ) ≤ K'' := hK''1
      _ ≤ K'' * 202 := le_mul_of_one_le_right hK''pos.le (by norm_num)
  set logfacL : ℝ := (1 + Real.log (202 : ℝ) / Real.log 2) ^ (12 : ℝ) with hlogfacLdef
  set logfacRatioL : ℝ := (1 + Real.log K'ratioL / Real.log 2) ^ (12 : ℝ) with hlogfacRatioLdef
  have hlogfacLnn : (0 : ℝ) ≤ logfacL := by
    rw [hlogfacLdef]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog202nn : (0 : ℝ) ≤ Real.log (202 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  have hlogfacRatioLnn : (0 : ℝ) ≤ logfacRatioL := by
    rw [hlogfacRatioLdef]
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlogK'nn : (0 : ℝ) ≤ Real.log K'ratioL := Real.log_nonneg hK'ratioL1
    positivity
  -- Our own outer constant `C`.
  set C : ℝ := max 1 (max C_H (max (C_H * 202 * logfacL) (max (C_H * MXell)
      (max C0star (max CA0 (max (C0star * K'ratioL * logfacRatioL)
        (max (K'' * MXell) (CA0 * 3216)))))))) with hCdef
  refine ⟨C, le_max_left _ _, ?_⟩
  intro nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L ell hellL
    hLnaught hscale n hNell hGap
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hCH_C : C_H ≤ C := le_max_of_le_right (le_max_left _ _)
  have hCHK'Llogfac_C : C_H * 202 * logfacL ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCHMXell_C : C_H * MXell ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hC0star_C : C0star ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  have hCA0_C : CA0 ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))
  have hC0starK'ratiologfac_C : C0star * K'ratioL * logfacRatioL ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
  have hK''MXell_C : K'' * MXell ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
  have hCA03216_C : CA0 * 3216 ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))
  have hcStar2 := hJ5.cStar_le_two
  have hcStarpos := hJ5.cStar_pos
  have hKnn := hJ5.K_pos.le
  have hellLR : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hellL
  have hLnaughtAtL : lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) := le_trans hLnaught hellLR
  -- `ell ≥ L/2`, via `lNaught_absorbs` at OUR `(C, C*M)`.
  have hCM1 : (1 : ℝ) ≤ C * M := le_trans hM (le_mul_of_one_le_left (le_trans zero_le_one hM) hC1)
  have hAbsorbAtL := hAbsorbs C hCA0_C (C * M) hCM1 alpha hα0 hα1 cStar hcStarpos hcStar2 nu hnu
    hnu1 K hKnn L hLnaughtAtL
  have hML2 : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2 := by
    have heq : C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) =
        C * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    rw [heq] at hAbsorbAtL
    have hMLnn : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
      have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
      have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
      positivity
    nlinarith only [hAbsorbAtL, hC1, hMLnn]
  have hL2ell : (L : ℝ) ≤ 2 * (ell : ℝ) := by linarith only [hscale, hML2]
  -- `ell ≥ 64 C_H`, via `hHomog`'s own threshold at `X := ell`, `M_X := MXell`.
  have hThreshHomogEll : lNaught C_H (C_H * MXell) alpha cStar nu K ≤ (ell : ℝ) :=
    (sbAsm_inflate_fixed (C0 := C_H) (Mfix := C_H * MXell) (C := C) (M := M)
      hCHpos.le (by positivity) hM hC1 hα1 hcStarpos hnu hKnn hCH_C hCHMXell_C).trans hLnaught
  have hsbAsmGrowthB_le_MXell : sbAsmGrowthB ≤ MXell := by
    rw [hMXelldef]
    nlinarith only [hCH1, hsbAsmGrowthBpos]
  have hCHMXellGe : C_H * sbAsmGrowthB ≤ C_H * MXell :=
    mul_le_mul_of_nonneg_left hsbAsmGrowthB_le_MXell hCHpos.le
  have hEll64CH : (64 : ℝ) * C_H ≤ (ell : ℝ) :=
    le_trans (sbAsm_lNaught_ge_C_of_M_ge (C := C_H) (M := C_H * MXell) hCH1 hCHMXellGe
        hcStarpos hcStar2 hnu hnu1 hKnn hα0 hα1)
      hThreshHomogEll
  have hell64 : (64 : ℝ) ≤ (ell : ℝ) := by nlinarith only [hEll64CH, hCH1]
  have hell1nat : (1 : ℕ) ≤ ell := by
    have : (1 : ℝ) ≤ (ell : ℝ) := by linarith only [hell64]
    exact_mod_cast this
  have hL64 : (64 : ℝ) ≤ (L : ℝ) := le_trans hell64 hellLR
  have hL4nat : (4 : ℕ) ≤ L := by
    have : (4 : ℝ) ≤ (L : ℝ) := by linarith only [hL64]
    exact_mod_cast this
  have hL3nat : (3 : ℕ) ≤ L := le_trans (by norm_num) hL4nat
  have hell3nat : (3 : ℕ) ≤ ell := by
    have : (3 : ℝ) ≤ (ell : ℝ) := by linarith only [hell64]
    exact_mod_cast this
  -- `n ≥ ell / 2`, via the tail bound, the ratio bounds, and `lNaught_absorbs`
  -- at a fixed multiple `3216` of OUR own outer constant.
  have hTailL : 200 * Real.log (L : ℝ) + 1 ≤ 201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
    sbAsm_tail_le hL3nat hα0
  have hRatioAlpha : (L : ℝ) ^ alpha ≤ 2 * (ell : ℝ) ^ alpha :=
    sbAsm_ratio_alpha_le hell1nat hellL hL2ell hα0 hα1
  have hRatioLog : Real.log (L : ℝ) ^ (3 : ℝ) ≤ 8 * Real.log (ell : ℝ) ^ (3 : ℝ) :=
    sbAsm_ratio_log_le hL4nat hL2ell
  have hlog3Lnn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
    Real.rpow_nonneg (Real.log_natCast_nonneg L) _
  have hellalphann : (0 : ℝ) ≤ (ell : ℝ) ^ alpha := Real.rpow_nonneg (by linarith only [hell64]) _
  have hTailToEll : 200 * Real.log (L : ℝ) + 1 ≤ 3216 * ((ell : ℝ) ^ alpha *
      Real.log (ell : ℝ) ^ (3 : ℝ)) := by
    have hstep1 : 201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        201 * (2 * (ell : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have h201 : (0 : ℝ) ≤ 201 * Real.log (L : ℝ) ^ (3 : ℝ) := by positivity
      nlinarith only [hRatioAlpha, h201]
    have hstep2 : 201 * (2 * (ell : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        201 * (2 * (ell : ℝ) ^ alpha) * (8 * Real.log (ell : ℝ) ^ (3 : ℝ)) := by
      have h0 : (0 : ℝ) ≤ 201 * (2 * (ell : ℝ) ^ alpha) := by positivity
      nlinarith only [hRatioLog, h0]
    nlinarith only [hTailL, hstep1, hstep2]
  have hThreshAbsorbEll : lNaught CA0 (CA0 * 3216) alpha cStar nu K ≤ (ell : ℝ) :=
    (sbAsm_inflate_fixed (C0 := CA0) (Mfix := CA0 * 3216) (C := C) (M := M)
      (le_trans zero_le_one hCA01) (by positivity) hM hC1 hα1 hcStarpos hnu hKnn hCA0_C
      hCA03216_C).trans hLnaught
  have hAbsorbEll := hAbsorbs CA0 le_rfl (CA0 * 3216) (by nlinarith only [hCA01])
    alpha hα0 hα1 cStar hcStarpos hcStar2 nu hnu hnu1 K hKnn ell hThreshAbsorbEll
  have hEllHalfBound : 3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) ≤
      (ell : ℝ) / 2 := by
    have heq : CA0 * 3216 * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) =
        CA0 * (3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) := by ring
    rw [heq] at hAbsorbEll
    have hnn : (0 : ℝ) ≤ 3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by positivity
    nlinarith only [hAbsorbEll, hCA01, hnn]
  have hNEllHalf : (ell : ℝ) / 2 ≤ (n : ℝ) := by linarith only [hGap, hTailToEll, hEllHalfBound]
  have hN32CH : (32 : ℝ) * C_H ≤ (n : ℝ) := by linarith only [hNEllHalf, hEll64CH]
  -- The generic per-`X` bound: applying `hHomog` at `(X,n)` and controlling
  -- both residual terms by `1/32` each.
  have hGeneric : ∀ (X : ℕ) (M_X : ℝ), 1 ≤ M_X →
      (X : ℝ) - M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) →
      3 ≤ X →
      lNaught C_H (C_H * M_X) alpha cStar nu K ≤ (X : ℝ) →
      M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ) * (32 * C_H * (1 + C_H)) ≤
        (sigmaBarInfinite nu X P) ^ 2 →
      |(sigmaBarInfinite nu X P)⁻¹ * sigmaBarSeq nu X P n - 1| ≤ (1 / 16 : ℝ) := by
    intro X M_X hMX1 hXGap hX3 hXThresh hRatio
    have hX3R : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
    have hXRpos : (0 : ℝ) < (X : ℝ) := by linarith only [hX3R]
    have hSXpos : (0 : ℝ) < sigmaBarInfinite nu X P := sigmaBarInfinite_pos hnu X hPrefix hJ2 hJ3 hJ4
    have hHomogAtXn := hHomogBody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M_X
      hα0 hα1 hMX1 X n hXThresh hXGap
    have hlog3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      linarith only [Real.exp_one_lt_d9]
    have hlogXgt1 : (1 : ℝ) < Real.log (X : ℝ) :=
      lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) hX3R)
    have hlogXpos : (0 : ℝ) < Real.log (X : ℝ) := by linarith only [hlogXgt1]
    have hXalpha1 : (1 : ℝ) ≤ (X : ℝ) ^ alpha :=
      Real.one_le_rpow (by linarith only [hX3R]) hα0
    have hlogcube_eq : Real.log (X : ℝ) ^ (3 : ℝ) =
        Real.log (X : ℝ) ^ (2 : ℝ) * Real.log (X : ℝ) := by
      have h : Real.log (X : ℝ) ^ ((2 : ℝ) + (1 : ℝ)) =
          Real.log (X : ℝ) ^ (2 : ℝ) * Real.log (X : ℝ) ^ (1 : ℝ) := Real.rpow_add hlogXpos 2 1
      rw [Real.rpow_one] at h
      rwa [show (2 : ℝ) + (1 : ℝ) = (3 : ℝ) by norm_num] at h
    have hlog2Xnn : (0 : ℝ) ≤ Real.log (X : ℝ) ^ (2 : ℝ) := Real.rpow_nonneg hlogXpos.le _
    have hlog3Xnn : (0 : ℝ) ≤ Real.log (X : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogXpos.le _
    have hlog2_le_log3 : Real.log (X : ℝ) ^ (2 : ℝ) ≤ Real.log (X : ℝ) ^ (3 : ℝ) := by
      rw [hlogcube_eq]
      have hmul := mul_le_mul_of_nonneg_left hlogXgt1.le hlog2Xnn
      rw [mul_one] at hmul
      linarith only [hmul]
    have hMXXalpha1 : (1 : ℝ) ≤ M_X * (X : ℝ) ^ alpha := by nlinarith only [hMX1, hXalpha1]
    have hB : Real.log (X : ℝ) ^ (2 : ℝ) ≤
        M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ) := by
      nlinarith only [hMXXalpha1, hlog3Xnn, hlog2_le_log3]
    have hY : (X : ℝ) - (n : ℝ) + C_H * Real.log (X : ℝ) ^ (2 : ℝ) ≤
        (1 + C_H) * (M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ)) := by
      nlinarith only [hXGap, hB, hCHpos]
    have hMXXalphalog3nn : (0 : ℝ) ≤ M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ) := by
      have hXalphann : (0 : ℝ) ≤ (X : ℝ) ^ alpha := le_trans zero_le_one hXalpha1
      have hMXnn : (0 : ℝ) ≤ M_X := le_trans zero_le_one hMX1
      positivity
    have hMaxY : max (0 : ℝ) ((X : ℝ) - (n : ℝ) + C_H * Real.log (X : ℝ) ^ (2 : ℝ)) ≤
        (1 + C_H) * (M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ)) :=
      max_le (by nlinarith only [hMXXalphalog3nn, hCHpos]) hY
    have hrpow2 : (sigmaBarInfinite nu X P) ^ (2 : ℝ) = (sigmaBarInfinite nu X P) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hXNegRpow : (sigmaBarInfinite nu X P) ^ (-(2 : ℝ)) =
        ((sigmaBarInfinite nu X P) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hSXpos.le, hrpow2]
    have hSXSqPos : (0 : ℝ) < (sigmaBarInfinite nu X P) ^ 2 := pow_pos hSXpos 2
    have hFirstTermBound : C_H * (sigmaBarInfinite nu X P) ^ (-(2 : ℝ)) *
        max (0 : ℝ) ((X : ℝ) - (n : ℝ) + C_H * Real.log (X : ℝ) ^ (2 : ℝ)) ≤ (1 / 32 : ℝ) := by
      rw [hXNegRpow]
      have hstep1 : C_H * ((sigmaBarInfinite nu X P) ^ 2)⁻¹ *
          max (0 : ℝ) ((X : ℝ) - (n : ℝ) + C_H * Real.log (X : ℝ) ^ (2 : ℝ)) ≤
          C_H * ((sigmaBarInfinite nu X P) ^ 2)⁻¹ *
            ((1 + C_H) * (M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ))) := by
        have hCoefnn : (0 : ℝ) ≤ C_H * ((sigmaBarInfinite nu X P) ^ 2)⁻¹ := by positivity
        exact mul_le_mul_of_nonneg_left hMaxY hCoefnn
      have hstep2 : C_H * ((sigmaBarInfinite nu X P) ^ 2)⁻¹ *
            ((1 + C_H) * (M_X * (X : ℝ) ^ alpha * Real.log (X : ℝ) ^ (3 : ℝ))) ≤ (1 / 32 : ℝ) := by
        have hratioMul := mul_le_mul_of_nonneg_right hRatio
          (inv_nonneg.mpr hSXSqPos.le)
        rw [mul_inv_cancel₀ hSXSqPos.ne'] at hratioMul
        nlinarith only [hratioMul]
      linarith only [hstep1, hstep2]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by nlinarith only [hN32CH, hCH1]
    have hnRpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le one_pos hn1
    have hnrpow3000pos : (0 : ℝ) < (n : ℝ) ^ (3000 : ℝ) := Real.rpow_pos_of_pos hnRpos _
    have hnle3000 : (n : ℝ) ≤ (n : ℝ) ^ (3000 : ℝ) := by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ (3000 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    have hN323000 : (32 : ℝ) * C_H ≤ (n : ℝ) ^ (3000 : ℝ) := le_trans hN32CH hnle3000
    have hSecondTermBound : C_H * (n : ℝ) ^ (-(3000 : ℝ)) ≤ (1 / 32 : ℝ) := by
      rw [Real.rpow_neg hnRpos.le, ← div_eq_mul_inv, div_le_iff₀ hnrpow3000pos]
      linarith only [hN323000]
    have hSumBound : |(sigmaBarInfinite nu X P)⁻¹ * sigmaBarSeq nu X P n - 1| +
        |sigmaBarInfinite nu X P * sigmaBarStarInvSeq nu X P n - 1| ≤ (1 / 16 : ℝ) := by
      refine le_trans hHomogAtXn ?_
      linarith only [hFirstTermBound, hSecondTermBound]
    have hOtherNonneg : (0 : ℝ) ≤ |sigmaBarInfinite nu X P * sigmaBarStarInvSeq nu X P n - 1| :=
      abs_nonneg _
    linarith only [hSumBound, hOtherNonneg]
  -- Apply `hGeneric` at `X := L` (`M_X := 202*M`) and `X := ell` (`M_X := MXell`).
  have hMXL1 : (1 : ℝ) ≤ 202 * M := by nlinarith only [hM]
  have hXGapL : (L : ℝ) - 202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (n : ℝ) := by
    have h1 : (L : ℝ) - (n : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) +
        200 * Real.log (L : ℝ) + 1 := by linarith only [hscale, hGap]
    have h2 : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) + (200 * Real.log (L : ℝ) + 1) ≤
        M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) +
          201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by linarith only [hTailL]
    have h3 : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) +
        201 * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
        202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have hLalpha_log3_nn : (0 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
        have hLalphann : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
        positivity
      nlinarith only [hM, hLalpha_log3_nn]
    linarith only [h1, h2, h3]
  have hThreshHomogL : lNaught C_H (C_H * (202 * M)) alpha cStar nu K ≤ (L : ℝ) :=
    (sbAsm_inflate_B (Ch := C_H) (K' := 202) (C := C) (M := M)
      hCHpos.le (le_trans zero_le_one hM) hCpos.le hα1 hcStarpos hnu hKnn (by norm_num)
      hCH_C hCHK'Llogfac_C).trans hLnaughtAtL
  have hRatioL : 202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) *
      (32 * C_H * (1 + C_H)) ≤ (sigmaBarInfinite nu L P) ^ 2 := by
    have hThreshRatioL : lNaught C0star (K'ratioL * M) alpha cStar nu K ≤ (L : ℝ) :=
      (sbAsm_inflate_C (C0 := C0star) (K' := K'ratioL) (C := C) (M := M)
        (le_trans zero_le_one hC0star1) (le_trans zero_le_one hM) hC1 hα1 hcStarpos hnu hKnn
        hK'ratioL1 hC0starK'ratiologfac_C).trans hLnaughtAtL
    have hK'ratioLM1 : (1 : ℝ) ≤ K'ratioL * M := by nlinarith only [hK'ratioL1, hM]
    have hSstarAtL := hSstarLower C0star le_rfl (K'ratioL * M) hK'ratioLM1 alpha hα0 hα1 cStar
      hcStarpos hcStar2 nu hnu hnu1 K hKnn P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hThreshRatioL L
      (by linarith only [hL64]) le_rfl
    have hStarLe := sigmaBarStarScalar_originCube_le_sigmaBarInfinite hnu L hPrefix hJ2 hJ3 hJ4 L
    have hStarPos := SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L
      hPrefix hJ2 hJ3 hJ4 (L : ℤ)
    have hStarSqLe : sigmaBarStarScalar nu L P (cubeSet (originCube d (L : ℤ))) ^ 2 ≤
        (sigmaBarInfinite nu L P) ^ 2 := pow_le_pow_left₀ hStarPos.le hStarLe 2
    have hcK''202M : c * (K'ratioL * M) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) =
        (c * K'') * (202 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
      rw [hK'ratioLdef]; ring
    have hLalpha_log3_nn : (0 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have hLalphann : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity
    have h202Mnn : (0 : ℝ) ≤ 202 * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
      have hMnn : (0 : ℝ) ≤ M := le_trans zero_le_one hM
      positivity
    nlinarith only [hSstarAtL, hStarSqLe, hcK''202M, hcK''big, h202Mnn]
  have hHBL := hGeneric L (202 * M) hMXL1 hXGapL hL3nat hThreshHomogL hRatioL
  have hXGapEll : (ell : ℝ) - MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) ≤
      (n : ℝ) := by
    have h1 : 3216 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) ≤
        MXell * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by
      have hnn : (0 : ℝ) ≤ (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by
        have hlogellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := by
          have : (0 : ℝ) ≤ Real.log (ell : ℝ) := by
            have : (1 : ℝ) ≤ (ell : ℝ) := by linarith only [hell64]
            exact Real.log_nonneg this
          positivity
        positivity
      have hle : (3216 : ℝ) ≤ MXell := by
        have h0 : (0 : ℝ) ≤ C_H * sbAsmGrowthB := by positivity
        rw [hMXelldef]; linarith only [h0]
      exact mul_le_mul_of_nonneg_right hle hnn
    have h2 : (ell : ℝ) - (n : ℝ) ≤ MXell * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) :=
      le_trans hGap (le_trans hTailToEll h1)
    linarith only [h2]
  have hRatioEll : MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) *
      (32 * C_H * (1 + C_H)) ≤ (sigmaBarInfinite nu ell P) ^ 2 := by
    have hThreshRatioEll : lNaught C0star (K'' * MXell) alpha cStar nu K ≤ (ell : ℝ) :=
      (sbAsm_inflate_fixed (C0 := C0star) (Mfix := K'' * MXell) (C := C) (M := M)
        (le_trans zero_le_one hC0star1) (by positivity) hM hC1 hα1 hcStarpos hnu hKnn hC0star_C
        hK''MXell_C).trans hLnaught
    have hK''MXell1 : (1 : ℝ) ≤ K'' * MXell := by nlinarith only [hK''1, hMXell1]
    have hSstarAtEll := hSstarLower C0star le_rfl (K'' * MXell) hK''MXell1 alpha hα0 hα1 cStar
      hcStarpos hcStar2 nu hnu hnu1 K hKnn P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 ell hThreshRatioEll ell
      (by linarith only [hell64]) le_rfl
    have hStarLe := sigmaBarStarScalar_originCube_le_sigmaBarInfinite hnu ell hPrefix hJ2 hJ3 hJ4
      ell
    have hStarPos := SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu ell
      hPrefix hJ2 hJ3 hJ4 (ell : ℤ)
    have hStarSqLe : sigmaBarStarScalar nu ell P (cubeSet (originCube d (ell : ℤ))) ^ 2 ≤
        (sigmaBarInfinite nu ell P) ^ 2 := pow_le_pow_left₀ hStarPos.le hStarLe 2
    have hcK''MXell : c * (K'' * MXell) * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) =
        (c * K'') * (MXell * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by ring
    have hellalpha_log3_nn : (0 : ℝ) ≤ (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by
      have hlogellnn : (0 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := by
        have : (0 : ℝ) ≤ Real.log (ell : ℝ) := by
          have : (1 : ℝ) ≤ (ell : ℝ) := by linarith only [hell64]
          exact Real.log_nonneg this
        positivity
      positivity
    have hMXellnn : (0 : ℝ) ≤ MXell * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by
      have hMXellnn' : (0 : ℝ) ≤ MXell := le_trans zero_le_one hMXell1
      positivity
    nlinarith only [hSstarAtEll, hStarSqLe, hcK''MXell, hcK''big, hMXellnn]
  have hHBEll := hGeneric ell MXell hMXell1 hXGapEll hell3nat hThreshHomogEll hRatioEll
  linarith only [hHBL, hHBEll]

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
