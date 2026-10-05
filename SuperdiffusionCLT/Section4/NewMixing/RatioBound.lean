/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.AssemblyRatioSmall
public import SuperdiffusionCLT.Section4.NewMixing.ScaleConstruction

/-!
# `hRatio`: `σ̄_r σ̄_{ell,*}^{-1}(cu_n) ≤ Cratio`

The bound needed by `newMixAsm_mainBound_uniform2` (`AssemblyMainUniform2.lean`):
the reference comparison `e.mixing.reference.compare`
(see `newMixAsm_refCompare_of_homog`) gives

```
|shom_r shom_{ell,*}^{-1}(cu_n) - 1| ≤ Cref shom_r^{-2} ((L-m)_+ + K log^2 L),
```

not the absolute bound `σ̄_r σ̄_{ell,*}^{-1}(cu_n) ≤ Cratio` that
`newMixAsm_mainBound_uniform2` needs. Turning the first into the second needs the
right-hand side bounded by an absolute constant (independent of `L, m, K`) at
the scales the scale construction `newMixAsm_scaleExplicit` produces, once `L` clears a
threshold `L₀`.

**The route used here is sharper than a `lNaught_absorbs`-style
`log¹¹`-power corollary**: instead of the crude growth bound `shom_r ≳ nu^{-1}(1+r)` /
`shom_r ≳ L^{1/2}log^{-9/2}L`, this file reuses
`Section4.SigmaBarComparison.AssemblyRatioSmall.sbAsm_ratio_small`, which
already proves the SHARP absolute bound

```
C M L^alpha shom_L^{-2} log^3 L ≤ 1/2
```

(via `lNaught_sstar_lower`'s `shom_L^2 ≳ M L^alpha log^3 L`, itself from
`SstarLowerBound`), at `L ≥ L₀(C, C M, alpha, cStar, nu, K)`.
Instantiating that at the scale `r` (in place of `L`) with `M := Cref(M+K)`,
and comparing `r`'s own `r^alpha log^3 r` to the *outer* `L`'s
`L^alpha log^3 L` and `log^2 L` via the scale-construction fact `r ≥ L/2`
(so `r^alpha ≥ L^alpha/2` and `log r ≥ (log L)/2`, up to a numeral loss of
`16`), gives the bracket `(L-m)_+ + K log^2 L` bounded by `16(M+K) r^alpha
log^3 r`, hence the whole right-hand side by the absolute constant `1/4` once
`C' ≥ 32`. No `log¹¹` power, and no new `lNaught_absorbs`-style corollary, is
needed.

A cruder `log¹¹` estimate would also suffice for the printed reading, but it is a weaker
route than the one used here.
-/

@[expose] public section

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)
open SuperdiffusionCLT.Section4.SigmaBarComparison (sbAsm_ratio_small)

namespace SuperdiffusionCLT.Section4.NewMixing

noncomputable section

/-! ## Elementary comparison of `r`-scale and `L`-scale log/power growth,
given `L/2 ≤ r`. -/

private lemma newMixRatio_half_rpow_le {alpha : ℝ} (halpha1 : alpha ≤ 1) :
    (1 : ℝ) / 2 ≤ ((1 : ℝ) / 2) ^ alpha := by
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha1
  rwa [Real.rpow_one] at h

private lemma newMixRatio_pow_scale {L r alpha : ℝ} (hL : 0 ≤ L) (hr : L / 2 ≤ r)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    L ^ alpha ≤ 2 * r ^ alpha := by
  have hhalf := newMixRatio_half_rpow_le halpha1
  have hL2nonneg : (0 : ℝ) ≤ L / 2 := by linarith only [hL]
  have hstep1 : (L / 2) ^ alpha ≤ r ^ alpha := Real.rpow_le_rpow hL2nonneg hr halpha0
  have hLalpha_nonneg : (0 : ℝ) ≤ L ^ alpha := Real.rpow_nonneg hL _
  have heq2 : (L / 2 : ℝ) = L * (1 / 2) := by ring
  have heq3 : (L * (1 / 2) : ℝ) ^ alpha = L ^ alpha * ((1 : ℝ) / 2) ^ alpha :=
    Real.mul_rpow hL (by norm_num)
  have hcomb : L ^ alpha * ((1 : ℝ) / 2) ≤ (L / 2) ^ alpha := by
    rw [heq2, heq3]
    exact mul_le_mul_of_nonneg_left hhalf hLalpha_nonneg
  linarith only [hcomb, hstep1]

private lemma newMixRatio_log_scale {L r : ℝ} (hL16 : (16 : ℝ) < L) (hr : L / 2 ≤ r) :
    Real.log L ≤ 2 * Real.log r ∧ (1 : ℝ) ≤ Real.log r := by
  have hLpos : (0 : ℝ) < L := by linarith only [hL16]
  have hL2pos : (0 : ℝ) < L / 2 := by linarith only [hLpos]
  have hlogr_ge : Real.log (L / 2) ≤ Real.log r := Real.log_le_log hL2pos hr
  have hlogdiv : Real.log (L / 2) = Real.log L - Real.log 2 :=
    Real.log_div hLpos.ne' (by norm_num)
  have hlog16 : Real.log (16 : ℝ) ≤ Real.log L := Real.log_le_log (by norm_num) hL16.le
  have hlog16eq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlog2bound : (0.69 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  constructor
  · linarith only [hlogr_ge, hlogdiv, hlog16, hlog16eq, hlog2bound]
  · linarith only [hlogr_ge, hlogdiv, hlog16, hlog16eq, hlog2bound]

/-! ## The combined gap bound: `M L^alpha log^3 L + K log^2 L ≤ 16(M+K) r^alpha log^3 r`. -/

private lemma newMixRatio_gap_bound {L r alpha M K : ℝ}
    (hL16 : (16 : ℝ) < L) (hr : L / 2 ≤ r)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) (hM : 0 ≤ M) (hK : 0 ≤ K) :
    M * L ^ alpha * Real.log L ^ (3 : ℝ) + K * Real.log L ^ (2 : ℝ) ≤
      16 * (M + K) * r ^ alpha * Real.log r ^ (3 : ℝ) := by
  have hLnn : (0 : ℝ) ≤ L := by linarith only [hL16]
  have hLge1 : (1 : ℝ) ≤ L := by linarith only [hL16]
  have hα1 : alpha ≤ 1 := halpha1.le
  have hpow := newMixRatio_pow_scale hLnn hr halpha0 hα1
  obtain ⟨hlog2r, hlogr1⟩ := newMixRatio_log_scale hL16 hr
  have hlogLnn : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hLge1
  have hlogrnn : (0 : ℝ) ≤ Real.log r := by linarith only [hlogr1]
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h16 : Real.log (16 : ℝ) ≤ Real.log L := Real.log_le_log (by norm_num) hL16.le
    have h16eq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    have hlog2gt : (0.69 : ℝ) < Real.log 2 := by linarith only [Real.log_two_gt_d9]
    linarith only [h16, h16eq, hlog2gt]
  have hLalphage1 : (1 : ℝ) ≤ L ^ alpha := newMixParam_one_le_rpow hLge1 halpha0
  have hlogsq_le_cube : Real.log L ^ (2 : ℝ) ≤ Real.log L ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogL1 (by norm_num)
  have hK_le_KL : K ≤ K * L ^ alpha := le_mul_of_one_le_right hK hLalphage1
  have hlogL3nn : (0 : ℝ) ≤ Real.log L ^ (3 : ℝ) := Real.rpow_nonneg hlogLnn _
  have hstep1 : M * L ^ alpha * Real.log L ^ (3 : ℝ) + K * Real.log L ^ (2 : ℝ) ≤
      M * L ^ alpha * Real.log L ^ (3 : ℝ) + K * L ^ alpha * Real.log L ^ (3 : ℝ) := by
    have ha : K * Real.log L ^ (2 : ℝ) ≤ K * Real.log L ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogsq_le_cube hK
    have hb : K * Real.log L ^ (3 : ℝ) ≤ (K * L ^ alpha) * Real.log L ^ (3 : ℝ) :=
      mul_le_mul_of_nonneg_right hK_le_KL hlogL3nn
    linarith only [ha, hb]
  have hstep2 : M * L ^ alpha * Real.log L ^ (3 : ℝ) + K * L ^ alpha * Real.log L ^ (3 : ℝ) =
      (M + K) * L ^ alpha * Real.log L ^ (3 : ℝ) := by ring
  have h3cube : Real.log L ^ (3 : ℝ) ≤ 8 * Real.log r ^ (3 : ℝ) := by
    have hs : Real.log L ^ (3 : ℝ) ≤ (2 * Real.log r) ^ (3 : ℝ) :=
      Real.rpow_le_rpow hlogLnn hlog2r (by norm_num)
    have heq : (2 * Real.log r : ℝ) ^ (3 : ℝ) = (2 : ℝ) ^ (3 : ℝ) * Real.log r ^ (3 : ℝ) :=
      Real.mul_rpow (by norm_num) hlogrnn
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [heq, h8] at hs
    exact hs
  have hMKnn : (0 : ℝ) ≤ M + K := by linarith only [hM, hK]
  have hrnn : (0 : ℝ) ≤ r := by linarith only [hL16, hr]
  have hrpow_nn : (0 : ℝ) ≤ 2 * r ^ alpha := by
    have h1 : (0 : ℝ) ≤ r ^ alpha := Real.rpow_nonneg hrnn _
    linarith only [h1]
  have hmulstep : L ^ alpha * Real.log L ^ (3 : ℝ) ≤ (2 * r ^ alpha) * (8 * Real.log r ^ (3 : ℝ)) :=
    mul_le_mul hpow h3cube hlogL3nn hrpow_nn
  have heqrhs : (2 * r ^ alpha) * (8 * Real.log r ^ (3 : ℝ)) = 16 * r ^ alpha * Real.log r ^ (3 : ℝ) := by
    ring
  have hmulstep' : L ^ alpha * Real.log L ^ (3 : ℝ) ≤ 16 * r ^ alpha * Real.log r ^ (3 : ℝ) := by
    rw [heqrhs] at hmulstep; exact hmulstep
  have hfinal : (M + K) * L ^ alpha * Real.log L ^ (3 : ℝ) ≤
      (M + K) * (16 * r ^ alpha * Real.log r ^ (3 : ℝ)) := by
    have hmm := mul_le_mul_of_nonneg_left hmulstep' hMKnn
    calc (M + K) * L ^ alpha * Real.log L ^ (3 : ℝ)
        = (M + K) * (L ^ alpha * Real.log L ^ (3 : ℝ)) := by ring
      _ ≤ (M + K) * (16 * r ^ alpha * Real.log r ^ (3 : ℝ)) := hmm
  have heqfinal : (M + K) * (16 * r ^ alpha * Real.log r ^ (3 : ℝ)) =
      16 * (M + K) * r ^ alpha * Real.log r ^ (3 : ℝ) := by ring
  linarith only [hstep1, hstep2, hfinal, heqfinal]

/-! ## The main theorem: `hRatio` at the scale-construction scales, `L ≥ L₀`. -/

/-- **`hRatio`** (the ratio bound needed by `newMixAsm_mainBound_uniform2`,
`AssemblyMainUniform2.lean`): `σ̄_r σ̄_{ell,*}^{-1}(cu_n) ≤ Cratio` for an ABSOLUTE
`Cratio` (`5/4` suffices), derived from the
conclusion of the reference comparison (`e.mixing.reference.compare`, taken here verbatim as the
hypothesis `hRC`, as in `newMixAsm_mainBound_uniform2`),
the gap input `hLm` of the scale construction and the range fact
(`hLr2 : L/2 ≤ r`), and a threshold `L ≥ L₀` of the same "`∃C, ∀C'≥C`" shape
as `newMixAsm_scaleExplicit` itself, with `L₀ := lNaught C' (C' *
(Cref*(M+K))) alpha cStar nu Kdeg` (absorbing the `Cref` constant into the
`M`-argument, matching `newMixParam_absorbSlack`'s `C*(M+K)` trick). -/
theorem newMixRatio_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ Cref : ℝ, 1 ≤ Cref →
      ∀ nu cStar Kdeg : ℝ, 0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 ≤ Kdeg →
      ∀ (P : ProbabilityMeasure (ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar Kdeg hPrefix hJ2 hJ3 →
      ∀ alpha M K : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M → 1 ≤ K →
      ∀ L m r ell n : ℕ,
        lNaught C' (C' * (Cref * (M + K))) alpha cStar nu Kdeg ≤ (L : ℝ) / 2 →
        (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
        (L : ℝ) / 2 ≤ (r : ℝ) →
        |(sigmaBarInfinite nu r P)⁻¹ * sigmaBarSeq nu ell P n - 1| +
            |sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n - 1| ≤
          Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
            (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) →
        ∀ Cratio : ℝ, (5 : ℝ) / 4 ≤ Cratio →
        sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n ≤ Cratio := by
  obtain ⟨C0star, hC0star1, hRatioSmall⟩ := sbAsm_ratio_small d hd
  obtain ⟨C0g, hC0g1, hGeFn⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_ge
  refine ⟨max 32 (max C0star C0g), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro C' hCC' Cref hCref1 nu cStar Kdeg hnu hnu1 hcStar hcStar2 hKdeg
    P hPrefix hJ2 hJ3 hJ1V2 hJ4b hJ5 alpha M K hα0 hα1 hM1 hK1
    L m r ell n hLthresh hLm hLr2 hRC Cratio hCratio
  have hC32 : (32 : ℝ) ≤ C' := le_trans (le_max_left _ _) hCC'
  have hC0star' : C0star ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCC'
  have hC0g' : C0g ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCC'
  have hC'pos : (0 : ℝ) < C' := lt_of_lt_of_le (by norm_num) hC32
  have hCrefMK1 : (1 : ℝ) ≤ Cref * (M + K) := by nlinarith only [hCref1, hM1, hK1]
  -- `L > 16`, from `lNaught_ge` applied at the same `M`-argument.
  have hC'CrefMK1 : (1 : ℝ) ≤ C' * (Cref * (M + K)) := by
    have h1 : C' ≤ C' * (Cref * (M + K)) := le_mul_of_one_le_right hC'pos.le hCrefMK1
    linarith only [h1, hC32]
  have hLge8half : (8 : ℝ) < (L : ℝ) / 2 := by
    have hge := hGeFn C' hC0g' (C' * (Cref * (M + K))) hC'CrefMK1 alpha hα0 hα1 cStar hcStar
      hcStar2 nu hnu hnu1 Kdeg hKdeg
    exact lt_of_lt_of_le hge hLthresh
  have hL16 : (16 : ℝ) < (L : ℝ) := by linarith only [hLge8half]
  have hMnn : (0 : ℝ) ≤ M := by linarith only [hM1]
  have hKnn : (0 : ℝ) ≤ K := by linarith only [hK1]
  have hgap := newMixRatio_gap_bound hL16 hLr2 hα0 hα1 hMnn hKnn
  -- `max 0 (L-m) ≤ M L^alpha log^3 L`, from `hLm`.
  have hmaxle : max (0 : ℝ) ((L : ℝ) - (m : ℝ)) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    apply max_le
    · have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
      have hLalphann : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg L) _
      have hlogL3nn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogLnn _
      positivity
    · linarith only [hLm]
  have hbracket : max (0 : ℝ) ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ) ≤
      16 * (M + K) * (r : ℝ) ^ alpha * Real.log (r : ℝ) ^ (3 : ℝ) := by
    linarith only [hmaxle, hgap]
  -- `sbAsm_ratio_small` at `L := r`, `M := Cref*(M+K)`.
  have hthreshR : lNaught C' (C' * (Cref * (M + K))) alpha cStar nu Kdeg ≤ (r : ℝ) :=
    le_trans hLthresh hLr2
  have hSmall := hRatioSmall C' hC0star' nu cStar Kdeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4b hJ5
    alpha (Cref * (M + K)) hα0 hα1 hCrefMK1 r hthreshR
  set shomr := sigmaBarInfinite nu r P with hshomrdef
  have hshomrpos : (0 : ℝ) < shomr := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4b
  have hshomrneg2nn : (0 : ℝ) ≤ shomr ^ (-(2 : ℝ)) := Real.rpow_nonneg hshomrpos.le _
  have hSmall' : Cref * (M + K) * (r : ℝ) ^ alpha * shomr ^ (-(2 : ℝ)) * Real.log (r : ℝ) ^ (3 : ℝ) ≤
      1 / (2 * C') := by
    rw [le_div_iff₀ (by linarith only [hC'pos] : (0 : ℝ) < 2 * C')]
    nlinarith only [hSmall]
  have hCrefshomrnn : (0 : ℝ) ≤ Cref * shomr ^ (-(2 : ℝ)) :=
    mul_nonneg (by linarith only [hCref1]) hshomrneg2nn
  have hstepfinal : Cref * shomr ^ (-(2 : ℝ)) *
      (max (0 : ℝ) ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) ≤
      Cref * shomr ^ (-(2 : ℝ)) * (16 * (M + K) * (r : ℝ) ^ alpha * Real.log (r : ℝ) ^ (3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hbracket hCrefshomrnn
  have heqswap : Cref * shomr ^ (-(2 : ℝ)) *
      (16 * (M + K) * (r : ℝ) ^ alpha * Real.log (r : ℝ) ^ (3 : ℝ)) =
      16 * (Cref * (M + K) * (r : ℝ) ^ alpha * shomr ^ (-(2 : ℝ)) * Real.log (r : ℝ) ^ (3 : ℝ)) := by
    ring
  have hstepfinal' : Cref * shomr ^ (-(2 : ℝ)) *
      (max (0 : ℝ) ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) ≤
      16 * (1 / (2 * C')) := by
    rw [heqswap] at hstepfinal
    have h16 := mul_le_mul_of_nonneg_left hSmall' (by norm_num : (0 : ℝ) ≤ 16)
    linarith only [hstepfinal, h16]
  have hquarter : Cref * shomr ^ (-(2 : ℝ)) *
      (max (0 : ℝ) ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) ≤ 1 / 4 := by
    have h1 : (16 : ℝ) * (1 / (2 * C')) ≤ 1 / 4 := by
      rw [show (16 : ℝ) * (1 / (2 * C')) = 8 / C' by ring,
        div_le_div_iff₀ hC'pos (by norm_num : (0 : ℝ) < 4)]
      linarith only [hC32]
    linarith only [hstepfinal', h1]
  have habs2 : |shomr * sigmaBarStarInvSeq nu ell P n - 1| ≤
      Cref * shomr ^ (-(2 : ℝ)) * (max (0 : ℝ) ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) := by
    have habs1nn : (0 : ℝ) ≤ |shomr⁻¹ * sigmaBarSeq nu ell P n - 1| := abs_nonneg _
    linarith only [hRC, habs1nn]
  have hfin : shomr * sigmaBarStarInvSeq nu ell P n ≤ 5 / 4 := by
    have h := (abs_le.mp (le_trans habs2 hquarter)).2
    linarith only [h]
  linarith only [hfin, hCratio]

end

end SuperdiffusionCLT.Section4.NewMixing
