/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyScaleFacts
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyStar
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyRefFold
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyFold
public import SuperdiffusionCLT.Section4.NewMixing.Nu4Threshold
public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioC
public import SuperdiffusionCLT.Section4.SigmaBarComparison.Growth

/-!
# The reference comparison from `p.homog.below` and the cutoff localization

`e.mixing.reference.compare`: for the scales of
the scale construction, with the threshold `L ≥ L₀`,
`|shom_r⁻¹ shom_ell(cu_n) - 1| + |shom_r shom_{ell,*}^{-1}(cu_n) - 1|
  ≤ C shom_r^{-2} ((L-m)_+ + K log² L)`.

The lower block is compared through the cutoff localization (`AssemblyStar.lean`), the
upper block through the identity `shom_ell shom_{ell,*}^{-1} ≈ 1`, which comes from
`p.homog.below` (carried as the hypothesis `hHomog`) at the two cutoffs `r` and `ell` on `cu_n`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

theorem newMixAsm_refCompare_of_homog (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hHomog : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
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
    ∀ Cg : ℝ, 1 ≤ Cg → ∃ Cref Cp : ℝ, 1 ≤ Cref ∧ 1 ≤ Cp ∧
      ∀ (nu cStar K nondeg : ℝ), 0 < nu → nu ≤ 1 → 1 ≤ K →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar nondeg hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ (L m ell r n : ℕ),
              SuperdiffusionCLT.Frozen.Section4.lNaught Cp (Cp * (M + K)) alpha cStar nu
                nondeg ≤ (L : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m : ℝ) →
              n < ell → ell < m → ell ≤ L →
              (L : ℝ) / 2 ≤ (ell : ℝ) → (L : ℝ) / 2 ≤ (r : ℝ) → (r : ℝ) ≤ 2 * (L : ℝ) →
              (L : ℝ) - (ell : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + Cg * K * Real.log (L : ℝ) →
              (ell : ℝ) - (n : ℝ) ≤ Cg * K * Real.log (L : ℝ) →
              n ≤ r →
              (r : ℝ) - (n : ℝ) ≤ max 0 ((L : ℝ) - (m : ℝ)) + Cg * K * Real.log (L : ℝ) →
              200 * Real.log (L : ℝ) ≤ min (ell : ℝ) (r : ℝ) - (n : ℝ) →
              (8 : ℝ) < (L : ℝ) → (L : ℝ) / 4 ≤ (n : ℝ) →
              |(sigmaBarInfinite nu r P)⁻¹ * sigmaBarSeq nu ell P n - 1| +
                  |sigmaBarInfinite nu r P * sigmaBarStarInvSeq nu ell P n - 1| ≤
                Cref * (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) *
                  (max 0 ((L : ℝ) - (m : ℝ)) + K * Real.log (L : ℝ) ^ (2 : ℝ)) := by
  intro Cg hCg1
  obtain ⟨Chom, hChom1, hH⟩ := hHomog
  obtain ⟨C0abs, hC0abs1, hAbs⟩ := SuperdiffusionCLT.Section4.SigmaBarComparison.sbIndep_absorption_le_eighth hd
  obtain ⟨Cc, hCc1, hGrow⟩ := SuperdiffusionCLT.Section4.SigmaBarComparison.sbAsm_crude_growth_bound d
  obtain ⟨Cst, hCst, hStar⟩ := newMixAsm_starCompare d hd
  obtain ⟨B8, hB8def⟩ : ∃ B8 : ℝ, B8 = (8 : ℝ) ^ (3000 : ℕ) := ⟨_, rfl⟩
  have hB8 : 0 ≤ B8 := by rw [hB8def]; positivity
  set C3₀ : ℝ := 4 / ((100000 : ℝ) ^ 2 * (Real.log 2) ^ (12 : ℝ)) with hC3₀def
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC3₀nn : 0 ≤ C3₀ := by rw [hC3₀def]; positivity
  set c1 : ℝ := 1 + Cg + 4 * Chom with hc1def
  set mu : ℝ := 16 + 2 * Cg + Chom with hmudef
  set Cabs : ℝ := max C0abs (max Chom (Chom * B8)) with hCabsdef
  set c2 : ℝ := 72 * Chom * B8 * Cc ^ 2 * C3₀ ^ 2 with hc2def
  set c3 : ℝ := 27 * Cc ^ 3 * Cst * C3₀ ^ 4 with hc3def
  set Cref : ℝ := 40 * Chom * c1 + c2 + 4 * c3 with hCrefdef
  set Cp : ℝ := max 100000 (max (2 * Cabs) (max (Cabs * mu) (8 * Cc * Cst * C3₀ ^ 2))) with hCpdef
  have hCp1 : (1 : ℝ) ≤ Cp := le_trans (by norm_num) (le_max_left _ _)
  have hCst0 : 0 < Cst := hCst
  have hCabs1 : (1 : ℝ) ≤ Cabs := le_trans hChom1 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hc1 : 1 ≤ c1 := by rw [hc1def]; linarith only [hCg1, hChom1]
  have hmu : 16 ≤ mu := by rw [hmudef]; linarith only [hCg1, hChom1]
  have hc2 : 0 ≤ c2 := by rw [hc2def]; positivity
  have hc3 : 0 ≤ c3 := by rw [hc3def]; positivity
  have hCref1 : 1 ≤ Cref := by
    rw [hCrefdef]
    have : 1 ≤ Chom * c1 := by nlinarith only [hChom1, hc1]
    linarith only [this, hc2, hc3]
  refine ⟨Cref, Cp, hCref1, hCp1, ?_⟩
  intro nu cStar K nondeg hnu hnu1 hK P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha M hα0 hα1 hM
    L m ell r n hL hGm hnell hellm hellL hLell hLr2 hr2L hg1 hg2 hnr hg3 h200 hL8 hLn
  have hcStar : 0 < cStar := hJ5.cStar_pos
  have hcStar2 : cStar ≤ 2 := hJ5.cStar_le_two
  have hnondeg : 0 ≤ nondeg := hJ5.K_pos.le
  have hMK : (0 : ℝ) ≤ M + K := by linarith only [hM, hK]
  have hσpos : 0 < sigmaBarInfinite nu r P := sigmaBarInfinite_pos hnu r hPrefix hJ2 hJ3 hJ4
  have hspos : 0 < sigmaBarInfinite nu ell P := sigmaBarInfinite_pos hnu ell hPrefix hJ2 hJ3 hJ4
  set G : ℝ := max 0 ((L : ℝ) - (m : ℝ)) with hGdef
  have hG0 : 0 ≤ G := le_max_left _ _
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have hGM : G ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    refine max_le ?_ (by linarith only [hGm])
    have : 0 ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg L) _
    have h3 : 0 ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogL0 _
    positivity
  set M1 : ℝ := mu * (M + K) with hM1def
  have hM1 : (1 : ℝ) ≤ M1 := by
    rw [hM1def]; nlinarith only [hmu, hM, hK]
  have hCabsC0 : C0abs ≤ Cabs := le_max_left _ _
  have hCabsChom : Chom ≤ Cabs := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCabs8 : Chom * B8 ≤ Cabs := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCp2 : 2 * Cabs ≤ Cp := by rw [hCpdef]; simp [le_max_iff]
  have hCpmu : Cabs * mu ≤ Cp := by rw [hCpdef]; simp [le_max_iff]
  have hCpLam : 8 * Cc * Cst * C3₀ ^ 2 ≤ Cp := by rw [hCpdef]; simp [le_max_iff]
  have hCp100 : (100000 : ℝ) ≤ Cp := le_max_left _ _
  have hthrHalf : SuperdiffusionCLT.Frozen.Section4.lNaught Cabs (Cabs * M1) alpha cStar nu
      nondeg ≤ (L : ℝ) / 2 := by
    have hhalf := newMixAsm_lNaught_le_half (C := Cabs) (C' := Cp) (M := Cabs * M1)
      (M' := Cp * (M + K)) (alpha := alpha) (cStar := cStar) (nu := nu) (K := nondeg)
      (by linarith only [hCabs1]) hCp2 (by positivity)
      (by
        have : Cabs * M1 = (Cabs * mu) * (M + K) := by rw [hM1def]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hCpmu hMK)
      hnondeg hcStar hnu hα0 hα1
    linarith only [hhalf, hL]
  have hPer : ∀ a : ℕ, (L : ℝ) / 2 ≤ (a : ℝ) → (a : ℝ) ≤ 2 * (L : ℝ) → n ≤ a →
      (a : ℝ) - (n : ℝ) ≤ G + Cg * K * Real.log (L : ℝ) →
      (|(sigmaBarInfinite nu a P)⁻¹ * sigmaBarSeq nu a P n - 1| +
          |sigmaBarInfinite nu a P * sigmaBarStarInvSeq nu a P n - 1| ≤
        Chom * (sigmaBarInfinite nu a P) ^ (-(2 : ℝ)) *
            (c1 * (G + K * Real.log (L : ℝ) ^ (2 : ℝ))) + Chom * (n : ℝ) ^ (-(3000 : ℝ))) ∧
      (|(sigmaBarInfinite nu a P)⁻¹ * sigmaBarSeq nu a P n - 1| +
          |sigmaBarInfinite nu a P * sigmaBarStarInvSeq nu a P n - 1| ≤ 1 / 8) := by
    intro a ha1 ha2 hna hdiff
    have hthrA : SuperdiffusionCLT.Frozen.Section4.lNaught Cabs (Cabs * M1) alpha cStar nu
        nondeg ≤ (a : ℝ) := le_trans hthrHalf ha1
    have hgapabs : (a : ℝ) - M1 * (a : ℝ) ^ alpha * Real.log (a : ℝ) ^ (3 : ℝ) ≤ (a : ℝ) := by
      have h1 : 0 ≤ M1 * (a : ℝ) ^ alpha * Real.log (a : ℝ) ^ (3 : ℝ) := by
        have : 0 ≤ (a : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg a) _
        have h3 : 0 ≤ Real.log (a : ℝ) ^ (3 : ℝ) :=
          Real.rpow_nonneg (Real.log_natCast_nonneg a) _
        have : 0 ≤ M1 := by linarith only [hM1]
        positivity
      linarith only [h1]
    have habsA := hAbs Cabs hCabsC0 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha
      M1 hα0 hα1 hM1 a a le_rfl hthrA hgapabs
    have ha1' : (1 : ℝ) ≤ (a : ℝ) := by linarith only [ha1, hL8]
    have hnpow : (n : ℝ) ^ (-(3000 : ℝ)) ≤ B8 * (a : ℝ) ^ (-(99 : ℝ)) := by
      rw [hB8def]
      exact newMixAsm_n_neg3000_le ha1' (by linarith only [hLn, ha2])
    obtain ⟨hsz, hsm, hgapa⟩ := newMixAsm_perCutoff (s := sigmaBarInfinite nu a P)
      (sigmaBarInfinite_pos hnu a hPrefix hJ2 hJ3 hJ4) hChom1 hCg1 hK hM hα0 hα1 hCabsChom
      hCabs8 hnpow hL8.le ha1 ha2 hG0 hGM hdiff (le_of_eq hM1def.symm)
      habsA.2
    have hthrH : SuperdiffusionCLT.Frozen.Section4.lNaught Chom (Chom * M1) alpha cStar nu
        nondeg ≤ (a : ℝ) := by
      have hmono := SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both
        (C := Chom) (C' := Cabs) (M := Chom * M1) (M' := Cabs * M1) (alpha := alpha)
        (cStar := cStar) (nu := nu) (K := nondeg) (by linarith only [hChom1]) hCabsChom
        (mul_nonneg (by linarith only [hChom1]) (by linarith only [hM1]))
        (mul_le_mul_of_nonneg_right hCabsChom (by linarith only [hM1])) hnondeg hcStar hnu hα1
      exact le_trans hmono hthrA
    have hHa := hH nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 alpha M1 hα0 hα1 hM1
      a n hthrH hgapa
    exact ⟨le_trans hHa hsz, le_trans hHa hsm⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL8]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by linarith only [hL8]
  have hlogL1 : 1 ≤ Real.log (L : ℝ) := by
    obtain ⟨_, _, _, _, _, h⟩ := newMixAsm_scale_facts (L := (L : ℝ)) (a := (L : ℝ)) hL8.le
      (by linarith only [hLpos]) (by linarith only [hLpos]) hα0 hα1
    exact h
  -- the two cutoffs
  have hnellR : n ≤ ell := hnell.le
  have hdiffE : (ell : ℝ) - (n : ℝ) ≤ G + Cg * K * Real.log (L : ℝ) := by linarith only [hg2, hG0]
  have hdiffR : (r : ℝ) - (n : ℝ) ≤ G + Cg * K * Real.log (L : ℝ) := by
    rw [hGdef]; linarith only [hg3]
  have hellL' : (ell : ℝ) ≤ 2 * (L : ℝ) := by
    have : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hellL
    linarith only [this, hLpos]
  obtain ⟨hszE, hsmE⟩ := hPer ell hLell hellL' hnellR hdiffE
  obtain ⟨hszR, hsmR⟩ := hPer r hLr2 hr2L hnr hdiffR
  -- the polynomial bounds on `nu`
  have hnu4 : nu ^ (-(4 : ℝ)) ≤ (4 / (Cp ^ 2 * (Real.log 2) ^ (12 : ℝ))) * (L : ℝ) := by
    have hMK2 : 2 * Cp ≤ Cp * (M + K) := by
      have : (2 : ℝ) ≤ M + K := by linarith only [hM, hK]
      have h0' : (0 : ℝ) ≤ Cp := by linarith only [hCp100]
      nlinarith only [this, h0']
    exact newMixParam_nu4_le_linear_L (C := Cp) (M := Cp * (M + K)) (alpha := alpha)
      (cStar := cStar) (nu := nu) (K := nondeg) hCp100 hMK2 hnondeg hcStar hcStar2 hnu hnu1 hα0
      hα1 hL
  have hnu4' : nu ^ (-(4 : ℝ)) ≤ C3₀ * (L : ℝ) := by
    have h2 : 4 / (Cp ^ 2 * (Real.log 2) ^ (12 : ℝ)) ≤ C3₀ := by
      rw [hC3₀def]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have hsq : (100000 : ℝ) ^ 2 ≤ Cp ^ 2 := pow_le_pow_left₀ (by norm_num) hCp100 2
      exact mul_le_mul_of_nonneg_right hsq (by positivity)
    exact le_trans hnu4 (mul_le_mul_of_nonneg_right h2 hLpos.le)
  have hLCp : Cp ≤ (L : ℝ) :=
    newMixAsm_L_ge_of_nu4 (by linarith only [hCp100]) hnu hnu1 hnu4
  have hnuinv : nu⁻¹ ≤ C3₀ * (L : ℝ) :=
    le_trans (newMixAsm_inv_le_rpow_neg_four hnu hnu1) hnu4'
  have hnu3 : nu ^ (-(3 : ℝ)) ≤ C3₀ * (L : ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_ge hnu hnu1 (by norm_num)) hnu4'
  -- the size of `sigma`
  have hσle : sigmaBarInfinite nu r P ≤ 3 * Cc * C3₀ * (L : ℝ) ^ 2 := by
    have h1 := hGrow nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 r
    have hr1 : 1 + (r : ℝ) ≤ 3 * (L : ℝ) := by linarith only [hr2L, hL1]
    have h2 : Cc * nu⁻¹ * (1 + (r : ℝ)) ≤ Cc * (C3₀ * (L : ℝ)) * (3 * (L : ℝ)) := by
      have hr0 : (0 : ℝ) ≤ 1 + (r : ℝ) := by positivity
      have := mul_le_mul (mul_le_mul_of_nonneg_left hnuinv (by linarith only [hCc1])) hr1 hr0
        (by positivity)
      exact this
    calc sigmaBarInfinite nu r P ≤ Cc * nu⁻¹ * (1 + (r : ℝ)) := h1
      _ ≤ Cc * (C3₀ * (L : ℝ)) * (3 * (L : ℝ)) := h2
      _ = 3 * Cc * C3₀ * (L : ℝ) ^ 2 := by ring
  set q : ℝ := (L : ℝ) ^ (-(200 : ℝ)) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hLpos.le _
  -- the star comparison
  have hStarB : |sigmaBarStarInvSeq nu ell P n - sigmaBarStarInvSeq nu r P n| ≤
      Cst * nu ^ (-(3 : ℝ)) * q := by
    have hC3nn : 0 ≤ Cst * nu ^ (-(3 : ℝ)) := mul_nonneg hCst.le (Real.rpow_nonneg hnu.le _)
    rcases le_total ell r with h | h
    · have h1 := hStar hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 hnellR h
      rw [abs_sub_comm]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC3nn)
      rw [Nat.cast_sub hnellR]
      apply newMixAsm_three_pow_le hL1
      have : min (ell : ℝ) (r : ℝ) = (ell : ℝ) := min_eq_left (by exact_mod_cast h)
      linarith only [h200, this]
    · have h1 := hStar hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 hnr h
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC3nn)
      rw [Nat.cast_sub hnr]
      apply newMixAsm_three_pow_le hL1
      have : min (ell : ℝ) (r : ℝ) = (r : ℝ) := min_eq_right (by exact_mod_cast h)
      linarith only [h200, this]
  have hδ0 : 0 ≤ Cst * nu ^ (-(3 : ℝ)) * q :=
    mul_nonneg (mul_nonneg hCst.le (Real.rpow_nonneg hnu.le _)) hq0
  have hδle : Cst * nu ^ (-(3 : ℝ)) * q ≤ Cst * (C3₀ * (L : ℝ)) * q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnu3 hCst.le) hq0
  have h7 : (L : ℝ) ^ 7 * q ≤ 1 := newMixAsm_pow_mul_rpow_le_one hL1 (by norm_num)
  have h4 : (L : ℝ) ^ 4 * q ≤ 1 := newMixAsm_pow_mul_rpow_le_one hL1 (by norm_num)
  obtain ⟨hσ3δ, hσδsmall⟩ := newMixAsm_sigma_delta hσpos.le hδ0 hL1 hq0 (by linarith only [hCc1])
    hCst.le hC3₀nn hσle hδle h7 h4 hCpLam hLCp
  have hrneg : ∀ x : ℝ, 0 < x → x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
    intro x hx
    rw [Real.rpow_neg hx.le, Real.rpow_two]
  have hu0 : 0 < (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hσpos _
  have huσ : (sigmaBarInfinite nu r P) ^ (-(2 : ℝ)) * (sigmaBarInfinite nu r P) ^ 2 = 1 := by
    rw [hrneg _ hσpos]
    exact inv_mul_cancel₀ (by positivity)
  have hX1 : 1 ≤ G + K * Real.log (L : ℝ) ^ (2 : ℝ) := by
    have h1 : 1 ≤ Real.log (L : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; nlinarith only [hlogL1]
    have h2 : 1 ≤ K * Real.log (L : ℝ) ^ (2 : ℝ) := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 h1), hK, h1]
    linarith only [hG0, h2]
  have hn3 : (n : ℝ) ^ (-(3000 : ℝ)) ≤ B8 * (L : ℝ) ^ (-(99 : ℝ)) := by
    rw [hB8def]
    exact newMixAsm_n_neg3000_le hL1 (by linarith only [hLn])
  have h99 : (L : ℝ) ^ 4 * (L : ℝ) ^ (-(99 : ℝ)) ≤ 1 :=
    newMixAsm_pow_mul_rpow_le_one hL1 (by norm_num)
  have hw0 : 0 ≤ Chom * (n : ℝ) ^ (-(3000 : ℝ)) :=
    mul_nonneg (by linarith only [hChom1]) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hw := newMixAsm_w_bound hσpos.le hw0 huσ hu0.le hL1 hChom1 hB8 rfl hσle hn3 h99
  exact newMixAsm_final_fold hσpos hspos hChom1 hc1 hc2 hc3 hCrefdef hX1 rfl rfl hszE hsmE hszR
    hsmR hStarB hδ0 hσδsmall hσ3δ hw

end
end SuperdiffusionCLT.Section4.NewMixing
