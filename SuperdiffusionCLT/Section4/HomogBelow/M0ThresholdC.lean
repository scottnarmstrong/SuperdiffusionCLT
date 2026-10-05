/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.M0Threshold

/-!
The `m > L²` branch of the `m₀`-threshold: the companion of
`homogBelowM0_threshold_corrected` (`Section4/HomogBelow/M0ThresholdB.lean`), needed for the
other branch of the `p.homog.below` homogenization-below-cutoff assembly, where the input
scale `m` is *larger* than `L²` instead of smaller.

The statement is `homogBelowM0_threshold_corrected` with two changes: the
hypothesis is `L ^ 2 ≤ m` (instead of `m ≤ L ^ 2`), and `m₀` is now
`⌈Cprime * Real.log (m:ℝ) ^ 2⌉₊` (using `log m` instead of `log L`), both in
`X`'s `(m + m₀ + 1)` factor and on the right side of the inequality. `Θ₀`
itself (`(2Cenv(d)+4Cenv(d)²)·ν⁻²·L`) is unchanged: it still uses `L`.

**Math** (reusing every lemma from `M0Threshold.lean`): since `L² ≤ m` and `L ≥ 1`
(`homogBelowM0_L_controls`), `L ≤ L² ≤ m`; this one inequality drives
everything:
* `ν⁻¹ ≤ L ≤ m` and `ν⁻¹² ≤ L ≤ m`, so `homogBelowM0_upsilon2_le_pow`
  applies with `m` in place of `L`, giving `Υ₂ ≤ U₂·m^{p₂}`;
* `Cprime ≤ 1000L ≤ 1000m`, so `homogBelowM0_mPlusM0_le_cube` applies with
  *both* its own `L` and `m` parameters instantiated at `m`
  (using the trivial `m ≤ m²`), giving `m + m₀(m) + 1 ≤ 1003m³` directly;
* `Θ₀ ≤ Cdp·L² ≤ Cdp·m²` (`homogBelowM0_thetaBound_le_sq` chained with
  `L² ≤ m ≤ m²`).

These three bounds are exactly the `L`-based bounds of
`homogBelowM0_threshold_corrected`'s proof with `L` replaced by `m`
throughout (`Θ₀`'s own formula, which still contains the actual `L`, is
untouched — only its *upper bound* is re-expressed via `m`), so the
remainder of the proof (assembling `log X ≤ A₀+A₁·log m`, the second log,
and the final `≤ Bfinal·log²m ≤ Cprime·log²m ≤ m₀` chain) is the identical
argument with `m` as the growth variable and `Cprime ≥ 3000` forcing
`m ≥ 3` (via `Cprime ≤ 1000m`) in place of forcing `L ≥ 3`.

Sanity check: at the smallest allowed input, `L = 1` forces `m ≥ 1`; the
`Cprime ≥ 3000` threshold this file's `C₀` provides forces `m ≥ 3` exactly
as `homogBelowM0_threshold_corrected` forces `L ≥ 3`, so the same
refutation the corrected `m ≤ L²` branch addresses (the naive `L = 1`
counterexample for a single shared constant) is excluded here too,
now via `m` instead of `L`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **The `m > L²` branch of the corrected `m₀`-threshold theorem**: same
statement as `homogBelowM0_threshold_corrected`, except `L ^ 2 ≤ m`
replaces `m ≤ L ^ 2`, and `m₀ := ⌈Cprime * Real.log (m:ℝ) ^ 2⌉₊` (using
`log m`, not `log L`) everywhere `m₀` appears — in `X`'s `(m+m₀+1)` factor
and on the right side. -/
theorem homogBelowM0_threshold_large_m :
    ∀ C61 : ℝ, 1 ≤ C61 →
    ∀ Cmix : ℝ, 1 ≤ Cmix →
    ∀ Cellip : ℝ, 1 ≤ Cellip →
    ∀ d : ℕ, 2 ≤ d →
    ∃ C0 : ℝ, 1 ≤ C0 ∧
    ∀ Cprime : ℝ, C0 ≤ Cprime →
    ∀ M : ℝ, 1 ≤ M →
    ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
    ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
    ∀ K : ℝ, 0 ≤ K →
    ∀ L : ℕ,
      SuperdiffusionCLT.Frozen.Section4.lNaught Cprime M alpha cStar nu K ≤ (L : ℝ) →
      ∀ m : ℕ, L ^ 2 ≤ m →
        32 * C61 * (Cmix + 1) *
          Real.log
            ((C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
                    (6 * ((d : ℝ) + 1) ^ 2) +
                C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
                  2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2))))) *
              ((m : ℝ) + (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) + 1) *
              ((2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
                    4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2) *
                nu⁻¹ ^ 2 * (L : ℝ))) *
          Real.log
            (3 * ((2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
                    4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^ 2) *
                nu⁻¹ ^ 2 * (L : ℝ)) *
              (2 + 4 * Cmix *
                Real.log
                  ((C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
                          (6 * ((d : ℝ) + 1) ^ 2) +
                      C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
                        2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2))))) *
                    ((m : ℝ) + (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) + 1) *
                    ((2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
                          4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^
                            2) *
                      nu⁻¹ ^ 2 * (L : ℝ))))) ≤
          (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) := by
  intro C61 hC61 Cmix hCmix Cellip hCellip d hd
  clear hd
  have hCd1 : 1 ≤ SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d := by
    clear * - d
    exact SuperdiffusionCLT.Section2.Annealed.one_le_cutoffEnvelopeConst d
  set Cd : ℝ := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d with hCddef
  clear hCddef
  have hKPsi : Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) = 64 :=
    homogBelowM0_gammaGrowthConst_third
  set Ups1 : ℝ := C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
      (6 * ((d : ℝ) + 1) ^ 2) with hUps1def
  have hUps1eq : Ups1 = C61 * (64 : ℝ) ^ (6 * ((d : ℝ) + 1) ^ 2) := by clear * - d C61 hKPsi Ups1 hUps1def; rw [hUps1def, hKPsi]
  clear hUps1def hKPsi
  have hUps1pos : 0 < Ups1 := by rw [hUps1eq]; positivity
  set p2 : ℝ := C61 * (4 * Cmix + 4) with hp2def
  have hp2nonneg : 0 ≤ p2 := by clear * - hC61 hCmix p2 hp2def; rw [hp2def]; nlinarith only [hC61, hCmix]
  set U2 : ℝ := C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log 2 + 2 +
      2 * Real.log (8 * Cellip + 2))) with hU2def
  have hU2pos : 0 < U2 := by rw [hU2def]; positivity
  set Cdp : ℝ := 2 * Cd + 4 * Cd ^ 2 with hCdpdef
  have hCdppos : 0 < Cdp := by clear * - hCd1 Cdp hCdpdef; rw [hCdpdef]; nlinarith only [hCd1]
  set A0 : ℝ := 1003 * Cdp * (Ups1 + U2) with hA0def
  have hA0pos : 0 < A0 := by rw [hA0def]; positivity
  set A1 : ℝ := p2 + 5 with hA1def
  have hA0nonneg : 0 ≤ A0 := by
    clear * - A0 hA0pos
    exact hA0pos.le
  have hA1nonneg : 0 ≤ A1 := by clear * - hp2nonneg A1 hA1def; rw [hA1def]; linarith only [hp2nonneg]
  set Az : ℝ := 2 + 4 * Cmix * (A0 + A1) with hAzdef
  have hAzpos : 0 < Az := by
    rw [hAzdef]
    have : (0 : ℝ) ≤ 4 * Cmix * (A0 + A1) := by
      have hCmixnn : (0 : ℝ) ≤ Cmix := by linarith only [hCmix]
      have hsum : (0 : ℝ) ≤ A0 + A1 := by linarith only [hA0nonneg, hA1nonneg]
      positivity
    linarith only [this]
  have hAznonneg : 0 ≤ Az := by
    clear * - Az hAzpos
    exact hAzpos.le
  set Vx : ℝ := 3 * Cdp * Az with hVxdef
  have hVxpos : 0 < Vx := by rw [hVxdef]; positivity
  have hVxnonneg : 0 ≤ Vx := by
    clear * - Vx hVxpos
    exact hVxpos.le
  set Bfinal : ℝ := 32 * C61 * (Cmix + 1) * (A0 + A1) * (Vx + 3) with hBfinaldef
  have hBfinalnonneg : 0 ≤ Bfinal := by
    clear * - C61 hC61 Cmix hCmix A0 A1 hA0nonneg hA1nonneg Vx hVxnonneg Bfinal hBfinaldef
    rw [hBfinaldef]
    have h1 : (0 : ℝ) ≤ 32 * C61 := by linarith only [hC61]
    have h2 : (0 : ℝ) ≤ Cmix + 1 := by linarith only [hCmix]
    have h3 : (0 : ℝ) ≤ A0 + A1 := by linarith only [hA0nonneg, hA1nonneg]
    have h4 : (0 : ℝ) ≤ Vx + 3 := by linarith only [hVxnonneg]
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  refine ⟨max 3000 Bfinal, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro Cprime hCprime M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK
    L hL m hLm
  have hCprime3000 : (3000 : ℝ) ≤ Cprime := by
    clear * - Cprime hCprime
    exact le_trans (le_max_left _ _) hCprime
  have hCprimeBfinal : Bfinal ≤ Cprime := by
    clear * - Bfinal Cprime hCprime
    exact le_trans (le_max_right _ _) hCprime
  clear hCprime
  have hC1000 : (1000 : ℝ) ≤ Cprime := by clear * - Cprime hCprime3000; linarith only [hCprime3000]
  obtain ⟨hL1, hnuinvL, hnuinv2L, hCprimeL⟩ :=
    homogBelowM0_L_controls hC1000 hM hcStar hcStar2 hnu hnu1 hK halpha0 halpha1 hL
  clear hK hcStar2 hcStar halpha1 halpha0 hM
  have hCprime0 : (0 : ℝ) ≤ Cprime := by clear * - Cprime hC1000; linarith only [hC1000]
  -- L ≤ m, in both Nat and real form
  clear hC1000
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by clear * - hL1; exact_mod_cast hL1
  clear hL1
  have hLmR : (L : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hLm
  have hLleMR : (L : ℝ) ≤ (m : ℝ) := by clear * - hL1R hLmR; nlinarith only [hL1R, hLmR]
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by
    clear * - hL1R hLleMR
    exact le_trans hL1R hLleMR
  have hm1 : 1 ≤ m := by clear * - hm1R; exact_mod_cast hm1R
  have hnuinvm : nu⁻¹ ≤ (m : ℝ) := by
    clear * - nu hnuinvL hLleMR
    exact le_trans hnuinvL hLleMR
  clear hnuinvL
  have hnuinv2m : nu⁻¹ ^ 2 ≤ (m : ℝ) := by
    clear * - nu hnuinv2L hLleMR
    exact le_trans hnuinv2L hLleMR
  have hCprimem : Cprime ≤ 1000 * (m : ℝ) := by clear * - Cprime hCprimeL hLleMR; nlinarith only [hCprimeL, hLleMR]
  clear hLleMR hCprimeL
  have hLpos : (0 : ℝ) < (L : ℝ) := by clear * - hL1R; linarith only [hL1R]
  -- force m ≥ 3
  have hm3 : (3 : ℕ) ≤ m := by
    clear * - hCprime3000 hCprimem
    have hstep : (3000 : ℝ) ≤ 1000 * (m : ℝ) := le_trans hCprime3000 hCprimem
    have hm3' : (3 : ℝ) ≤ (m : ℝ) := by linarith only [hstep]
    exact_mod_cast hm3'
  clear hCprime3000
  have hm3' : (3 : ℝ) ≤ (m : ℝ) := by clear * - hm3; exact_mod_cast hm3
  clear hm3
  have hlogm_gt1 : (1 : ℝ) < Real.log (m : ℝ) := by
    clear * - hm3'
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hlt : Real.exp 1 < (m : ℝ) := lt_of_lt_of_le he3 hm3'
    have hh := Real.log_lt_log (Real.exp_pos 1) hlt
    rwa [Real.log_exp] at hh
  have hlogm1 : (1 : ℝ) ≤ Real.log (m : ℝ) := by
    clear * - hlogm_gt1
    exact le_of_lt hlogm_gt1
  clear hlogm_gt1
  have hlogmnn : (0 : ℝ) ≤ Real.log (m : ℝ) := by
    clear * - hlogm1
    exact le_trans (by norm_num) hlogm1
  have hmpos : (0 : ℝ) < (m : ℝ) := by clear * - hm3'; linarith only [hm3']
  -- Upsilon2 bound, in terms of m
  clear hm3'
  have hUps2bound := homogBelowM0_upsilon2_le_pow hC61 hCmix hCellip hnu hm1 hnuinvm hnuinv2m
  clear hnuinv2m hnuinvm hCellip
  rw [← hU2def, ← hp2def] at hUps2bound
  -- m + m0 + 1 bound, in terms of m (instantiate the cube lemma's own L and m both at m)
  clear hU2def hp2def
  have hmm2 : m ≤ m ^ 2 := by clear * - hm1; nlinarith only [hm1]
  have hmm0bound := homogBelowM0_mPlusM0_le_cube hCprime0 hCprimem hm1 hmm2
  -- Theta0 bound: Theta0 ≤ Cdp * L^2 ≤ Cdp * m^2
  clear hmm2 hCprimem hm1 hCprime0
  have hTheta0boundL := homogBelowM0_thetaBound_le_sq
    (by linarith only [hCd1] : (0 : ℝ) ≤ Cd) hnuinv2L
  clear hnuinv2L
  rw [← hCdpdef] at hTheta0boundL
  clear hCdpdef
  have hCdpnn : (0 : ℝ) ≤ Cdp := by
    clear * - Cdp hCdppos
    exact hCdppos.le
  have hLmM2 : (L : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by clear * - hLmR hm1R; nlinarith only [hLmR, hm1R]
  clear hLmR
  have hTheta0bound : (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) ≤ Cdp * (m : ℝ) ^ 2 := by
    clear * - Cd Ups1 p2 U2 Cdp nu hTheta0boundL hCdpnn hLmM2
    have h1 : Cdp * (L : ℝ) ^ 2 ≤ Cdp * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hLmM2 hCdpnn
    linarith only [hTheta0boundL, h1]
  -- Ups1 + Ups2 ≤ (Ups1+U2) * m^p2
  clear hLmM2 hTheta0boundL
  have hmp2ge1 : (1 : ℝ) ≤ (m : ℝ) ^ p2 := by
    clear * - p2 hp2nonneg hm1R
    have h := Real.rpow_le_rpow_of_exponent_le hm1R hp2nonneg
    rwa [Real.rpow_zero] at h
  have hUps1L : Ups1 ≤ Ups1 * (m : ℝ) ^ p2 := by
    clear * - Ups1 hUps1pos p2 hmp2ge1
    have h := mul_le_mul_of_nonneg_left hmp2ge1 hUps1pos.le
    linarith only [h]
  clear hmp2ge1
  have hsum : Ups1 + C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
      2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2)))) ≤
      (Ups1 + U2) * (m : ℝ) ^ p2 := by
    clear * - C61 Cmix Cellip Ups1 p2 U2 nu hUps2bound hUps1L
    have h := add_le_add hUps1L hUps2bound
    nlinarith only [h]
  clear hUps1L hUps2bound
  have hUps2actual_pos : 0 < C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
      2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2)))) := by positivity
  have hsum_pos : 0 < Ups1 + C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
      2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2)))) := by
    clear * - C61 Cmix Cellip Ups1 hUps1pos nu hUps2actual_pos
    linarith only [hUps1pos, hUps2actual_pos]
  have hmm0_nn : (0 : ℝ) ≤ (m : ℝ) + (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) + 1 := by positivity
  have hTheta0actual_nn : (0 : ℝ) ≤ (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) := by
    have hnuinvnn : (0 : ℝ) ≤ nu⁻¹ := by positivity
    have hCdnn : (0 : ℝ) ≤ Cd := by linarith only [hCd1]
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := by linarith only [hLpos]
    positivity
  -- X ≤ (Ups1+U2) * m^p2 * (1003 * m^3) * (Cdp * m^2)
  have hCdpos : 0 < Cd := by clear * - hCd1 Cd; linarith only [hCd1]
  have hTheta0actual_pos : 0 < (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) := by positivity
  have hmm0_pos : 0 < (m : ℝ) + (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) + 1 := by positivity
  have hUps1ge1 : (1 : ℝ) ≤ Ups1 := by
    rw [hUps1eq]
    have hpow1 : (1 : ℝ) ≤ (64 : ℝ) ^ (6 * ((d : ℝ) + 1) ^ 2) := by
      have hdnn : (0 : ℝ) ≤ 6 * ((d : ℝ) + 1) ^ 2 := by positivity
      calc (1 : ℝ) = (64 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 64).symm
        _ ≤ (64 : ℝ) ^ (6 * ((d : ℝ) + 1) ^ 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hdnn
    nlinarith only [hC61, hpow1]
  clear hUps1eq
  have hUps1sum_ge1 : (1 : ℝ) ≤ Ups1 + C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
      2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2)))) := by
    clear * - C61 Cmix Cellip Ups1 nu hUps2actual_pos hUps1ge1
    linarith only [hUps1ge1, hUps2actual_pos]
  clear hUps1ge1
  have hmm0ge1 : (1 : ℝ) ≤ (m : ℝ) + (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) + 1 := by
    clear * - Cprime
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hceilnn : (0 : ℝ) ≤ (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith only [hmnn, hceilnn]
  have hTheta0ge1 : (1 : ℝ) ≤ (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) := by
    clear * - hCd1 Cd nu hnu hnu1 hL1R
    have h1 : (1 : ℝ) ≤ 2 * Cd + 4 * Cd ^ 2 := by nlinarith only [hCd1]
    have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
    have h2 : (1 : ℝ) ≤ nu⁻¹ ^ 2 := by nlinarith only [hnuinv1]
    have h12 : (1 : ℝ) ≤ (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 := by
      nlinarith only [h1, h2, mul_nonneg (by linarith only [h1] : (0 : ℝ) ≤ 2 * Cd + 4 * Cd ^ 2 - 1)
        (by linarith only [h2] : (0 : ℝ) ≤ nu⁻¹ ^ 2 - 1)]
    nlinarith only [h12, hL1R, mul_nonneg (by linarith only [h12] : (0 : ℝ) ≤
      (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 - 1) (by linarith only [hL1R] : (0 : ℝ) ≤ (L : ℝ) - 1)]
  clear hL1R hnu1 hnu hCd1
  generalize hS1def : (Ups1 + C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) + 2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2))))) = S1 at hsum hsum_pos hUps1sum_ge1 ⊢
  generalize hMqdef : ((m : ℝ) + (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) + 1) = Mq at hmm0bound hmm0_nn hmm0ge1 hmm0_pos ⊢
  generalize hThdef : ((2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ)) = Th at hTheta0bound hTheta0actual_nn hTheta0actual_pos hTheta0ge1 ⊢
  have hXbound : S1 *
      Mq *
      Th ≤
      (Ups1 + U2) * (m : ℝ) ^ p2 * (1003 * (m : ℝ) ^ 3) * (Cdp * (m : ℝ) ^ 2) := by
    have hRHS1nn : (0 : ℝ) ≤ (Ups1 + U2) * (m : ℝ) ^ p2 := by positivity
    have step1 : S1 *
        Mq ≤
        (Ups1 + U2) * (m : ℝ) ^ p2 * (1003 * (m : ℝ) ^ 3) :=
      mul_le_mul hsum hmm0bound hmm0_nn hRHS1nn
    have hRHS2nn : (0 : ℝ) ≤ (Ups1 + U2) * (m : ℝ) ^ p2 * (1003 * (m : ℝ) ^ 3) := by positivity
    have step2 := mul_le_mul step1 hTheta0bound hTheta0actual_nn hRHS2nn
    nlinarith only [step2]
  clear hsum hmm0bound
  have hXpos : 0 < S1 *
      Mq *
      Th := by
    clear * - hsum_pos hTheta0actual_pos hmm0_pos
    exact mul_pos (mul_pos hsum_pos hmm0_pos) hTheta0actual_pos
  have hRHSeq : (Ups1 + U2) * (m : ℝ) ^ p2 * (1003 * (m : ℝ) ^ 3) * (Cdp * (m : ℝ) ^ 2) =
      A0 * ((m : ℝ) ^ p2 * (m : ℝ) ^ (3 : ℕ) * (m : ℝ) ^ (2 : ℕ)) := by clear * - Ups1 p2 U2 Cdp A0 hA0def; rw [hA0def]; ring
  clear hA0def
  rw [hRHSeq] at hXbound
  clear hRHSeq
  have hRHSpos : 0 < A0 * ((m : ℝ) ^ p2 * (m : ℝ) ^ (3 : ℕ) * (m : ℝ) ^ (2 : ℕ)) := by
    have h1 : (0 : ℝ) < (m : ℝ) ^ p2 := Real.rpow_pos_of_pos hmpos _
    positivity
  have hlogXbound : Real.log (S1 *
      Mq *
      Th) ≤ A0 + A1 * Real.log (m : ℝ) := by
    have hstep := Real.log_le_log hXpos hXbound
    have hlogPow : Real.log ((m : ℝ) ^ p2 * (m : ℝ) ^ (3 : ℕ) * (m : ℝ) ^ (2 : ℕ)) =
        p2 * Real.log (m : ℝ) + ((3 : ℕ) * Real.log (m : ℝ) + (2 : ℕ) * Real.log (m : ℝ)) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (Real.rpow_pos_of_pos hmpos _).ne' (by positivity),
        Real.log_rpow hmpos, Real.log_pow, Real.log_pow]
      ring
    have hlogProd : Real.log (A0 * ((m : ℝ) ^ p2 * (m : ℝ) ^ (3 : ℕ) * (m : ℝ) ^ (2 : ℕ))) =
        Real.log A0 + Real.log ((m : ℝ) ^ p2 * (m : ℝ) ^ (3 : ℕ) * (m : ℝ) ^ (2 : ℕ)) :=
      Real.log_mul hA0pos.ne' (by positivity)
    have hlogRHS : Real.log (A0 * ((m : ℝ) ^ p2 * (m : ℝ) ^ (3 : ℕ) * (m : ℝ) ^ (2 : ℕ))) =
        Real.log A0 + (p2 * Real.log (m : ℝ) + ((3 : ℕ) * Real.log (m : ℝ) +
          (2 : ℕ) * Real.log (m : ℝ))) := by rw [hlogProd, hlogPow]
    rw [hlogRHS] at hstep
    have hlogA0le : Real.log A0 ≤ A0 := by
      have h := Real.log_le_sub_one_of_pos hA0pos
      linarith only [h]
    have heqA1 : p2 * Real.log (m : ℝ) + ((3 : ℕ) * Real.log (m : ℝ) + (2 : ℕ) * Real.log (m : ℝ)) =
        A1 * Real.log (m : ℝ) := by
      rw [hA1def]; push_cast; ring
    rw [heqA1] at hstep
    linarith only [hstep, hlogA0le]
  -- the second log's argument
  clear hXbound hA1def
  have hlogmleM : Real.log (m : ℝ) ≤ (m : ℝ) := by
    clear * - hmpos
    have h := Real.log_le_sub_one_of_pos hmpos
    linarith only [h]
  have hlogXbound2 : Real.log (S1 *
      Mq *
      Th) ≤ (A0 + A1) * (m : ℝ) := by
    clear * - A0 A1 hA0nonneg hA1nonneg hm1R hlogXbound hlogmleM
    have h2 : A1 * Real.log (m : ℝ) ≤ A1 * (m : ℝ) := mul_le_mul_of_nonneg_left hlogmleM hA1nonneg
    have h3 : A0 + A1 * (m : ℝ) ≤ (A0 + A1) * (m : ℝ) := by nlinarith only [hA0nonneg, hm1R]
    linarith only [hlogXbound, h2, h3]
  clear hlogmleM
  have hargBound : 2 + 4 * Cmix * Real.log (S1 *
      Mq *
      Th) ≤ Az * (m : ℝ) := by
    clear * - Cmix hCmix A0 A1 Az hAzdef hm1R hlogXbound2
    have hCmixnn : (0 : ℝ) ≤ 4 * Cmix := by linarith only [hCmix]
    have h1 : 4 * Cmix * Real.log (S1 *
        Mq *
        Th) ≤ 4 * Cmix * ((A0 + A1) * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogXbound2 hCmixnn
    rw [hAzdef]
    nlinarith only [h1, hm1R]
  clear hlogXbound2 hm1R hAzdef
  have hABge1 : (1 : ℝ) ≤ S1 *
      Mq := by
    clear * - hUps1sum_ge1 hmm0ge1
    nlinarith only [hUps1sum_ge1, hmm0ge1,
      mul_nonneg (by linarith only [hUps1sum_ge1] : (0 : ℝ) ≤
        S1 - 1)
        (by linarith only [hmm0ge1] : (0 : ℝ) ≤
          Mq - 1)]
  clear hmm0ge1 hUps1sum_ge1
  have hXge1 : (1 : ℝ) ≤ S1 *
      Mq *
      Th := by
    clear * - hTheta0ge1 hABge1
    nlinarith only [hABge1, hTheta0ge1,
      mul_nonneg (by linarith only [hABge1] : (0 : ℝ) ≤ S1 *
        Mq - 1)
        (by linarith only [hTheta0ge1] : (0 : ℝ) ≤ Th - 1)]
  clear hABge1
  have hlogXnn : (0 : ℝ) ≤ Real.log (S1 *
      Mq *
      Th) := by
    clear * - hXge1
    exact Real.log_nonneg hXge1
  clear hXge1
  have hargnn : (0 : ℝ) ≤ 2 + 4 * Cmix * Real.log (S1 *
      Mq *
      Th) := by
    clear * - Cmix hCmix hlogXnn
    have hCmixnn : (0 : ℝ) ≤ Cmix := by linarith only [hCmix]
    nlinarith only [hlogXnn, hCmixnn]
  have hCdpM2nn : (0 : ℝ) ≤ Cdp * (m : ℝ) ^ 2 := by positivity
  have hprodstep : Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th)) ≤
      (Cdp * (m : ℝ) ^ 2) * (Az * (m : ℝ)) := by
    clear * - Cmix Cdp Az hTheta0bound hargBound hargnn hCdpM2nn
    exact mul_le_mul hTheta0bound hargBound hargnn hCdpM2nn
  clear hargBound hTheta0bound
  have hprodbound : 3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th)) ≤ Vx * (m : ℝ) ^ 3 := by
    clear * - Cmix Vx hVxdef hprodstep
    rw [hVxdef]
    nlinarith only [hprodstep]
  clear hprodstep hVxdef
  have hprodpos : 0 < 3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th)) := by
    clear * - Cmix hCmix hTheta0actual_pos hlogXnn
    have h2 : (0 : ℝ) < 2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th) := by
      have hCmixnn : (0 : ℝ) ≤ Cmix := by linarith only [hCmix]
      nlinarith only [hlogXnn, hCmixnn]
    have h3 : (0 : ℝ) < 3 * Th := by
      linarith only [hTheta0actual_pos]
    exact mul_pos h3 h2
  have hVxM3pos : 0 < Vx * (m : ℝ) ^ 3 := by positivity
  have hlog2bound : Real.log (3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th))) ≤ Vx + 3 * Real.log (m : ℝ) := by
    have hstep := Real.log_le_log hprodpos hprodbound
    have hlogVxM3 : Real.log (Vx * (m : ℝ) ^ 3) = Real.log Vx + 3 * Real.log (m : ℝ) := by
      rw [Real.log_mul hVxpos.ne' (by positivity)]
      rw [Real.log_pow]
      push_cast; ring
    rw [hlogVxM3] at hstep
    have hlogVxle : Real.log Vx ≤ Vx := by
      have h := Real.log_le_sub_one_of_pos hVxpos
      linarith only [h]
    linarith only [hstep, hlogVxle]
  -- final assembly
  clear hprodbound
  have hargge2 : (2 : ℝ) ≤ 2 + 4 * Cmix * Real.log (S1 *
      Mq *
      Th) := by
    clear * - Cmix hCmix hlogXnn
    have hCmixnn : (0 : ℝ) ≤ Cmix := by linarith only [hCmix]
    nlinarith only [hlogXnn, hCmixnn]
  have h3Theta0ge3 : (3 : ℝ) ≤ 3 * Th := by
    clear * - hTheta0ge1
    linarith only [hTheta0ge1]
  clear hTheta0ge1
  have hprod_ge1 : (1 : ℝ) ≤ 3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th)) := by
    clear * - Cmix hargge2 h3Theta0ge3
    nlinarith only [h3Theta0ge3, hargge2,
      mul_nonneg (by linarith only [h3Theta0ge3] : (0 : ℝ) ≤
        3 * Th - 3)
        (by linarith only [hargge2] : (0 : ℝ) ≤
          2 + 4 * Cmix * Real.log (S1 *
            Mq *
            Th) - 2)]
  clear h3Theta0ge3 hargge2
  have hlog2nn : (0 : ℝ) ≤ Real.log (3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th))) := by
    clear * - Cmix hprod_ge1
    exact Real.log_nonneg hprod_ge1
  clear hprod_ge1
  have hlogXle2 : Real.log (S1 *
      Mq *
      Th) ≤ (A0 + A1) * Real.log (m : ℝ) := by
    clear * - A0 A1 hA0nonneg hlogm1 hlogXbound
    have h1 : A0 ≤ A0 * Real.log (m : ℝ) := by nlinarith only [hA0nonneg, hlogm1]
    nlinarith only [hlogXbound, h1]
  clear hlogXbound
  have hlog2le2 : Real.log (3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th))) ≤ (Vx + 3) * Real.log (m : ℝ) := by
    clear * - Cmix Vx hVxnonneg hlogm1 hlog2bound
    have h1 : Vx ≤ Vx * Real.log (m : ℝ) := by nlinarith only [hVxnonneg, hlogm1]
    nlinarith only [hlog2bound, h1]
  clear hlog2bound hlogm1
  have hRHSprodnn : (0 : ℝ) ≤ (A0 + A1) * Real.log (m : ℝ) := by
    clear * - A0 A1 hA0nonneg hA1nonneg hlogmnn
    nlinarith only [hA0nonneg, hA1nonneg, hlogmnn]
  have hprodfinal : Real.log (S1 *
      Mq *
      Th) *
    Real.log (3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th))) ≤
      (A0 + A1) * (Vx + 3) * (Real.log (m : ℝ)) ^ 2 := by
    clear * - Cmix A0 A1 Vx hlog2nn hlogXle2 hlog2le2 hRHSprodnn
    have hstep := mul_le_mul hlogXle2 hlog2le2 hlog2nn hRHSprodnn
    calc Real.log (S1 *
        Mq *
        Th) *
      Real.log (3 * Th *
        (2 + 4 * Cmix * Real.log (S1 *
          Mq *
          Th))) ≤
        (A0 + A1) * Real.log (m : ℝ) * ((Vx + 3) * Real.log (m : ℝ)) := hstep
      _ = (A0 + A1) * (Vx + 3) * (Real.log (m : ℝ)) ^ 2 := by ring
  clear hlog2le2 hlogXle2
  have hPrefnn : (0 : ℝ) ≤ 32 * C61 * (Cmix + 1) := by clear * - C61 hC61 Cmix hCmix; nlinarith only [hC61, hCmix]
  clear hCmix hC61
  have hfinal : 32 * C61 * (Cmix + 1) *
      Real.log (S1 *
        Mq *
        Th) *
      Real.log (3 * Th *
        (2 + 4 * Cmix * Real.log (S1 *
          Mq *
          Th))) ≤
      Bfinal * (Real.log (m : ℝ)) ^ 2 := by
    clear * - C61 Cmix A0 A1 Vx Bfinal hBfinaldef hprodfinal hPrefnn
    rw [hBfinaldef]
    calc 32 * C61 * (Cmix + 1) *
        Real.log (S1 *
          Mq *
          Th) *
        Real.log (3 * Th *
          (2 + 4 * Cmix * Real.log (S1 *
            Mq *
            Th))) =
        32 * C61 * (Cmix + 1) *
          (Real.log (S1 *
            Mq *
            Th) *
          Real.log (3 * Th *
            (2 + 4 * Cmix * Real.log (S1 *
              Mq *
              Th)))) := by ring
      _ ≤ 32 * C61 * (Cmix + 1) * ((A0 + A1) * (Vx + 3) * (Real.log (m : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hprodfinal hPrefnn
      _ = 32 * C61 * (Cmix + 1) * (A0 + A1) * (Vx + 3) * (Real.log (m : ℝ)) ^ 2 := by ring
  clear hprodfinal hBfinaldef
  have hCprimelog2nn : (0 : ℝ) ≤ (Real.log (m : ℝ)) ^ 2 := sq_nonneg _
  have hfinal2 : Bfinal * (Real.log (m : ℝ)) ^ 2 ≤ Cprime * (Real.log (m : ℝ)) ^ 2 := by
    clear * - Bfinal Cprime hCprimeBfinal hCprimelog2nn
    exact mul_le_mul_of_nonneg_right hCprimeBfinal hCprimelog2nn
  clear hCprimeBfinal
  have hceil : Cprime * Real.log (m : ℝ) ^ 2 ≤ (⌈Cprime * Real.log (m : ℝ) ^ 2⌉₊ : ℝ) := by
    clear * - Cprime
    exact Nat.le_ceil _
  exact le_trans (le_trans hfinal hfinal2) hceil

end SuperdiffusionCLT.Section4.HomogBelow
