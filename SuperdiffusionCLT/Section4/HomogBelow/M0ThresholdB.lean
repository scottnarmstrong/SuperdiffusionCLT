/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.M0Threshold

/-!
The `m₀` startup-scale threshold of `p.homog.below` Step 1, specialized against the form of
[AK, Theorem 6.1] recorded as `SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`, at the
parameter choice `D := 1, β := γ := 1/2, L₁ := 4·Cmix, L₂ := ν⁻¹,
H := 8·Cellip·ν⁻²`, with `K_{Ψ_S} = 2` exact and `K_Ψ := gammaGrowthConst(1/3)
= 64` exact (`homogBelowM0_gammaGrowthConst_third`), `d ≥ 2` collapsing both
`min`-denominators to `1`, and `Θ₀` replaced by its proved upper bound
`(2Cenv(d)+4Cenv(d)²)·ν⁻²·L` (`Section4/HomogBelow/ThetaLmThetaZero.lean`).

The constants have separate roles. Using a single constant `C` for the constant of [AK,
Theorem 6.1], the `m₀` coefficient and the `L₀` threshold constant would make the naive
statement false (see the module docstring of `M0Threshold.lean`).
This file separates `C₆₁` (the constant of [AK, Theorem 6.1] -- fixed first, arbitrary) from
`Cprime` (the shared `m₀`/`L₀` constant `C'` -- chosen large depending on
`C₆₁, Cmix, Cellip, d`), and bounds the input scale `m ≤ L²`.

The proof uses `homogBelowM0_L_controls` to get `ν⁻¹ ≤ L`, `ν⁻¹² ≤ L`,
`1 ≤ L`, `Cprime ≤ 1000L` from `L ≥ lNaught Cprime ...`; forces `L ≥ 3`
(hence `log L > 1`) by choosing `Cprime ≥ 3000`; bounds `Υ₂` by a fixed
power of `L` (`homogBelowM0_upsilon2_le_pow`); bounds `m+m₀+1` and `Θ₀`'s
upper bound by fixed powers of `L` (`homogBelowM0_mPlusM0_le_cube`,
`homogBelowM0_thetaBound_le_sq`); and assembles `log X` and the second log
into `(constant) + (constant)·log L` bounds, giving the whole left side
`≤ Bfinal·log²L` for an explicit constant `Bfinal` depending only on
`(C₆₁, Cmix, Cellip, d)`, absorbed once `Cprime ≥ Bfinal`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- **The corrected `m₀`-threshold theorem** (with the quantifiers in the
right order): `C₆₁` (the constant of [AK, Theorem 6.1]) is fixed first and
arbitrary; `C₀` is then chosen depending on `(C₆₁, Cmix, Cellip, d)`; for
every `Cprime ≥ C₀` playing both the `lNaught`/`L₀` role and the `m₀ :=
⌈Cprime·log²L⌉₊` coefficient, and every `L` with `L ≥ lNaught Cprime M alpha
cStar nu K` and every `m ≤ L²`, the `m₀`-threshold display (with `D=1,
β=γ=1/2, L₁=4Cmix, L₂=ν⁻¹, H=8·Cellip·ν⁻², K_{Ψ_S}=2, K_Ψ=gammaGrowthConst(1/3),
min-denominators=1`, and `Θ₀` replaced by its proved upper bound
`(2Cenv(d)+4Cenv(d)²)ν⁻²L`) holds with `≤ m₀`. -/
theorem homogBelowM0_threshold_corrected :
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
      ∀ m : ℕ, m ≤ L ^ 2 →
        32 * C61 * (Cmix + 1) *
          Real.log
            ((C61 * (Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3)) ^
                    (6 * ((d : ℝ) + 1) ^ 2) +
                C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
                  2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2))))) *
              ((m : ℝ) + (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + 1) *
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
                    ((m : ℝ) + (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + 1) *
                    ((2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
                          4 * (SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) ^
                            2) *
                      nu⁻¹ ^ 2 * (L : ℝ))))) ≤
          (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) := by
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
    L hL m hm
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
  have hL3 : (3 : ℕ) ≤ L := by
    clear * - hCprime3000 hCprimeL
    have hstep : (3000 : ℝ) ≤ 1000 * (L : ℝ) := le_trans hCprime3000 hCprimeL
    have hL3' : (3 : ℝ) ≤ (L : ℝ) := by linarith only [hstep]
    exact_mod_cast hL3'
  clear hCprime3000
  have hL3' : (3 : ℝ) ≤ (L : ℝ) := by clear * - hL3; exact_mod_cast hL3
  clear hL3
  have hlogL_gt1 : (1 : ℝ) < Real.log (L : ℝ) := by
    clear * - hL3'
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hlt : Real.exp 1 < (L : ℝ) := lt_of_lt_of_le he3 hL3'
    have hh := Real.log_lt_log (Real.exp_pos 1) hlt
    rwa [Real.log_exp] at hh
  have hlogL1 : (1 : ℝ) ≤ Real.log (L : ℝ) := by
    clear * - hlogL_gt1
    exact le_of_lt hlogL_gt1
  clear hlogL_gt1
  have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) := by
    clear * - hlogL1
    exact le_trans (by norm_num) hlogL1
  have hLpos : (0 : ℝ) < (L : ℝ) := by clear * - hL3'; linarith only [hL3']
  have hCprime0 : (0 : ℝ) ≤ Cprime := by clear * - Cprime hC1000; linarith only [hC1000]
  -- Upsilon2 bound
  clear hC1000
  have hUps2bound := homogBelowM0_upsilon2_le_pow hC61 hCmix hCellip hnu hL1 hnuinvL hnuinv2L
  clear hnuinvL hCellip
  rw [← hU2def, ← hp2def] at hUps2bound
  -- m + m0 + 1 bound
  clear hU2def hp2def
  have hmm0bound := homogBelowM0_mPlusM0_le_cube hCprime0 hCprimeL hL1 hm
  -- Theta0 bound
  clear hCprime0 hCprimeL hL1
  have hTheta0bound := homogBelowM0_thetaBound_le_sq
    (by linarith only [hCd1] : (0 : ℝ) ≤ Cd) hnuinv2L
  clear hnuinv2L
  rw [← hCdpdef] at hTheta0bound
  -- Ups1 + Ups2 ≤ (Ups1+U2) * L^p2
  clear hCdpdef
  have hL1'' : (1 : ℝ) ≤ (L : ℝ) := by
    clear * - hL3'
    exact le_trans (by norm_num) hL3'
  clear hL3'
  have hLp2ge1 : (1 : ℝ) ≤ (L : ℝ) ^ p2 := by
    clear * - p2 hp2nonneg hL1''
    have h := Real.rpow_le_rpow_of_exponent_le hL1'' hp2nonneg
    rwa [Real.rpow_zero] at h
  have hUps1L : Ups1 ≤ Ups1 * (L : ℝ) ^ p2 := by
    clear * - Ups1 hUps1pos p2 hLp2ge1
    have h := mul_le_mul_of_nonneg_left hLp2ge1 hUps1pos.le
    linarith only [h]
  clear hLp2ge1
  have hsum : Ups1 + C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) +
      2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2)))) ≤
      (Ups1 + U2) * (L : ℝ) ^ p2 := by
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
  have hmm0_nn : (0 : ℝ) ≤ (m : ℝ) + (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + 1 := by positivity
  have hTheta0actual_nn : (0 : ℝ) ≤ (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) := by
    have hnuinvnn : (0 : ℝ) ≤ nu⁻¹ := by positivity
    have hCdnn : (0 : ℝ) ≤ Cd := by linarith only [hCd1]
    have hLnn : (0 : ℝ) ≤ (L : ℝ) := by linarith only [hLpos]
    positivity
  -- X ≤ (Ups1+U2) * L^p2 * (1003 * L^3) * (Cdp * L^2)
  have hCdpos : 0 < Cd := by clear * - hCd1 Cd; linarith only [hCd1]
  have hTheta0actual_pos : 0 < (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) := by positivity
  have hmm0_pos : 0 < (m : ℝ) + (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + 1 := by positivity
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
  have hmm0ge1 : (1 : ℝ) ≤ (m : ℝ) + (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + 1 := by
    clear * - Cprime
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hceilnn : (0 : ℝ) ≤ (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith only [hmnn, hceilnn]
  have hTheta0ge1 : (1 : ℝ) ≤ (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ) := by
    clear * - hCd1 Cd nu hnu hnu1 hL1''
    have h1 : (1 : ℝ) ≤ 2 * Cd + 4 * Cd ^ 2 := by nlinarith only [hCd1]
    have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
    have h2 : (1 : ℝ) ≤ nu⁻¹ ^ 2 := by nlinarith only [hnuinv1]
    have h12 : (1 : ℝ) ≤ (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 := by
      nlinarith only [h1, h2, mul_nonneg (by linarith only [h1] : (0 : ℝ) ≤ 2 * Cd + 4 * Cd ^ 2 - 1)
        (by linarith only [h2] : (0 : ℝ) ≤ nu⁻¹ ^ 2 - 1)]
    nlinarith only [h12, hL1'', mul_nonneg (by linarith only [h12] : (0 : ℝ) ≤
      (2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 - 1) (by linarith only [hL1''] : (0 : ℝ) ≤ (L : ℝ) - 1)]
  clear hnu1 hnu hCd1
  generalize hS1def : (Ups1 + C61 * Real.exp (C61 * ((4 * Cmix + 2) * Real.log (2 * nu⁻¹) + 2 * (1 + Real.log (8 * Cellip * nu⁻¹ ^ 2 + 2))))) = S1 at hsum hsum_pos hUps1sum_ge1 ⊢
  generalize hMqdef : ((m : ℝ) + (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) + 1) = Mq at hmm0bound hmm0_nn hmm0ge1 hmm0_pos ⊢
  generalize hThdef : ((2 * Cd + 4 * Cd ^ 2) * nu⁻¹ ^ 2 * (L : ℝ)) = Th at hTheta0bound hTheta0actual_nn hTheta0actual_pos hTheta0ge1 ⊢
  have hXbound : S1 *
      Mq *
      Th ≤
      (Ups1 + U2) * (L : ℝ) ^ p2 * (1003 * (L : ℝ) ^ 3) * (Cdp * (L : ℝ) ^ 2) := by
    have hRHS1nn : (0 : ℝ) ≤ (Ups1 + U2) * (L : ℝ) ^ p2 := by positivity
    have step1 : S1 *
        Mq ≤
        (Ups1 + U2) * (L : ℝ) ^ p2 * (1003 * (L : ℝ) ^ 3) :=
      mul_le_mul hsum hmm0bound hmm0_nn hRHS1nn
    have hRHS2nn : (0 : ℝ) ≤ (Ups1 + U2) * (L : ℝ) ^ p2 * (1003 * (L : ℝ) ^ 3) := by positivity
    have step2 := mul_le_mul step1 hTheta0bound hTheta0actual_nn hRHS2nn
    nlinarith only [step2]
  clear hsum hmm0bound
  have hXpos : 0 < S1 *
      Mq *
      Th := by
    clear * - hsum_pos hTheta0actual_pos hmm0_pos
    exact mul_pos (mul_pos hsum_pos hmm0_pos) hTheta0actual_pos
  have hRHSeq : (Ups1 + U2) * (L : ℝ) ^ p2 * (1003 * (L : ℝ) ^ 3) * (Cdp * (L : ℝ) ^ 2) =
      A0 * ((L : ℝ) ^ p2 * (L : ℝ) ^ (3 : ℕ) * (L : ℝ) ^ (2 : ℕ)) := by clear * - Ups1 p2 U2 Cdp A0 hA0def; rw [hA0def]; ring
  clear hA0def
  rw [hRHSeq] at hXbound
  clear hRHSeq
  have hRHSpos : 0 < A0 * ((L : ℝ) ^ p2 * (L : ℝ) ^ (3 : ℕ) * (L : ℝ) ^ (2 : ℕ)) := by
    have h1 : (0 : ℝ) < (L : ℝ) ^ p2 := Real.rpow_pos_of_pos hLpos _
    positivity
  have hlogXbound : Real.log (S1 *
      Mq *
      Th) ≤ A0 + A1 * Real.log (L : ℝ) := by
    have hstep := Real.log_le_log hXpos hXbound
    have hlogPow : Real.log ((L : ℝ) ^ p2 * (L : ℝ) ^ (3 : ℕ) * (L : ℝ) ^ (2 : ℕ)) =
        p2 * Real.log (L : ℝ) + ((3 : ℕ) * Real.log (L : ℝ) + (2 : ℕ) * Real.log (L : ℝ)) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (Real.rpow_pos_of_pos hLpos _).ne' (by positivity),
        Real.log_rpow hLpos, Real.log_pow, Real.log_pow]
      ring
    have hlogProd : Real.log (A0 * ((L : ℝ) ^ p2 * (L : ℝ) ^ (3 : ℕ) * (L : ℝ) ^ (2 : ℕ))) =
        Real.log A0 + Real.log ((L : ℝ) ^ p2 * (L : ℝ) ^ (3 : ℕ) * (L : ℝ) ^ (2 : ℕ)) :=
      Real.log_mul hA0pos.ne' (by positivity)
    have hlogRHS : Real.log (A0 * ((L : ℝ) ^ p2 * (L : ℝ) ^ (3 : ℕ) * (L : ℝ) ^ (2 : ℕ))) =
        Real.log A0 + (p2 * Real.log (L : ℝ) + ((3 : ℕ) * Real.log (L : ℝ) +
          (2 : ℕ) * Real.log (L : ℝ))) := by rw [hlogProd, hlogPow]
    rw [hlogRHS] at hstep
    have hlogA0le : Real.log A0 ≤ A0 := by
      have h := Real.log_le_sub_one_of_pos hA0pos
      linarith only [h]
    have heqA1 : p2 * Real.log (L : ℝ) + ((3 : ℕ) * Real.log (L : ℝ) + (2 : ℕ) * Real.log (L : ℝ)) =
        A1 * Real.log (L : ℝ) := by
      rw [hA1def]; push_cast; ring
    rw [heqA1] at hstep
    linarith only [hstep, hlogA0le]
  -- the second log's argument
  clear hXbound hA1def
  have hlogLleL : Real.log (L : ℝ) ≤ (L : ℝ) := by
    clear * - hLpos
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith only [h]
  have hlogXbound2 : Real.log (S1 *
      Mq *
      Th) ≤ (A0 + A1) * (L : ℝ) := by
    clear * - A0 A1 hA0nonneg hA1nonneg hL1'' hlogXbound hlogLleL
    have h2 : A1 * Real.log (L : ℝ) ≤ A1 * (L : ℝ) := mul_le_mul_of_nonneg_left hlogLleL hA1nonneg
    have h3 : A0 + A1 * (L : ℝ) ≤ (A0 + A1) * (L : ℝ) := by nlinarith only [hA0nonneg, hL1'']
    linarith only [hlogXbound, h2, h3]
  clear hlogLleL
  have hargBound : 2 + 4 * Cmix * Real.log (S1 *
      Mq *
      Th) ≤ Az * (L : ℝ) := by
    clear * - Cmix hCmix A0 A1 Az hAzdef hL1'' hlogXbound2
    have hCmixnn : (0 : ℝ) ≤ 4 * Cmix := by linarith only [hCmix]
    have h1 : 4 * Cmix * Real.log (S1 *
        Mq *
        Th) ≤ 4 * Cmix * ((A0 + A1) * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogXbound2 hCmixnn
    rw [hAzdef]
    nlinarith only [h1, hL1'']
  clear hlogXbound2 hL1'' hAzdef
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
  have hTheta0le : Th ≤ Cdp * (L : ℝ) ^ 2 := by
    clear * - Cdp hTheta0bound
    exact hTheta0bound
  clear hTheta0bound
  have hCdpL2nn : (0 : ℝ) ≤ Cdp * (L : ℝ) ^ 2 := by positivity
  have hprodstep : Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th)) ≤
      (Cdp * (L : ℝ) ^ 2) * (Az * (L : ℝ)) := by
    clear * - Cmix Cdp Az hargBound hargnn hTheta0le hCdpL2nn
    exact mul_le_mul hTheta0le hargBound hargnn hCdpL2nn
  clear hTheta0le hargBound
  have hprodbound : 3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th)) ≤ Vx * (L : ℝ) ^ 3 := by
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
  have hVxL3pos : 0 < Vx * (L : ℝ) ^ 3 := by positivity
  have hlog2bound : Real.log (3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th))) ≤ Vx + 3 * Real.log (L : ℝ) := by
    have hstep := Real.log_le_log hprodpos hprodbound
    have hlogVxL3 : Real.log (Vx * (L : ℝ) ^ 3) = Real.log Vx + 3 * Real.log (L : ℝ) := by
      rw [Real.log_mul hVxpos.ne' (by positivity)]
      rw [Real.log_pow]
      push_cast; ring
    rw [hlogVxL3] at hstep
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
      Th) ≤ (A0 + A1) * Real.log (L : ℝ) := by
    clear * - A0 A1 hA0nonneg hlogL1 hlogXbound
    have h1 : A0 ≤ A0 * Real.log (L : ℝ) := by nlinarith only [hA0nonneg, hlogL1]
    nlinarith only [hlogXbound, h1]
  clear hlogXbound
  have hlog2le2 : Real.log (3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th))) ≤ (Vx + 3) * Real.log (L : ℝ) := by
    clear * - Cmix Vx hVxnonneg hlogL1 hlog2bound
    have h1 : Vx ≤ Vx * Real.log (L : ℝ) := by nlinarith only [hVxnonneg, hlogL1]
    nlinarith only [hlog2bound, h1]
  clear hlog2bound hlogL1
  have hRHSprodnn : (0 : ℝ) ≤ (A0 + A1) * Real.log (L : ℝ) := by
    clear * - A0 A1 hA0nonneg hA1nonneg hlogLnn
    nlinarith only [hA0nonneg, hA1nonneg, hlogLnn]
  have hprodfinal : Real.log (S1 *
      Mq *
      Th) *
    Real.log (3 * Th *
      (2 + 4 * Cmix * Real.log (S1 *
        Mq *
        Th))) ≤
      (A0 + A1) * (Vx + 3) * (Real.log (L : ℝ)) ^ 2 := by
    clear * - Cmix A0 A1 Vx hlog2nn hlogXle2 hlog2le2 hRHSprodnn
    have hstep := mul_le_mul hlogXle2 hlog2le2 hlog2nn hRHSprodnn
    calc Real.log (S1 *
        Mq *
        Th) *
      Real.log (3 * Th *
        (2 + 4 * Cmix * Real.log (S1 *
          Mq *
          Th))) ≤
        (A0 + A1) * Real.log (L : ℝ) * ((Vx + 3) * Real.log (L : ℝ)) := hstep
      _ = (A0 + A1) * (Vx + 3) * (Real.log (L : ℝ)) ^ 2 := by ring
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
      Bfinal * (Real.log (L : ℝ)) ^ 2 := by
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
      _ ≤ 32 * C61 * (Cmix + 1) * ((A0 + A1) * (Vx + 3) * (Real.log (L : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hprodfinal hPrefnn
      _ = 32 * C61 * (Cmix + 1) * (A0 + A1) * (Vx + 3) * (Real.log (L : ℝ)) ^ 2 := by ring
  clear hprodfinal hBfinaldef
  have hCprimelog2nn : (0 : ℝ) ≤ (Real.log (L : ℝ)) ^ 2 := sq_nonneg _
  have hfinal2 : Bfinal * (Real.log (L : ℝ)) ^ 2 ≤ Cprime * (Real.log (L : ℝ)) ^ 2 := by
    clear * - Bfinal Cprime hCprimeBfinal hCprimelog2nn
    exact mul_le_mul_of_nonneg_right hCprimeBfinal hCprimelog2nn
  clear hCprimeBfinal
  have hceil : Cprime * Real.log (L : ℝ) ^ 2 ≤ (⌈Cprime * Real.log (L : ℝ) ^ 2⌉₊ : ℝ) := by
    clear * - Cprime
    exact Nat.le_ceil _
  exact le_trans (le_trans hfinal hfinal2) hceil

/-- **The `m₀`-threshold's left side is monotone in `Θ₀ ≥ 1`**, with
`Ups12` standing for `Υ₁+Υ₂ ≥ 1` and `mm0` for `m+m₀+1 ≥ 1`: increasing
`Θ₀` (holding every other parameter fixed) only increases
`32·C₆₁·(Cmix+1)·log(Ups12·mm0·Θ₀)·log(3Θ₀(2+4Cmix·log(Ups12·mm0·Θ₀)))`.
Combined with `homogBelowM0_threshold_corrected` (proved at the specific
value `Θ₀ := (2Cenv(d)+4Cenv(d)²)ν⁻²L`) and the proved upper bound
`Θ₀ ≤ (2Cenv(d)+4Cenv(d)²)ν⁻²L` on the *actual* ellipticity ratio
(`Section4/HomogBelow/ThetaLmThetaZero.lean`,
`homogBelow_thetaCutoff_zero_le`), a downstream consumer gets the
threshold at the actual `Θ₀` once `1 ≤ Θ₀`. -/
theorem homogBelowM0_monotone_in_Theta0
    {C61 Cmix Ups12 mm0 Theta0 Theta0' : ℝ}
    (hC61 : 1 ≤ C61) (hCmix : 1 ≤ Cmix)
    (hUps12ge1 : 1 ≤ Ups12) (hmm0ge1 : 1 ≤ mm0)
    (hTheta0ge1 : 1 ≤ Theta0) (hTheta0le : Theta0 ≤ Theta0') :
    32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * mm0 * Theta0) *
        Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) ≤
      32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * mm0 * Theta0') *
        Real.log (3 * Theta0' * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0'))) := by
  have hTheta0pos : (0 : ℝ) < Theta0 := lt_of_lt_of_le one_pos hTheta0ge1
  have hUps12mm0pos : (0 : ℝ) < Ups12 * mm0 := by
    have h1 : (0 : ℝ) < Ups12 := lt_of_lt_of_le one_pos hUps12ge1
    have h2 : (0 : ℝ) < mm0 := lt_of_lt_of_le one_pos hmm0ge1
    exact mul_pos h1 h2
  have hUps12mm0ge1 : (1 : ℝ) ≤ Ups12 * mm0 := by
    nlinarith only [hUps12ge1, hmm0ge1,
      mul_nonneg (by linarith only [hUps12ge1] : (0 : ℝ) ≤ Ups12 - 1)
        (by linarith only [hmm0ge1] : (0 : ℝ) ≤ mm0 - 1)]
  -- argument of the first log is monotone in Theta0, and ≥ 1
  have hargmono : Ups12 * mm0 * Theta0 ≤ Ups12 * mm0 * Theta0' :=
    mul_le_mul_of_nonneg_left hTheta0le hUps12mm0pos.le
  have harg_ge1 : (1 : ℝ) ≤ Ups12 * mm0 * Theta0 := by
    nlinarith only [hUps12mm0ge1, hTheta0ge1,
      mul_nonneg (by linarith only [hUps12mm0ge1] : (0 : ℝ) ≤ Ups12 * mm0 - 1)
        (by linarith only [hTheta0ge1] : (0 : ℝ) ≤ Theta0 - 1)]
  have harg'_ge1 : (1 : ℝ) ≤ Ups12 * mm0 * Theta0' := le_trans harg_ge1 hargmono
  have hlogargmono : Real.log (Ups12 * mm0 * Theta0) ≤ Real.log (Ups12 * mm0 * Theta0') :=
    Real.log_le_log (lt_of_lt_of_le one_pos harg_ge1) hargmono
  have hlogarg_nn : (0 : ℝ) ≤ Real.log (Ups12 * mm0 * Theta0) := Real.log_nonneg harg_ge1
  -- second log's argument is monotone in Theta0, and ≥ 1
  have hCmixnn : (0 : ℝ) ≤ Cmix := by linarith only [hCmix]
  have harg2part_mono : 2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0) ≤
      2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0') := by
    have h := mul_le_mul_of_nonneg_left hlogargmono
      (by linarith only [hCmixnn] : (0 : ℝ) ≤ 4 * Cmix)
    linarith only [h]
  have harg2part_ge2 : (2 : ℝ) ≤ 2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0) := by
    nlinarith only [hlogarg_nn, hCmixnn]
  have harg2part_nn : (0 : ℝ) ≤ 2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0) := by
    linarith only [harg2part_ge2]
  have harg2part'_nn : (0 : ℝ) ≤ 2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0') := by
    linarith only [harg2part_mono, harg2part_nn]
  have hsecmono : 3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)) ≤
      3 * Theta0' * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0')) := by
    have hTheta0nn3 : (0 : ℝ) ≤ 3 * Theta0 := by linarith only [hTheta0pos]
    have step1 : 3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)) ≤
        3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0')) :=
      mul_le_mul_of_nonneg_left harg2part_mono hTheta0nn3
    have step2 : 3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0')) ≤
        3 * Theta0' * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0')) := by
      have h := mul_le_mul_of_nonneg_right hTheta0le harg2part'_nn
      nlinarith only [h]
    linarith only [step1, step2]
  have hsec_ge1 : (1 : ℝ) ≤ 3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)) := by
    have h3Theta0ge3 : (3 : ℝ) ≤ 3 * Theta0 := by linarith only [hTheta0ge1]
    nlinarith only [h3Theta0ge3, harg2part_ge2,
      mul_nonneg (by linarith only [h3Theta0ge3] : (0 : ℝ) ≤ 3 * Theta0 - 3)
        (by linarith only [harg2part_ge2] : (0 : ℝ) ≤
          2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0) - 2)]
  have hlog2mono : Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) ≤
      Real.log (3 * Theta0' * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0'))) :=
    Real.log_le_log (lt_of_lt_of_le one_pos hsec_ge1) hsecmono
  have hlog2_nn : (0 : ℝ) ≤
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) :=
    Real.log_nonneg hsec_ge1
  have hPrefnn : (0 : ℝ) ≤ 32 * C61 * (Cmix + 1) := by nlinarith only [hC61, hCmix]
  have hlogarg'_nn : (0 : ℝ) ≤ Real.log (Ups12 * mm0 * Theta0') := Real.log_nonneg harg'_ge1
  have hprodmono : Real.log (Ups12 * mm0 * Theta0) *
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0))) ≤
      Real.log (Ups12 * mm0 * Theta0') *
      Real.log (3 * Theta0' * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0'))) :=
    mul_le_mul hlogargmono hlog2mono hlog2_nn hlogarg'_nn
  calc 32 * C61 * (Cmix + 1) *
      Real.log (Ups12 * mm0 * Theta0) *
      Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)))
      = 32 * C61 * (Cmix + 1) *
        (Real.log (Ups12 * mm0 * Theta0) *
          Real.log (3 * Theta0 * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0)))) := by ring
    _ ≤ 32 * C61 * (Cmix + 1) *
        (Real.log (Ups12 * mm0 * Theta0') *
          Real.log (3 * Theta0' * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0')))) :=
        mul_le_mul_of_nonneg_left hprodmono hPrefnn
    _ = 32 * C61 * (Cmix + 1) *
        Real.log (Ups12 * mm0 * Theta0') *
        Real.log (3 * Theta0' * (2 + 4 * Cmix * Real.log (Ups12 * mm0 * Theta0'))) := by ring

end SuperdiffusionCLT.Section4.HomogBelow
