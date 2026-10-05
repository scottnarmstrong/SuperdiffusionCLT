/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssemblyA
public import SuperdiffusionCLT.Section4.Mixing.MixBaseWitnessB
public import SuperdiffusionCLT.Section4.Mixing.MixMainTerm1Bare
public import SuperdiffusionCLT.Section4.Mixing.MixMainGaugeBare

/-!
# The localization and gauge witnesses at one shared coefficient

`mixBaseB_hLoc` and `mixBaseB_hGauge` supply the two witnesses consumed by
`mixFin_annealedComparison`, at an arbitrary coefficient `Cg` above a dimension-only threshold.
The gauge witness uses the scale conversion with one uniform constant
(`mixBase_raw_uniform`), so its coefficient does not depend on the instance. The absorption of
the explicit `X3g` amplitude into `Cg m^{-5000}` is `mixGaugeAbsorb_X3g_amplitude_bound`.
The numerals `1 < log 3 < 3/2` give the sizes of the canonical threshold `50100 / log 3`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

theorem mixBaseB_one_lt_log_three : (1 : ℝ) < Real.log 3 :=
  (Real.lt_log_iff_exp_lt (by norm_num)).2 (by
    have := Real.exp_one_lt_d9
    linarith only [this])

theorem mixBaseB_log_three_lt : Real.log 3 < 3 / 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)
  norm_num at h
  linarith only [h]

theorem mixBaseB_K1_tenth_le {Lg : ℝ} (hLg : 0 ≤ Lg) :
    (50100 / Real.log 3) / 10 * Lg ≤ 5010 * Lg := by
  have h1 := mixBaseB_one_lt_log_three
  have : 50100 / Real.log 3 ≤ 50100 := by
    rw [div_le_iff₀ (by linarith only [h1])]
    nlinarith only [h1]
  nlinarith only [this, hLg]

theorem mixBaseB_K1_half_ge : (16700 : ℝ) ≤ (50100 / Real.log 3) / 2 := by
  have h2 := mixBaseB_log_three_lt
  have h1 := mixBaseB_one_lt_log_three
  have : (33400 : ℝ) ≤ 50100 / Real.log 3 := by
    rw [le_div_iff₀ (by linarith only [h1])]
    nlinarith only [h2]
  linarith only [this]

/-- **The localization witness at a shared coefficient.** -/
theorem mixBaseB_hLoc (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cl : ℝ, 1 ≤ Cl ∧ ∀ Cg : ℝ, Cl ≤ Cg →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
              ∀ m n ell L : ℕ, n ≤ ell → ell ≤ m → ell ≤ L → 1 ≤ ell → 1 ≤ L → 1 ≤ m →
                ((50100 / Real.log 3) / 10 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((ell - n : ℕ) : ℝ)) →
                ((50100 / Real.log 3) / 10 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((m - ell : ℕ) : ℝ)) →
                ((m : ℝ) ≤ (L : ℝ) + (50100 / Real.log 3) / 2 * Real.log (nu⁻¹ * (L : ℝ))) →
                ∃ X3loc : ShellSeq d → ℝ,
                  Measurable X3loc ∧
                    IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3loc
                      (Cg * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                    ∀ (omega : ShellSeq d) (p q : BlockVec d),
                      2 * (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                            blockVecDot p (blockMatVecMul
                              (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
                        X3loc omega *
                          (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                            blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  obtain ⟨Cl, hCl1, hCl⟩ := mixMain_term1BoundBare d hd
  refine ⟨Cl, hCl1, fun Cg hCg nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL hell1
    hL1 hm1 hg1 hg2 hcase => ?_⟩
  obtain ⟨X, hXm, hXO, hXb⟩ := hCl nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n ell L hnl hlm hlL
    hell1 hL1 hm1 hg1 hg2 hcase
  have hmp : (0 : ℝ) ≤ (m : ℝ) ^ (-(5000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact ⟨X, hXm, hXO.mono_scale (mul_le_mul_of_nonneg_right hCg hmp), hXb⟩

/-- **The gauge witness at a shared coefficient.** -/
theorem mixBaseB_hGauge (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cg1 : ℝ, 1 ≤ Cg1 ∧ ∀ Cg : ℝ, Cg1 ≤ Cg →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
            ∀ ell L n m : ℕ, n ≤ ell → ell < L → 1 ≤ m →
              ((50100 / Real.log 3) / 10 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((ell - n : ℕ) : ℝ)) →
              ((m : ℝ) ≤ (L : ℝ) + (50100 / Real.log 3) / 2 * Real.log (nu⁻¹ * (L : ℝ))) →
              ∃ X1g X2g X3g : ShellSeq d → ℝ,
                Measurable X1g ∧
                  IsBigO P.toMeasure (gammaSigma 2) X1g
                    (Cg * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                        (-(1 : ℝ))) ∧
                Measurable X2g ∧
                  IsBigO P.toMeasure (gammaSigma 1) X2g
                    (Cg * ((L - ell : ℕ) : ℝ) *
                      (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                        (-(2 : ℝ))) ∧
                Measurable X3g ∧
                  IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3g
                    (Cg * (m : ℝ) ^ (-(5000 : ℝ))) ∧
                  ∀ (omega : ShellSeq d) (p q : BlockVec d),
                    2 * (((descendantsAtDepth (originCube d (m : ℤ)) (m - n)).card : ℝ)⁻¹ *
                          ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - n),
                            blockVecDot p (blockMatVecMul
                              (mixTerms_gaugeTermMatrix nu omega ell L P (n : ℤ) R) q)) ≤
                      (X1g omega + X2g omega + X3g omega) *
                        (blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
                          blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q)) := by
  obtain ⟨Cfixed, hCf1, hrawU⟩ := mixBase_raw_uniform d hd
  obtain ⟨C', hC'0, hC'⟩ := mixGaugeAbsorb_X3g_amplitude_bound d (50100 / Real.log 3) le_rfl
    Cfixed hCf1
  refine ⟨max (mixGaugeFinal_Cbase d) (max C' 1), le_trans (mixGaugeFinal_one_le_Cbase d)
    (le_max_left _ _), fun Cg hCg nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell L n m hnell hellL
    hm1 hg1 hcase => ?_⟩
  have hCbase : mixGaugeFinal_Cbase d ≤ Cg := le_trans (le_max_left _ _) hCg
  have hC'Cg : C' ≤ Cg := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCg
  have hL1 : 1 ≤ L := by omega
  obtain ⟨hX1gM, hX1gO⟩ := mixGaugeFinal_X1g_isBigO hnu hPrefix hJ2 hJ3 hJ4 hCbase ell L n m hellL
  obtain ⟨hX2gM, hX2gO⟩ := mixGaugeFinal_X2g_isBigO hnu hPrefix hJ2 hJ3 hJ4 hCbase ell L n m hellL
  obtain ⟨hX3gM, hX3gO⟩ := mixGaugeFinal_X3g_isBigO hnu hPrefix hJ2 hJ3 hJ4 hCf1 ell L n m hellL
  have htLnn : 0 ≤ sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) :=
    (sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)).le
  have htLle : sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) ≤ nu⁻¹ :=
    SuperdiffusionCLT.Section3.Setup.sigmaBarStarInvSeq_le_nuInv hnu L hPrefix hJ2 hJ3 hJ4 n
  have hamp := hC' nu L m n ell _ hnu hnu1 hL1 hm1 hellL.le htLnn htLle hg1 hcase
  have hmp : (0 : ℝ) ≤ (m : ℝ) ^ (-(5000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨_, _, _, hX1gM, hX1gO, hX2gM, hX2gO, hX3gM,
    hX3gO.mono_scale (hamp.trans (mul_le_mul_of_nonneg_right hC'Cg hmp)), ?_⟩
  intro omega p q
  have hEbound := hrawU nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell L n hnell hellL.le
  set E : ℝ := nu⁻¹ * gammaMomentConst 1 *
    (Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) with hEdef
  have htEllpos := sigmaBarStarInvScalar_pos_cutoff hnu ell hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    have h1 : (0 : ℝ) ≤ nu⁻¹ := inv_nonneg.2 hnu.le
    have h2 : (0 : ℝ) ≤ gammaMomentConst 1 := (gammaMomentConst_pos (by norm_num)).le
    have h3 : (0 : ℝ) ≤ Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) :=
      mul_nonneg (mul_nonneg (by linarith only [hCf1]) (Real.rpow_nonneg hnu.le _))
        (Real.rpow_nonneg (by norm_num) _)
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hsplit := mixGaugeFinal_coeff_split
    (tEll := sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))))
    (tL := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ)))) (E := E)
    (Y1 := mixGaugeFinal_Y1 omega ell L n m) (Y2 := mixGaugeFinal_Y2 omega ell L n m)
    htEllpos.le htLnn hEnn (mixGaugeFinal_Y1_nonneg omega ell L n m)
    (mixGaugeFinal_Y2_nonneg omega ell L n m) hEbound
  have hdet := mixGaugeFinal_bilinear_avg_le hnu hPrefix hJ2 hJ3 hJ4 ell L n m omega p q
  have hKnn : 0 ≤ blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p) +
      blockVecDot q (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) q) :=
    add_nonneg (mixGaugeFinal_Aell_bilinear_nonneg hnu ell hPrefix hJ2 hJ3 hJ4 (n : ℤ) p)
      (mixGaugeFinal_Aell_bilinear_nonneg hnu ell hPrefix hJ2 hJ3 hJ4 (n : ℤ) q)
  exact hdet.trans (mul_le_mul_of_nonneg_right hsplit hKnn)

end

end SuperdiffusionCLT.Section4.Mixing
