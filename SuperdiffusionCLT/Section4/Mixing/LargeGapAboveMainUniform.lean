/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapAboveEntrySumUniform
public import SuperdiffusionCLT.Section4.Mixing.LargeGapAboveNumericUniform
public import SuperdiffusionCLT.Section4.Mixing.LargeGapAboveQuadratic
public import SuperdiffusionCLT.Section4.Mixing.LargeGapConcentrationFinal

/-!
# The above-lattice main estimate, one `d`-only constant

The statement `mixing_below_cutoff` fixes its constant `C` *before*
quantifying over `ν, P, L, m, n` (`∃ C, ... ∧ ∀ ν P L m n, ...`), whereas
the above-lattice main estimate produces its `X4`-clause
witness *after* those are fixed (`∀ ..., ∃ C X4, ...`). Both amplitude
sub-lemmas it calls (the entry-sum amplitude bound and the wide numeric tail)
in fact return a constant depending only on `d` (resp. `d, K`, here fixed to
the canonical threshold `K₀(d) := 6100/(d log 3)`); this file exposes that
fact by restating them uniform first (`LargeGapAboveEntrySumUniform.lean`,
`LargeGapAboveNumericUniform.lean`) and reassembling. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- **The above-lattice main estimate, one `C(d)` uniform in `ν, P, L, nn, m`.** The gap
hypothesis fixes `K := 6100/(d log 3)` (the canonical threshold
the main estimate needs); a larger constant `C' ≥ K` gives a
*stronger* hypothesis `C' log(ν⁻¹n) ≤ m - n` here (since `log(ν⁻¹n) ≥ 0`),
so this composes with any such `C'`. -/
theorem mixGapAbove_main_uniform [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {nu : ℝ} {L nn m : ℕ} {P : ProbabilityMeasure (ShellSeq d)},
        0 < nu → nu ≤ 1 → 1 ≤ L → 1 ≤ m → L < nn →
        (6100 / ((d : ℝ) * Real.log 3)) * Real.log (nu⁻¹ * (nn : ℝ)) ≤ (m : ℝ) - (nn : ℝ) →
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∃ X4 : ShellSeq d → ℝ, Measurable X4 ∧
          IsBigO P.toMeasure (gammaSigma 1) X4 (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
          ∀ (omega : ShellSeq d) (p q : BlockVec d),
            2 * (((descendantsAtDepth (originCube d (m : ℤ)) (m - nn)).card : ℝ)⁻¹ *
                ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - nn),
                  blockVecDot p (blockMatVecMul
                    (ofFullBlockMat (toFullBlockMat
                          (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
                        toFullBlockMat
                          (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ))))))
                    q)) ≤
              X4 omega *
                (blockVecDot p
                    (blockMatVecMul
                      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) p) +
                  blockVecDot q
                    (blockMatVecMul
                      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) q)) := by
  obtain ⟨Cent, hCent_nn, hCent⟩ := mixGapAbove_entrySumAmp_le_uniform d
  obtain ⟨Cwide, hCwide_nn, hCwide⟩ := mixGapAbove_numericTail_uniform hd
  have hcrude_nn : (0:ℝ) ≤ Section4.Ellipticity.ellipBelow_crudeConst d := by
    unfold Section4.Ellipticity.ellipBelow_crudeConst
    have := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst_pos d
    positivity
  refine ⟨(2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent * Cwide,
    mul_nonneg (mul_nonneg (by positivity) hCent_nn) hCwide_nn, ?_⟩
  intro nu L nn m P hnu hnu1 hL hm1 hLn hgap hPrefix hJ1 hJ2 hJ3 hJ4
  have hnn1 : 1 ≤ nn := le_trans hL hLn.le
  have hnm : nn ≤ m := by
    have hKpos : (0:ℝ) < 6100 / ((d : ℝ) * Real.log 3) :=
      div_pos (by norm_num)
        (mul_pos (by exact_mod_cast lt_of_lt_of_le (by norm_num) hd) (Real.log_pos (by norm_num)))
    have hnnR : (1:ℝ) ≤ (nn:ℝ) := by exact_mod_cast hnn1
    have hnuinvnn : (1:ℝ) ≤ nu⁻¹ * (nn:ℝ) := by
      have hnuinv1 : (1:ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
      calc (1:ℝ) = 1*1 := by ring
        _ ≤ nu⁻¹ * (nn:ℝ) := mul_le_mul hnuinv1 hnnR (by norm_num) (by linarith only [hnuinv1])
    have hlog_nn : (0:ℝ) ≤ Real.log (nu⁻¹ * (nn:ℝ)) := Real.log_nonneg hnuinvnn
    have hmnn_nn : (0:ℝ) ≤ (m:ℝ) - (nn:ℝ) := le_trans (by positivity) hgap
    exact_mod_cast (by linarith only [hmnn_nn] : (nn:ℝ) ≤ (m:ℝ))
  set X4 : ShellSeq d → ℝ := fun omega =>
    (2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ)) *
      mixGap_entrySumEnvelope nu L P nn m omega with hX4
  have hexp_eq : (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2) =
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (nn : ℝ))) := by
    rw [Nat.cast_sub hnm]
    congr 1
    ring
  have hCent' : mixGapAbove_entrySumAmp d nu L nn m ≤
      Cent * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2) :=
    hCent hnu hnu1 hL
  have hCwide' : nu ^ (-(4 : ℝ)) * (nn : ℝ) ^ (2 : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (nn : ℝ))) ≤
      Cwide * (m : ℝ) ^ (-(3000 : ℝ)) :=
    hCwide hnu hnu1 hnn1 hm1 hgap
  have hLnnsq : (L : ℝ) ^ (2 : ℝ) ≤ (nn : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLn.le) (by norm_num)
  refine ⟨X4, (mixGap_measurable_entrySumEnvelope hnu L nn m).const_mul _, ?_, ?_⟩
  · have hbig := mixGapAbove_isBigO_gammaOne_entrySumEnvelope hnu hPrefix hJ1 hJ2 hJ3 hJ4 hLn.le hnm
    have hscale_nn : (0:ℝ) ≤ 2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ) := by
      have h2 : (0:ℝ) ≤ nu ^ (-(3:ℝ)) := Real.rpow_nonneg hnu.le _
      have h3 : (0:ℝ) ≤ (L:ℝ) := by positivity
      exact mul_nonneg (mul_nonneg (by positivity) h2) h3
    have hscaled := hbig.const_mul
      (c := 2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ))
      hscale_nn
    have hCd_nn : (0:ℝ) ≤ (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent :=
      mul_nonneg (by positivity) hCent_nn
    have hfinal : (2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ)) *
        (Cent * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2)) ≤
        (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent * Cwide *
          (m : ℝ) ^ (-(3000 : ℝ)) := by
      have hstep1 : (2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ)) *
          (Cent * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2)) =
          (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
            (nu ^ (-(3:ℝ)) * nu⁻¹ * ((L:ℝ) * (L:ℝ)) *
              (3 : ℝ) ^ (-((d : ℝ) * ((m - nn : ℕ) : ℝ)) / 2)) := by ring
      rw [hstep1, hexp_eq]
      have hnuinv_eq : nu ^ (-(3:ℝ)) * nu⁻¹ = nu ^ (-(4:ℝ)) := by
        rw [show nu⁻¹ = nu ^ (-(1:ℝ)) by rw [Real.rpow_neg_one], ← Real.rpow_add hnu]
        norm_num
      have hLL_eq : (L:ℝ) * (L:ℝ) = (L:ℝ) ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [hnuinv_eq, hLL_eq]
      have hpow_nn : (0:ℝ) ≤ (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (nn : ℝ))) :=
        Real.rpow_nonneg (by norm_num) _
      have hnu4_nn : (0:ℝ) ≤ nu ^ (-(4:ℝ)) := Real.rpow_nonneg hnu.le _
      have hstepLnn : nu ^ (-(4:ℝ)) * (L:ℝ) ^ (2:ℝ) *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (nn : ℝ))) ≤
          nu ^ (-(4:ℝ)) * (nn:ℝ) ^ (2:ℝ) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (nn : ℝ))) := by
        have hmul1 : nu ^ (-(4:ℝ)) * (L:ℝ) ^ (2:ℝ) ≤ nu ^ (-(4:ℝ)) * (nn:ℝ) ^ (2:ℝ) :=
          mul_le_mul_of_nonneg_left hLnnsq hnu4_nn
        exact mul_le_mul_of_nonneg_right hmul1 hpow_nn
      have hstep2 : (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
          (nu ^ (-(4:ℝ)) * (nn:ℝ) ^ (2:ℝ) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m:ℝ) - (nn:ℝ)))) ≤
          (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
            (Cwide * (m:ℝ) ^ (-(3000:ℝ))) :=
        mul_le_mul_of_nonneg_left hCwide' hCd_nn
      calc (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
            (nu ^ (-(4:ℝ)) * (L:ℝ) ^ (2:ℝ) *
              (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m:ℝ) - (nn:ℝ))))
          ≤ (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
              (nu ^ (-(4:ℝ)) * (nn:ℝ) ^ (2:ℝ) *
                (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m:ℝ) - (nn:ℝ)))) :=
            mul_le_mul_of_nonneg_left hstepLnn hCd_nn
        _ ≤ (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
              (Cwide * (m:ℝ) ^ (-(3000:ℝ))) := hstep2
        _ = (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent * Cwide *
              (m : ℝ) ^ (-(3000 : ℝ)) := by ring
    exact hscaled.mono_scale (le_trans (mul_le_mul_of_nonneg_left hCent' hscale_nn) hfinal)
  · intro omega p q
    exact mixGap_quadraticForm_annealed_le hnu hnu1 L nn m hL P hPrefix hJ2 hJ3 hJ4 omega p q

/-- **The full main estimate, one `C(d)` uniform in `ν, P, L, nn, m` (the `n ≤ L`
companion of `mixGapAbove_main_uniform`).** Same `K := 6100/(d log 3)`
canonical threshold; `mixGap_entrySumAmp_le_uniform` supplies the
already-uniform amplitude, `mixGapAbove_numericTail_uniform` (generic in its
scale parameter) supplies the numeric tail at that parameter `:= L`. -/
theorem mixGap_main_full_uniform [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {nu : ℝ} {L nn m : ℕ} {P : ProbabilityMeasure (ShellSeq d)},
        0 < nu → nu ≤ 1 → 1 ≤ L → 1 ≤ m → nn ≤ L →
        (6100 / ((d : ℝ) * Real.log 3)) * Real.log (nu⁻¹ * (L : ℝ)) ≤ (m : ℝ) - (L : ℝ) →
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∃ X4 : ShellSeq d → ℝ, Measurable X4 ∧
          IsBigO P.toMeasure (gammaSigma 1) X4 (C * (m : ℝ) ^ (-(3000 : ℝ))) ∧
          ∀ (omega : ShellSeq d) (p q : BlockVec d),
            2 * (((descendantsAtDepth (originCube d (m : ℤ)) (m - nn)).card : ℝ)⁻¹ *
                ∑ R ∈ descendantsAtDepth (originCube d (m : ℤ)) (m - nn),
                  blockVecDot p (blockMatVecMul
                    (ofFullBlockMat (toFullBlockMat
                          (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) -
                        toFullBlockMat
                          (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ))))))
                    q)) ≤
              X4 omega *
                (blockVecDot p
                    (blockMatVecMul
                      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) p) +
                  blockVecDot q
                    (blockMatVecMul
                      (annealedBlockMatrix nu L P (cubeSet (originCube d (nn : ℤ)))) q)) := by
  obtain ⟨Cent, hCent_nn, hCent⟩ := mixGap_entrySumAmp_le_uniform d
  obtain ⟨Cwide, hCwide_nn, hCwide⟩ := mixGapAbove_numericTail_uniform hd
  have hcrude_nn : (0:ℝ) ≤ Section4.Ellipticity.ellipBelow_crudeConst d := by
    unfold Section4.Ellipticity.ellipBelow_crudeConst
    have := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst_pos d
    positivity
  refine ⟨(2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent * Cwide,
    mul_nonneg (mul_nonneg (by positivity) hCent_nn) hCwide_nn, ?_⟩
  intro nu L nn m P hnu hnu1 hL hm1 hnl hgap hPrefix hJ1 hJ2 hJ3 hJ4
  have hLm : L ≤ m := by
    have hKpos : (0:ℝ) < 6100 / ((d : ℝ) * Real.log 3) :=
      div_pos (by norm_num)
        (mul_pos (by exact_mod_cast lt_of_lt_of_le (by norm_num) hd) (Real.log_pos (by norm_num)))
    have hLR : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    have hnuinvL : (1:ℝ) ≤ nu⁻¹ * (L:ℝ) := by
      have hnuinv1 : (1:ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
      calc (1:ℝ) = 1*1 := by ring
        _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul hnuinv1 hLR (by norm_num) (by linarith only [hnuinv1])
    have hlog_nn : (0:ℝ) ≤ Real.log (nu⁻¹ * (L:ℝ)) := Real.log_nonneg hnuinvL
    have hmL_nn : (0:ℝ) ≤ (m:ℝ) - (L:ℝ) := le_trans (by positivity) hgap
    exact_mod_cast (by linarith only [hmL_nn] : (L:ℝ) ≤ (m:ℝ))
  set X4 : ShellSeq d → ℝ := fun omega =>
    (2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ)) *
      mixGap_entrySumEnvelope nu L P nn m omega with hX4
  have hexp_eq : (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2) =
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (L : ℝ))) := by
    rw [Nat.cast_sub hLm]
    congr 1
    ring
  have hCent' : mixGap_entrySumAmp d nu L m ≤
      Cent * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2) :=
    hCent hnu hnu1 hL
  have hCwide' : nu ^ (-(4 : ℝ)) * (L : ℝ) ^ (2 : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (L : ℝ))) ≤
      Cwide * (m : ℝ) ^ (-(3000 : ℝ)) :=
    hCwide hnu hnu1 hL hm1 hgap
  refine ⟨X4, (mixGap_measurable_entrySumEnvelope hnu L nn m).const_mul _, ?_, ?_⟩
  · have hbig := mixGap_isBigO_gammaOne_entrySumEnvelope hnu hPrefix hJ1 hJ2 hJ3 hJ4 hnl hLm
    have hscale_nn : (0:ℝ) ≤ 2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ) := by
      have h2 : (0:ℝ) ≤ nu ^ (-(3:ℝ)) := Real.rpow_nonneg hnu.le _
      have h3 : (0:ℝ) ≤ (L:ℝ) := by positivity
      exact mul_nonneg (mul_nonneg (by positivity) h2) h3
    have hscaled := hbig.const_mul
      (c := 2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ))
      hscale_nn
    have hCd_nn : (0:ℝ) ≤ (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent :=
      mul_nonneg (by positivity) hCent_nn
    have hfinal : (2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ)) *
        (Cent * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2)) ≤
        (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent * Cwide *
          (m : ℝ) ^ (-(3000 : ℝ)) := by
      have hstep1 : (2 * Section4.Ellipticity.ellipBelow_crudeConst d * nu ^ (-(3 : ℝ)) * (L : ℝ)) *
          (Cent * nu⁻¹ * (L : ℝ) * (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2)) =
          (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
            (nu ^ (-(3:ℝ)) * nu⁻¹ * ((L:ℝ) * (L:ℝ)) *
              (3 : ℝ) ^ (-((d : ℝ) * ((m - L : ℕ) : ℝ)) / 2)) := by ring
      rw [hstep1, hexp_eq]
      have hnuinv_eq : nu ^ (-(3:ℝ)) * nu⁻¹ = nu ^ (-(4:ℝ)) := by
        rw [show nu⁻¹ = nu ^ (-(1:ℝ)) by rw [Real.rpow_neg_one], ← Real.rpow_add hnu]
        norm_num
      have hLL_eq : (L:ℝ) * (L:ℝ) = (L:ℝ) ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [hnuinv_eq, hLL_eq]
      have hstep2 : (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
          (nu ^ (-(4:ℝ)) * (L:ℝ) ^ (2:ℝ) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m:ℝ) - (L:ℝ)))) ≤
          (2 * Section4.Ellipticity.ellipBelow_crudeConst d) * Cent *
            (Cwide * (m:ℝ) ^ (-(3000:ℝ))) :=
        mul_le_mul_of_nonneg_left hCwide' hCd_nn
      exact hstep2.trans_eq (by ring)
    exact hscaled.mono_scale (le_trans (mul_le_mul_of_nonneg_left hCent' hscale_nn) hfinal)
  · intro omega p q
    exact mixGap_quadraticForm_annealed_le hnu hnu1 L nn m hL P hPrefix hJ2 hJ3 hJ4 omega p q

end

end SuperdiffusionCLT.Section4.Mixing
