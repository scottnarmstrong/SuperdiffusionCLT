/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseWitness
public import SuperdiffusionCLT.Section4.Mixing.MixBaseTLBound
public import SuperdiffusionCLT.Section4.Mixing.AnnealedFinal
public import SuperdiffusionCLT.Section4.Mixing.MixBaseAnnealedSand
public import SuperdiffusionCLT.Section4.Mixing.MixBaseTEllScale
public import SuperdiffusionCLT.Section4.Mixing.MixBaseGaugeSplit
public import SuperdiffusionCLT.Section4.Mixing.TermGaugeFinalB
public import SuperdiffusionCLT.Section4.Mixing.ConvertNormalization

/-!
# `mixFin_annealedComparison` at amplitude at most `1/2`

This file feeds `mixFin_annealedComparison` its two witnesses `hLocBound`,
`hGaugeBound` (at one fixed coefficient `Cg ≥ 1`) and concludes the deterministic sandwich bound
at a rate `t ≤ 1/2`, once the small-gap constant `C` is large. The coefficient `Cg` and the
margin constant `K₀` are fixed first; `C₀` depends on `d`, `Cg` only.

The envelope bound `σ ≤ (1 + 2 cutoffEnvelopeConst d) ν⁻¹ L` is derived from
`mixBase_tL_lowerBound`, so no hypothesis about `σ` beyond the small gap is carried.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-- The envelope bound on the running diffusivity scalar. -/
theorem mixBase_sigmaStar_le_envelope [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {L : ℕ} (hL1 : 1 ≤ L) {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (n : ℕ) :
    sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ))) ≤
      (1 + 2 * cutoffEnvelopeConst d) * (nu⁻¹ * (L : ℝ)) := by
  have hpos := sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hlow := mixBase_tL_lowerBound hnu hnu1 hL1 hPrefix hJ2 hJ3 hJ4 (j := (n : ℤ))
    (Int.natCast_nonneg n)
  rw [sigmaBarStarScalar_eq_inv hnu L hJ4 (n : ℤ) hpos]
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hBpos : 0 < 1 + 2 * cutoffEnvelopeConst d := by
    have := one_le_cutoffEnvelopeConst d
    linarith only [this]
  have hden : 0 < (1 + 2 * cutoffEnvelopeConst d) * (L : ℝ) := mul_pos hBpos hLpos
  have h := inv_anti₀ (div_pos hnu hden) hlow
  have heq : (nu / ((1 + 2 * cutoffEnvelopeConst d) * (L : ℝ)))⁻¹ =
      (1 + 2 * cutoffEnvelopeConst d) * (nu⁻¹ * (L : ℝ)) := by
    field_simp
  rw [heq] at h
  exact h

/-- **The `X1`/`X2` witnesses of `hBase`** at the `L`-normalization and the
amplitudes `C (L-n)^{1/2} σ⁻¹`, `C (L-n) σ⁻²`. The rate-`t` comparison `hcomp` (`t ≤ 1/2`) is
the output of `mixFin_annealedComparison` at amplitude at most `1/2`; the threshold `K₀`
for the `t_ell → t_L` conversion and
the coefficient threshold `CX` are fixed before `C`. -/
theorem mixBase_X12_witness (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ K0 CX : ℝ, 1 ≤ K0 ∧ K0 ≤ 5 ∧ 1 ≤ CX ∧ ∀ C : ℝ, CX ≤ C →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
              ∀ n L ell m : ℕ, 1 ≤ L → n ≤ ell → ell < L →
                K0 * Real.log (nu⁻¹ * (L : ℝ)) ≤ (((ell - n : ℕ) : ℕ) : ℝ) →
                ∀ t : ℝ, t ≤ 1 / 2 →
                  (∀ p q : BlockVec d,
                    2 * (blockVecDot p (blockMatVecMul
                            (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) -
                          blockVecDot p (blockMatVecMul
                            (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)) ≤
                      t * (blockVecDot p (blockMatVecMul
                              (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
                            blockVecDot q (blockMatVecMul
                              (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q))) →
                  ∃ X1 X2 : ShellSeq d → ℝ,
                    Measurable X1 ∧
                      IsBigO P.toMeasure (gammaSigma 2) X1
                        (C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                            (-(1 : ℝ))) ∧
                    Measurable X2 ∧
                      IsBigO P.toMeasure (gammaSigma 1) X2
                        (C * ((L - n : ℕ) : ℝ) *
                          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^
                            (-(2 : ℝ))) ∧
                    ∀ (omega : ShellSeq d) (p q : BlockVec d),
                      2 * descendantsAverage (originCube d (m : ℤ)) (m - n)
                          (fun R' => mixBase_F1 nu ell L P (n : ℤ) R' omega p q) ≤
                        X1 omega *
                          (blockVecDot p (blockMatVecMul
                              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
                            blockVecDot q (blockMatVecMul
                              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) ∧
                      2 * descendantsAverage (originCube d (m : ℤ)) (m - n)
                          (fun R' => mixBase_F2 nu ell L P (n : ℤ) R' omega p q) ≤
                        X2 omega *
                          (blockVecDot p (blockMatVecMul
                              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
                            blockVecDot q (blockMatVecMul
                              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) := by
  obtain ⟨K0, CE, hK01, hK05, hCE0, htell⟩ := mixBase_tEll_le_scaled_tL d hd
  have hCb1 := mixGaugeFinal_one_le_Cbase d
  set c1 : ℝ := 2 * (1 + CE) with hc1
  set c2 : ℝ := 2 * (1 + CE) ^ 2 with hc2
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  have hc2pos : 0 < c2 := by rw [hc2]; positivity
  refine ⟨K0, max 1 (max (c1 * mixGaugeFinal_Cbase d) (c2 * mixGaugeFinal_Cbase d)), hK01, hK05,
    le_max_left _ _, ?_⟩
  intro C hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 n L ell m hL1 hnell hellL hgap t ht hcomp
  have hCc1 : c1 * mixGaugeFinal_Cbase d ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hCc2 : c2 * mixGaugeFinal_Cbase d ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hC1 : 1 ≤ C := le_trans (le_max_left _ _) hC
  have ht1 : t < 1 := by linarith only [ht]
  have h1t : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith only [ht])]
    linarith only [ht]
  have h1t0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.2 (by linarith only [ht])
  -- scalar comparisons
  obtain ⟨-, hs, -, hu⟩ := mixBase_invertB_of_annealedComparison hnu hJ4 ell L (n : ℤ) ht1 hcomp
  have hdom : ∀ p : BlockVec d,
      blockVecDot p (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) ≤
        (1 - t)⁻¹ * blockVecDot p
          (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) := by
    intro p
    rw [mixMain_annealedBilinear_eq hnu ell hJ4 (n : ℤ) p,
      mixMain_annealedBilinear_eq hnu L hJ4 (n : ℤ) p]
    exact mixMain_quadraticForm_dom_of_scalar_bounds hs hu p
  have hQL : ∀ p q : BlockVec d, 0 ≤
      blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) := by
    intro p q
    have hsL := sigmaBarScalar_originCube_pos hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
    have huL := sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
    rw [mixMain_annealedBilinear_eq hnu L hJ4 (n : ℤ) p, mixMain_annealedBilinear_eq hnu L hJ4 (n : ℤ) q]
    nlinarith only [mul_nonneg hsL.le (vecNormSq_nonneg p.1), mul_nonneg huL.le (vecNormSq_nonneg p.2),
      mul_nonneg hsL.le (vecNormSq_nonneg q.1), mul_nonneg huL.le (vecNormSq_nonneg q.2)]
  have hellnn : 0 ≤ sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) :=
    (sigmaBarStarInvSeq_pos hnu ell hPrefix hJ2 hJ3 hJ4 n).le
  have htLpos := sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)
  have hscale := htell nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell L n hL1 hnell hellL.le hgap
  set tE := sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) with htE
  set tL := sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) with htL
  -- amplitudes
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  have hCb : ∀ c : ℝ, 0 < c → c * mixGaugeFinal_Cbase d ≤ C →
      mixGaugeFinal_Cbase d ≤ C / c := fun c hc h => by
    rw [le_div_iff₀ hc]; linarith only [h, mul_comm c (mixGaugeFinal_Cbase d)]
  have hsig : 0 < sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ))) :=
    SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L hPrefix hJ2 hJ3 hJ4
      (n : ℤ)
  have hu_le : ((L - ell : ℕ) : ℝ) ≤ ((L - n : ℕ) : ℝ) := by exact_mod_cast (by omega : L - ell ≤ L - n)
  have hpow1 : ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hu_le (by norm_num)
  obtain ⟨hX1M, hX1O⟩ := mixGaugeFinal_X1g_isBigO (P := P) (nu := nu) hnu hPrefix hJ2 hJ3 hJ4
    (hCb c1 hc1pos hCc1) ell L n m hellL
  obtain ⟨hX2M, hX2O⟩ := mixGaugeFinal_X2g_isBigO (P := P) (nu := nu) hnu hPrefix hJ2 hJ3 hJ4
    (hCb c2 hc2pos hCc2) ell L n m hellL
  refine ⟨fun omega => c1 * (4 * tL * mixGaugeFinal_Y1 omega ell L n m),
    fun omega => c2 * (2 * tL ^ 2 * mixGaugeFinal_Y2 omega ell L n m),
    hX1M.const_mul c1, ?_, hX2M.const_mul c2, ?_, ?_⟩
  · refine (hX1O.const_mul hc1pos.le).mono_scale ?_
    have hσ1 : 0 ≤ (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ)) :=
      Real.rpow_nonneg hsig.le _
    have : c1 * (C / c1 * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ))) =
        C * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(1 : ℝ)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 hCpos.le) hσ1
  · refine (hX2O.const_mul hc2pos.le).mono_scale ?_
    have hσ2 : 0 ≤ (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ)) :=
      Real.rpow_nonneg hsig.le _
    have : c2 * (C / c2 * ((L - ell : ℕ) : ℝ) *
        (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ))) =
        C * ((L - ell : ℕ) : ℝ) *
          (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (-(2 : ℝ)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu_le hCpos.le) hσ2
  · intro omega p q
    have hY1 := mixGaugeFinal_Y1_nonneg omega ell L n m
    have hY2 := mixGaugeFinal_Y2_nonneg omega ell L n m
    have hQ := hQL p q
    constructor
    · have hbase := mixBase_F1_avg_le hnu omega ell L n m hPrefix hJ2 hJ3 hJ4 p q
      have hconv := mixMain_convertNormalization_bilinear (Ω := ShellSeq d) (t := t)
        (QA := fun p => blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p))
        (QB := fun p => blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p))
        hdom
        (F := fun omega p q => descendantsAverage (originCube d (m : ℤ)) (m - n)
          (fun R' => mixBase_F1 nu ell L P (n : ℤ) R' omega p q))
        (X := fun omega => 4 * tE * mixGaugeFinal_Y1 omega ell L n m)
        (fun omega => mul_nonneg (mul_nonneg (by norm_num) hellnn) (mixGaugeFinal_Y1_nonneg omega ell L n m))
        (fun omega p q => mixBase_F1_avg_le hnu omega ell L n m hPrefix hJ2 hJ3 hJ4 p q)
        omega p q
      refine hconv.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hQ
      have h4 : 0 ≤ 4 * tE * mixGaugeFinal_Y1 omega ell L n m :=
        mul_nonneg (mul_nonneg (by norm_num) hellnn) hY1
      rw [div_eq_mul_inv, mul_comm _ (1 - t)⁻¹]
      calc (1 - t)⁻¹ * (4 * tE * mixGaugeFinal_Y1 omega ell L n m)
          ≤ 2 * (4 * tE * mixGaugeFinal_Y1 omega ell L n m) := mul_le_mul_of_nonneg_right h1t h4
        _ ≤ 2 * (4 * ((1 + CE) * tL) * mixGaugeFinal_Y1 omega ell L n m) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale
              (by norm_num : (0 : ℝ) ≤ 4)) hY1
            nlinarith only [this]
        _ = c1 * (4 * tL * mixGaugeFinal_Y1 omega ell L n m) := by rw [hc1]; ring
    · have hconv := mixMain_convertNormalization_bilinear (Ω := ShellSeq d) (t := t)
        (QA := fun p => blockVecDot p (blockMatVecMul (mixTerms_Aell nu ell P (n : ℤ)) p))
        (QB := fun p => blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p))
        hdom
        (F := fun omega p q => descendantsAverage (originCube d (m : ℤ)) (m - n)
          (fun R' => mixBase_F2 nu ell L P (n : ℤ) R' omega p q))
        (X := fun omega => 2 * tE ^ 2 * mixGaugeFinal_Y2 omega ell L n m)
        (fun omega => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (mixGaugeFinal_Y2_nonneg omega ell L n m))
        (fun omega p q => mixBase_F2_avg_le hnu omega ell L n m hPrefix hJ2 hJ3 hJ4 p q)
        omega p q
      refine hconv.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ hQ
      have h4 : 0 ≤ 2 * tE ^ 2 * mixGaugeFinal_Y2 omega ell L n m :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hY2
      have hsq : tE ^ 2 ≤ ((1 + CE) * tL) ^ 2 := pow_le_pow_left₀ hellnn hscale 2
      rw [div_eq_mul_inv, mul_comm _ (1 - t)⁻¹]
      calc (1 - t)⁻¹ * (2 * tE ^ 2 * mixGaugeFinal_Y2 omega ell L n m)
          ≤ 2 * (2 * tE ^ 2 * mixGaugeFinal_Y2 omega ell L n m) := mul_le_mul_of_nonneg_right h1t h4
        _ ≤ 2 * (2 * ((1 + CE) * tL) ^ 2 * mixGaugeFinal_Y2 omega ell L n m) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq
              (by norm_num : (0 : ℝ) ≤ 2)) hY2
            nlinarith only [this]
        _ = c2 * (2 * tL ^ 2 * mixGaugeFinal_Y2 omega ell L n m) := by rw [hc2]; ring

end

end SuperdiffusionCLT.Section4.Mixing
