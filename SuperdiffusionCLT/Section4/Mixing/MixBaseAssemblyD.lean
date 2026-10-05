/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseAssemblyC
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# `hBase` in the far regime `6500 log(ν⁻¹L) < L - n`

`mixBaseD_far` supplies the `hBase` conclusion for `n < L` when the gap `L - n` exceeds
`6500 log(ν⁻¹L)`, at the margin constant `K₀ = 1100`. The auxiliary scale is
`ell = n + ⌈5010 log(ν⁻¹L)⌉`. The three pieces are
`F1 = F1^{gauge} - λ (AL - Aell)`, `F2 = F2^{gauge}`, `F3 = loc - (1 - λ) (AL - Aell)`, where the
constant bilinear mismatch `AL - Aell` is split between `F1` and `F3` in the proportion `λ = τ₁₂/τ`
of the two parts of the annealed-comparison amplitude `τ = τ₁₂ + τ₃` (`τ₁₂` of order
`(L - n)^{1/2} σ⁻¹`, `τ₃` of order `m^{-5000}`). Reading the comparison at `(-p, q)` gives the
reverse sign, and the two shares are absorbed into the `Γ₂` amplitude of `X1` and the
`Γ_{1/3}` amplitude of `X3` respectively.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)

noncomputable section

variable {d : ℕ}

theorem mixBaseD_amp_comp {a1 a2 Cg C σ u w : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (hCg : 0 ≤ Cg)
    (hC : 1 ≤ C) (hσ : 0 < σ) (hu0 : 0 ≤ u) (huw : u ≤ w) (hgap : w ≤ C⁻¹ * σ ^ 2) :
    a1 * (Cg * u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) + a2 * (Cg * u * σ ^ (-(2 : ℝ))) ≤
      (a1 + a2) * Cg * (w ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) := by
  have hw0 : 0 ≤ w := hu0.trans huw
  have hσ2 : 0 < σ ^ 2 := by positivity
  have h2 : σ ^ (-(2 : ℝ)) = (σ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hσ.le]; norm_cast
  set a : ℝ := w ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)) with ha
  have ha0 : 0 ≤ a := mul_nonneg (Real.rpow_nonneg hw0 _) (Real.rpow_nonneg hσ.le _)
  have hsq : a ^ 2 = w * σ ^ (-(2 : ℝ)) := by
    rw [ha, mul_pow]
    congr 1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hw0]; norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hσ.le]; norm_num
  have hwσ : w * σ ^ (-(2 : ℝ)) ≤ 1 := by
    rw [h2, ← div_eq_mul_inv, div_le_one hσ2]
    calc w ≤ C⁻¹ * σ ^ 2 := hgap
      _ ≤ 1 * σ ^ 2 := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hC) hσ2.le
      _ = σ ^ 2 := one_mul _
  have ha1le : a ≤ 1 := by nlinarith only [hsq, hwσ, ha0]
  have hsqa : w * σ ^ (-(2 : ℝ)) ≤ a := by rw [← hsq]; nlinarith only [ha0, ha1le]
  have hA : u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)) ≤ a :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hu0 huw (by norm_num))
      (Real.rpow_nonneg hσ.le _)
  have hB : u * σ ^ (-(2 : ℝ)) ≤ a :=
    le_trans (mul_le_mul_of_nonneg_right huw (Real.rpow_nonneg hσ.le _)) hsqa
  have e1 : a1 * (Cg * u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) =
      a1 * Cg * (u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) := by ring
  have e2 : a2 * (Cg * u * σ ^ (-(2 : ℝ))) = a2 * Cg * (u * σ ^ (-(2 : ℝ))) := by ring
  have h3 := mul_le_mul_of_nonneg_left hA (mul_nonneg ha1 hCg)
  have h4 := mul_le_mul_of_nonneg_left hB (mul_nonneg ha2 hCg)
  rw [e1, e2]
  linarith only [h3, h4]

/-- The `AL`-versus-`Aell` bilinear mismatch at the origin cube. -/
noncomputable def mixBaseD_G0 (nu : ℝ) (ell L : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (n : ℕ)
    (p q : BlockVec d) : ℝ :=
  blockVecDot p (blockMatVecMul (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q) -
    blockVecDot p (blockMatVecMul (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)

theorem mixBaseD_far (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cfar : ℝ, 1 ≤ Cfar ∧ ∀ C : ℝ, Cfar ≤ C →
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
              ∀ n L : ℕ, 1 ≤ L → 1 ≤ n → n < L →
                (L : ℝ) - (n : ℝ) ≤
                  C⁻¹ * (sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ)))) ^ (2 : ℝ) →
                ∀ mb : ℕ, n ≤ mb →
                  (10 * 1100 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((mb - n : ℕ) : ℝ)) →
                  (((mb - n : ℕ) : ℝ) ≤ 20 * 1100 * (1 + Real.log (nu⁻¹ * (L : ℝ)))) →
                  6500 * Real.log (nu⁻¹ * (L : ℝ)) < (L : ℝ) - (n : ℝ) →
                    ∃ F1 F2 F3 : TriadicCube d → ShellSeq d → BlockVec d → BlockVec d → ℝ,
                      (∀ R omega p q, F1 R omega p q + F2 R omega p q + F3 R omega p q =
                        blockVecDot p (blockMatVecMul (ofFullBlockMat
                          (toFullBlockMat (coarseBlockMatrix (cubeSet R)
                                (coefficientCutoff nu omega L).toCoeffField) -
                            toFullBlockMat
                              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))))) q)) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F1 (translateCube w Q) omega p q =
                              F1 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F2 (translateCube w Q) omega p q =
                              F2 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (∀ (zreal : Vec d) (w : Fin d → ℤ) (Q : TriadicCube d) (omega : ShellSeq d)
                          (p q : BlockVec d),
                          cubeSet (translateCube w Q) = translateSet zreal (cubeSet Q) →
                            F3 (translateCube w Q) omega p q =
                              F3 Q (ShellField.translateSequence zreal omega) p q) ∧
                      (L ≤ n → ∀ R omega p q, F1 R omega p q = 0) ∧
                      (L ≤ n → ∀ R omega p q, F2 R omega p q = 0) ∧
                      ∃ X1 X2 X3 : ShellSeq d → ℝ,
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
                        Measurable X3 ∧
                          IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) X3
                            (C * (mb : ℝ) ^ (-(3000 : ℝ))) ∧
                          ∀ (omega : ShellSeq d) (p q : BlockVec d),
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F1 R' omega p q) ≤
                              X1 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) ∧
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F2 R' omega p q) ≤
                              X2 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) ∧
                            2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
                                (fun R' => F3 R' omega p q) ≤
                              X3 omega *
                                (blockVecDot p
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      p) +
                                  blockVecDot q
                                    (blockMatVecMul
                                      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
                                      q)) := by
  obtain ⟨Cl, hCl1, hLoc⟩ := mixBaseB_hLoc d hd
  obtain ⟨Cg1, hCg11, hGauge⟩ := mixBaseB_hGauge d hd
  obtain ⟨K0X, CX, hK0X1, hK0X5, hCX1, hX12⟩ := mixBase_X12_witness d hd
  set Cg : ℝ := max Cl Cg1 with hCgdef
  have hCgl : Cl ≤ Cg := le_max_left _ _
  have hCgg : Cg1 ≤ Cg := le_max_right _ _
  have hCg1 : 1 ≤ Cg := le_trans hCl1 hCgl
  have hCg0 : 0 < Cg := lt_of_lt_of_le one_pos hCg1
  have hB1 : (1 : ℝ) ≤ 1 + 2 * cutoffEnvelopeConst d := by
    have := one_le_cutoffEnvelopeConst d
    linarith only [this]
  set B : ℝ := 1 + 2 * cutoffEnvelopeConst d with hBdef
  have hg1 : 0 < gammaMomentConst 1 := gammaMomentConst_pos one_pos
  have hg2 : 0 < gammaMomentConst 2 := gammaMomentConst_pos (by norm_num)
  have hg3 : 0 < gammaMomentConst ((1 : ℝ) / 3) := gammaMomentConst_pos (by norm_num)
  have hg4 : 0 < gammaTriangleConst ((1 : ℝ) / 3) := gammaTriangleConst_pos
  obtain ⟨Ca, hCa1, hCa⟩ := mixBase_amplitude_le_half (a1 := gammaMomentConst 2)
    (a2 := gammaMomentConst 1) (a3 := gammaMomentConst ((1 : ℝ) / 3))
    (a4 := gammaTriangleConst ((1 : ℝ) / 3)) (Cg := Cg) (B := B) (K0 := 1100) hg2.le hg1.le
    hg3.le hg4.le hCg1 hB1 (by norm_num)
  set S1 : ℝ := 8 * (gammaMomentConst 1 + gammaMomentConst 2) * Cg with hS1
  set S3 : ℝ := 4 * Cg + 8 * gammaMomentConst ((1 : ℝ) / 3) * gammaTriangleConst ((1 : ℝ) / 3) *
    Cg with hS3
  set S4 : ℝ := (B * Real.exp 20) ^ 2 with hS4
  refine ⟨max (max Ca (4 * CX)) (max (max S1 S3) (max S4 1)),
    le_trans hCa1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro C hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 n L hL1 hn1 hnL hgapR mb hnmb hw1 hw2 hfar
  have hCa' : Ca ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hC4X : 4 * CX ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hCS1 : S1 ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hC
  have hCS3 : S3 ≤ C :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hC
  have hCS4 : S4 ≤ C :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hC
  have hC1 : 1 ≤ C := le_trans hCa1 hCa'
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  have hC4 : CX ≤ C / 4 := by linarith only [hC4X]
  have hσpos := SuperdiffusionCLT.Section3.HighContrast.sigmaBarStarScalar_pos hnu L hPrefix
    hJ2 hJ3 hJ4 (n : ℤ)
  have hσB := mixBase_sigmaStar_le_envelope hnu hnu1 hL1 hPrefix hJ2 hJ3 hJ4 n
  set σ : ℝ := sigmaBarStarScalar nu L P (cubeSet (originCube d (n : ℤ))) with hσdef
  have hgap : (L : ℝ) - (n : ℝ) ≤ C⁻¹ * σ ^ 2 := by
    rw [Real.rpow_two] at hgapR
    exact hgapR
  have hwn : (1 : ℝ) ≤ (L : ℝ) - (n : ℝ) := by
    have : (n : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hnL
    linarith only [this]
  have hCσ : C ≤ σ ^ 2 := by
    have h1 : C * 1 ≤ C * ((L : ℝ) - (n : ℝ)) := mul_le_mul_of_nonneg_left hwn hCpos.le
    have h2 : C * ((L : ℝ) - (n : ℝ)) ≤ σ ^ 2 :=
      calc C * ((L : ℝ) - (n : ℝ)) ≤ C * (C⁻¹ * σ ^ 2) :=
            mul_le_mul_of_nonneg_left hgap hCpos.le
        _ = σ ^ 2 := by field_simp
    linarith only [h1, h2]
  have hsqσ : Real.sqrt C ≤ σ :=
    (Real.sqrt_le_sqrt hCσ).trans_eq (Real.sqrt_sq hσpos.le)
  have hBpos : 0 < B := by linarith only [hB1]
  have hBexp : B * Real.exp 20 ≤ Real.sqrt C := by
    have h1 : Real.sqrt S4 = B * Real.exp 20 :=
      Real.sqrt_sq (mul_nonneg hBpos.le (Real.exp_pos 20).le)
    rw [← h1]
    exact Real.sqrt_le_sqrt hCS4
  have hexpY : Real.exp 20 ≤ nu⁻¹ * (L : ℝ) := by
    have h1 : B * Real.exp 20 ≤ B * (nu⁻¹ * (L : ℝ)) := hBexp.trans (hsqσ.trans hσB)
    exact le_of_mul_le_mul_left h1 hBpos
  have hYpos : 0 < nu⁻¹ * (L : ℝ) := lt_of_lt_of_le (Real.exp_pos 20) hexpY
  have hLg : 20 ≤ Real.log (nu⁻¹ * (L : ℝ)) := (Real.le_log_iff_exp_le hYpos).2 hexpY
  set Lg : ℝ := Real.log (nu⁻¹ * (L : ℝ)) with hLgdef
  have hLg0 : 0 ≤ Lg := by linarith only [hLg]
  have hm1 : 1 ≤ mb := le_trans hn1 hnmb
  have hw1' : 11000 * Lg ≤ ((mb - n : ℕ) : ℝ) := by linarith only [hw1]
  have hw2' : ((mb - n : ℕ) : ℝ) ≤ 22000 * (1 + Lg) := by linarith only [hw2]
  obtain ⟨ell, hnell, hellL, hellm, hell1, hg1', hg2', hcase⟩ :=
    mixBaseC_ell_facts hLg n L mb hn1 hnmb hfar hw1' hw2'
  have hK1a : (50100 / Real.log 3) / 10 * Lg ≤ 5010 * Lg := mixBaseB_K1_tenth_le hLg0
  have hKa : (50100 / Real.log 3) / 10 * Lg ≤ ((ell - n : ℕ) : ℝ) := hK1a.trans hg1'
  have hKb : (50100 / Real.log 3) / 10 * Lg ≤ ((mb - ell : ℕ) : ℝ) := hK1a.trans hg2'
  have hKc : (mb : ℝ) ≤ (L : ℝ) + (50100 / Real.log 3) / 2 * Lg := by
    have := mul_nonneg (sub_nonneg.2 mixBaseB_K1_half_ge) hLg0
    linarith only [hcase, this]
  obtain ⟨X3loc, hX3M, hX3O, hX3b⟩ := hLoc Cg hCgl nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 mb n
    ell L hnell hellm hellL.le hell1 hL1 hm1 hKa hKb hKc
  obtain ⟨X1g, X2g, X3g, hX1gM, hX1gO, hX2gM, hX2gO, hX3gM, hX3gO, hGb⟩ :=
    hGauge Cg hCgg nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell L n mb hnell hellL hm1 hKa hKc
  have hcomp := mixFin_annealedComparison (C := Cg) hCg1 nu hnu hPrefix hJ2 hJ3 hJ4 ell L n mb
    hm1 hnmb hellL ⟨X3loc, hX3M, hX3O, hX3b⟩
    ⟨X1g, X2g, X3g, hX1gM, hX1gO, hX2gM, hX2gO, hX3gM, hX3gO, hGb⟩
  have hhalf := hCa C hCa' nu σ hnu hnu1 hσpos L n ell mb hn1 hnell hellL hnmb hσB hgap hw1
  simp only [mixTerms_Aell] at hcomp hX3b
  set τ12 : ℝ := gammaMomentConst 2 * (Cg * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        σ ^ (-(1 : ℝ))) + gammaMomentConst 1 * (Cg * ((L - ell : ℕ) : ℝ) * σ ^ (-(2 : ℝ)))
    with hτ12
  set τ3 : ℝ := gammaMomentConst ((1 : ℝ) / 3) * (gammaTriangleConst ((1 : ℝ) / 3) *
        (2 * (Cg * (mb : ℝ) ^ (-(5000 : ℝ))))) with hτ3
  have hu0 : (0 : ℝ) < ((L - ell : ℕ) : ℝ) := by
    have : 0 < L - ell := by omega
    exact_mod_cast this
  have hτ12pos : 0 < τ12 := by
    have h1 : 0 < gammaMomentConst 2 * (Cg * ((L - ell : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        σ ^ (-(1 : ℝ))) :=
      mul_pos hg2 (mul_pos (mul_pos hCg0 (Real.rpow_pos_of_pos hu0 _))
        (Real.rpow_pos_of_pos hσpos _))
    have h2 : 0 ≤ gammaMomentConst 1 * (Cg * ((L - ell : ℕ) : ℝ) * σ ^ (-(2 : ℝ))) :=
      mul_nonneg hg1.le (mul_nonneg (mul_nonneg hCg0.le hu0.le) (Real.rpow_nonneg hσpos.le _))
    rw [hτ12]
    linarith only [h1, h2]
  have hτ3nn : 0 ≤ τ3 := by
    rw [hτ3]
    exact mul_nonneg hg3.le (mul_nonneg hg4.le (mul_nonneg (by norm_num)
      (mul_nonneg hCg0.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))))
  have hτpos : 0 < τ12 + τ3 := by linarith only [hτ12pos, hτ3nn]
  set lam : ℝ := τ12 / (τ12 + τ3) with hlam
  have hlamτ : lam * (τ12 + τ3) = τ12 := by rw [hlam]; field_simp
  have hlam0 : 0 ≤ lam := div_nonneg hτ12pos.le hτpos.le
  have hlam1 : 0 ≤ 1 - lam := by
    rw [hlam, sub_nonneg, div_le_one hτpos]
    linarith only [hτ3nn]
  have hlamτ' : (1 - lam) * (τ12 + τ3) = τ3 := by linarith only [hlamτ]
  have hdom := mixBaseC_dom hnu hPrefix hJ2 hJ3 hJ4 ell L n hhalf hcomp
  have hK0Xlog : K0X * Lg ≤ ((ell - n : ℕ) : ℝ) := by
    have : K0X * Lg ≤ 5 * Lg := mul_le_mul_of_nonneg_right hK0X5 hLg0
    linarith only [this, hg1', hLg0]
  obtain ⟨X1, X2, hX1M, hX1O, hX2M, hX2O, hX12b⟩ := hX12 (C / 4) hC4 nu hnu hnu1 P hPrefix hJ1V2
    hJ2 hJ3 hJ4 n L ell mb hL1 hnell hellL hK0Xlog (τ12 + τ3) hhalf hcomp
  -- the corrected bilinear bounds
  have hQLn : ∀ p : BlockVec d, 0 ≤ blockVecDot p (blockMatVecMul
      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) := fun p => (hdom p).1
  have hneg : ∀ p q : BlockVec d, -(2 * mixBaseD_G0 nu ell L P n p q) ≤
      (τ12 + τ3) * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)) := by
    intro p q
    have h := hcomp (-p) q
    rw [mixBaseA_quad_neg] at h
    simp only [mixBaseA_blockVecDot_neg_left] at h
    unfold mixBaseD_G0
    linarith only [h]
  have hQes : ∀ p q : BlockVec d,
      blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q) ≤
      2 * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) := by
    intro p q
    linarith only [(hdom p).2, (hdom q).2]
  have hQesnn : ∀ p q : BlockVec d, 0 ≤ blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q) := by
    intro p q
    have hsE := sigmaBarScalar_originCube_pos hnu ell hPrefix hJ2 hJ3 hJ4 (n : ℤ)
    have huE := sigmaBarStarInvScalar_pos_cutoff hnu ell hPrefix hJ2 hJ3 hJ4 (n : ℤ)
    rw [mixMain_annealedBilinear_eq hnu ell hJ4 (n : ℤ) p,
      mixMain_annealedBilinear_eq hnu ell hJ4 (n : ℤ) q]
    nlinarith only [mul_nonneg hsE.le (vecNormSq_nonneg p.1),
      mul_nonneg huE.le (vecNormSq_nonneg p.2), mul_nonneg hsE.le (vecNormSq_nonneg q.1),
      mul_nonneg huE.le (vecNormSq_nonneg q.2)]
  have hb1 : ∀ (omega : ShellSeq d) (p q : BlockVec d),
      2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun R' => mixBase_F1 nu ell L P (n : ℤ) R' omega p q -
            lam * mixBaseD_G0 nu ell L P n p q) ≤
        (X1 omega + 2 * τ12) *
          (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) := by
    intro omega p q
    have hsub : descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun R' => mixBase_F1 nu ell L P (n : ℤ) R' omega p q -
            lam * mixBaseD_G0 nu ell L P n p q) =
        descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun R' => mixBase_F1 nu ell L P (n : ℤ) R' omega p q) -
          lam * mixBaseD_G0 nu ell L P n p q := by
      rw [mixBaseA_avg_sub _ _ (fun R' => mixBase_F1 nu ell L P (n : ℤ) R' omega p q)
        (fun _ => lam * mixBaseD_G0 nu ell L P n p q), mixBaseA_avg_const]
    rw [hsub]
    have hB1 := (hX12b omega p q).1
    have hn1' := mul_le_mul_of_nonneg_left (hneg p q) hlam0
    have hcalc : lam * ((τ12 + τ3) * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q))) =
        τ12 * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)) := by
      rw [← mul_assoc, hlamτ]
    have hn2 := mul_le_mul_of_nonneg_left (hQes p q) hτ12pos.le
    have e : (X1 omega + 2 * τ12) * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) =
        X1 omega * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) +
          τ12 * (2 * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q))) := by ring
    rw [e]
    linarith only [hB1, hn1', hcalc, hn2]
  have hb3 : ∀ (omega : ShellSeq d) (p q : BlockVec d),
      2 * descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun R' => blockVecDot p (blockMatVecMul
              (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R') q) -
            (1 - lam) * mixBaseD_G0 nu ell L P n p q) ≤
        (2 * |X3loc omega| + 2 * τ3) *
          (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) := by
    intro omega p q
    have hsub : descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun R' => blockVecDot p (blockMatVecMul
              (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R') q) -
            (1 - lam) * mixBaseD_G0 nu ell L P n p q) =
        descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun R' => blockVecDot p (blockMatVecMul
              (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R') q)) -
          (1 - lam) * mixBaseD_G0 nu ell L P n p q := by
      rw [mixBaseA_avg_sub _ _ (fun R' => blockVecDot p (blockMatVecMul
              (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R') q))
        (fun _ => (1 - lam) * mixBaseD_G0 nu ell L P n p q), mixBaseA_avg_const]
    rw [hsub]
    have hloc := hX3b omega p q
    have havg : descendantsAverage (originCube d (mb : ℤ)) (mb - n)
          (fun R' => blockVecDot p (blockMatVecMul
              (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R') q)) =
        ((descendantsAtDepth (originCube d (mb : ℤ)) (mb - n)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (mb : ℤ)) (mb - n),
            blockVecDot p (blockMatVecMul
              (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q) := rfl
    rw [havg]
    have hn1' := mul_le_mul_of_nonneg_left (hneg p q) hlam1
    have hcalc : (1 - lam) * ((τ12 + τ3) * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q))) =
        τ3 * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)) := by
      rw [← mul_assoc, hlamτ']
    have hQ := hQesnn p q
    have h1 : X3loc omega * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)) ≤
        |X3loc omega| * (blockVecDot p (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) p) +
        blockVecDot q (blockMatVecMul
          (annealedBlockMatrix nu ell P (cubeSet (originCube d (n : ℤ)))) q)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hQ
    have h2 := mul_le_mul_of_nonneg_left (hQes p q) (add_nonneg (abs_nonneg (X3loc omega)) hτ3nn)
    have e : (2 * |X3loc omega| + 2 * τ3) * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)) =
        (|X3loc omega| + τ3) * (2 * (blockVecDot p (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
            blockVecDot q (blockMatVecMul
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q))) := by ring
    rw [e]
    linarith only [hloc, hn1', hcalc, h1, h2]
  -- amplitudes
  have hwn' : ((L - n : ℕ) : ℝ) = (L : ℝ) - (n : ℝ) := Nat.cast_sub hnL.le
  have huw : ((L - ell : ℕ) : ℝ) ≤ ((L - n : ℕ) : ℝ) := by
    exact_mod_cast (by omega : L - ell ≤ L - n)
  have hcomp12 := mixBaseD_amp_comp (a1 := gammaMomentConst 2) (a2 := gammaMomentConst 1)
    (Cg := Cg) (C := C) (σ := σ) (u := ((L - ell : ℕ) : ℝ)) (w := ((L - n : ℕ) : ℝ)) hg2.le
    hg1.le hCg0.le hC1 hσpos hu0.le huw (by rw [hwn']; exact hgap)
  have hamp1nn : 0 ≤ ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hσpos.le _)
  have hamp2nn : 0 ≤ ((L - n : ℕ) : ℝ) * σ ^ (-(2 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hσpos.le _)
  have hδ1 : 2 * τ12 ≤ C / 4 * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)) := by
    have h1 : 2 * τ12 ≤ 2 * ((gammaMomentConst 2 + gammaMomentConst 1) * Cg *
        (((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)))) := by
      rw [hτ12]; linarith only [hcomp12]
    have h2 : 2 * ((gammaMomentConst 2 + gammaMomentConst 1) * Cg) ≤ C / 4 := by
      have : S1 = 8 * (gammaMomentConst 1 + gammaMomentConst 2) * Cg := hS1
      linarith only [hCS1, this]
    have h3 := mul_le_mul_of_nonneg_right h2 hamp1nn
    have e : C / 4 * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)) =
        C / 4 * (((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) := by ring
    rw [e]
    linarith only [h1, h3]
  have hX1O' : IsBigO P.toMeasure (gammaSigma 2) (fun omega => X1 omega + 2 * τ12)
      (C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) := by
    refine (mixBaseA_isBigO_add_const hX1O (by linarith only [hτ12pos]) hδ1).mono_scale ?_
    have e : C * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)) =
        C * (((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) := by ring
    have e2 : 2 * (C / 4 * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) =
        C / 2 * (((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_right (by linarith only [hCpos]) hamp1nn
  have hX2O' : IsBigO P.toMeasure (gammaSigma 1) X2
      (C * ((L - n : ℕ) : ℝ) * σ ^ (-(2 : ℝ))) := by
    refine hX2O.mono_scale ?_
    have e : C * ((L - n : ℕ) : ℝ) * σ ^ (-(2 : ℝ)) =
        C * (((L - n : ℕ) : ℝ) * σ ^ (-(2 : ℝ))) := by ring
    have e2 : C / 4 * ((L - n : ℕ) : ℝ) * σ ^ (-(2 : ℝ)) =
        C / 4 * (((L - n : ℕ) : ℝ) * σ ^ (-(2 : ℝ))) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_right (by linarith only [hCpos]) hamp2nn
  have hmp5 : (0 : ℝ) ≤ (mb : ℝ) ^ (-(5000 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmp53 : (mb : ℝ) ^ (-(5000 : ℝ)) ≤ (mb : ℝ) ^ (-(3000 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm1) (by norm_num)
  have hX3O' : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3))
      (fun omega => 2 * |X3loc omega| + 2 * τ3) (C * (mb : ℝ) ^ (-(3000 : ℝ))) := by
    have h1 : IsBigO P.toMeasure (gammaSigma ((1 : ℝ) / 3)) (fun omega => |X3loc omega|)
        (Cg * (mb : ℝ) ^ (-(5000 : ℝ))) :=
      hX3O.of_abs_le (fun omega => by simp)
    have h2 := h1.const_mul (c := 2) (by norm_num)
    set A3 : ℝ := (2 * Cg + 4 * gammaMomentConst ((1 : ℝ) / 3) * gammaTriangleConst ((1 : ℝ) / 3) *
      Cg) * (mb : ℝ) ^ (-(5000 : ℝ)) with hA3
    have hA3le : 2 * (Cg * (mb : ℝ) ^ (-(5000 : ℝ))) ≤ A3 := by
      have : 0 ≤ 4 * gammaMomentConst ((1 : ℝ) / 3) * gammaTriangleConst ((1 : ℝ) / 3) * Cg *
          (mb : ℝ) ^ (-(5000 : ℝ)) := by positivity
      rw [hA3]; linarith only [this]
    have hδ3 : 2 * τ3 ≤ A3 := by
      have : 2 * τ3 = 4 * gammaMomentConst ((1 : ℝ) / 3) * gammaTriangleConst ((1 : ℝ) / 3) *
          Cg * (mb : ℝ) ^ (-(5000 : ℝ)) := by rw [hτ3]; ring
      have h0 : 0 ≤ 2 * Cg * (mb : ℝ) ^ (-(5000 : ℝ)) := by positivity
      rw [this, hA3]; linarith only [h0]
    refine (mixBaseA_isBigO_add_const (h2.mono_scale hA3le) (by linarith only [hτ3nn]) hδ3).mono_scale ?_
    have : 2 * A3 ≤ C * (mb : ℝ) ^ (-(5000 : ℝ)) := by
      have e : 2 * A3 = (4 * Cg + 8 * gammaMomentConst ((1 : ℝ) / 3) *
          gammaTriangleConst ((1 : ℝ) / 3) * Cg) * (mb : ℝ) ^ (-(5000 : ℝ)) := by rw [hA3]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hCS3 hmp5
    exact this.trans (mul_le_mul_of_nonneg_left hmp53 hCpos.le)
  refine ⟨fun R omega p q => mixBase_F1 nu ell L P (n : ℤ) R omega p q -
      lam * mixBaseD_G0 nu ell L P n p q,
    mixBase_F2 nu ell L P (n : ℤ),
    fun R omega p q => blockVecDot p (blockMatVecMul
        (mixTerms_localizationTermMatrix nu omega ell L P (n : ℤ) R) q) -
      (1 - lam) * mixBaseD_G0 nu ell L P n p q,
    ?_, ?_, ?_, ?_, ?_, ?_, fun omega => X1 omega + 2 * τ12, X2,
    fun omega => 2 * |X3loc omega| + 2 * τ3, hX1M.add measurable_const, hX1O', hX2M, hX2O',
    (hX3M.abs.const_mul 2).add measurable_const, hX3O', ?_⟩
  · intro R omega p q
    have h := mixBase_sum_eq hnu omega ell L hJ4 (n : ℤ) R p q
    rw [← h]
    simp only [mixBase_F3, mixTerms_Aell, mixBaseD_G0]
    ring
  · intro zreal w Q omega p q hset
    beta_reduce
    rw [mixBase_F1_hFcov nu ell L P (n : ℤ) zreal w Q omega p q hset]
  · exact mixBase_F2_hFcov nu ell L P (n : ℤ)
  · intro zreal w Q omega p q hset
    beta_reduce
    rw [mixBase_localizationTermMatrix_translate nu ell L P (n : ℤ) zreal w Q omega hset]
  · intro h
    exact absurd h (not_le.2 hnL)
  · intro h
    exact absurd h (not_le.2 hnL)
  · intro omega p q
    exact ⟨hb1 omega p q, (hX12b omega p q).2, hb3 omega p q⟩

end

end SuperdiffusionCLT.Section4.Mixing
