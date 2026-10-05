/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationT2Printed
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayK
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayG
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayE

/-!
# The printed localization average, including the singleton grid

Proves the conclusion of `l.localization.average`,
using the signed colour-class concentration from its proof.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory

variable {d : ℕ}

/-- A weight constant covering both singleton and larger grids. -/
noncomputable def localizationAveragePrintedWeightConst (d : ℕ) : ℝ :=
  localizationT2PrintedWeightConst d +
    ((1 + 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) *
      (2 * (1 + localizationDisplayI_gaugeConst d ^ 2)))

/-- The maximum-weight tail also holds when the grid consists of one cube. -/
theorem localizationAveragePrinted_weight [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l L m n : ℕ) (hnm : n ≤ m) (v : Homogenization.BlockVec d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => (localizationAverageGrid d m n).sup'
        (localizationAverageGrid_nonempty m n) (fun R => localizationW nu l L R v omega))
      (localizationAverageWbarAmplitude (localizationAveragePrintedWeightConst d)
        nu l L m n v) := by
  have hdot := SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg v
  have hc := localizationDisplayI_weightConst_pos d
  have ho : 0 < localizationT2PrintedWeightConst d := by
    unfold localizationT2PrintedWeightConst
    have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  rcases lt_or_eq_of_le hnm with hlt | heq
  · have hb := localizationAverage_wbar_bound_of_cube_bounds' hc hnu P l L m n v
      (localizationAverageGrid d m n) (localizationAverageGrid_nonempty m n)
      (localizationAverageGrid_card_ge_two hlt (NeZero.pos d))
      (fun R => localizationW nu l L R v) _ (fun _ => rfl)
      (fun R _ omega => sq_nonneg _)
      (localizationDisplayI_hcube hPrefix hJ2 hJ3 hJ4 hnu hnu1 l L m n v)
      (localizationAverageGrid_card_le m n)
    apply hb.mono_scale
    change localizationAverageWbarAmplitude (localizationT2PrintedWeightConst d) _ _ _ _ _ _ ≤ _
    unfold localizationAverageWbarAmplitude localizationAveragePrintedWeightConst
    gcongr
    exact le_add_of_nonneg_right hc.le
  · subst n
    have hg : localizationAverageGrid d m m = {Homogenization.originCube d (m : ℤ)} := by
      simp only [localizationAverageGrid, Nat.sub_self, Homogenization.descendantsAtDepth_zero]
    have hb := localizationDisplayI_hcube hPrefix hJ2 hJ3 hJ4 hnu hnu1 l L m m v
      (Homogenization.originCube d (m : ℤ)) (by rw [hg]; exact Finset.mem_singleton_self _)
    simp only [hg, Finset.sup'_singleton]
    apply hb.mono_scale
    unfold localizationAverageWbarCubeAmplitude localizationAverageWbarAmplitude
    simp only [Nat.sub_self, Nat.cast_zero, max_eq_left zero_le_one, mul_one]
    rw [mul_right_comm _ (max 1 (l : ℝ) * max 1 (L : ℝ))]
    gcongr
    exact le_add_of_nonneg_left ho.le

/-- The signed T2 estimate for all scales in the main statement. -/
theorem localizationAveragePrinted_T2_bound [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {n l m : ℕ} (hnl : n ≤ l) (hlm : l ≤ m)
    (L : ℕ) (v : Homogenization.BlockVec d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 2))
      (localizationT2 nu l L P m n v)
      (localizationAverageEnvelopeT2
        (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
          (localizationAveragePrintedWeightConst d * localizationT2PrintedSumConst d)) nu l L m n v) := by
  obtain ⟨U, hU, hfactor⟩ := localizationT2Printed_factor hnu P hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm L v
  have hW := localizationAveragePrinted_weight hnu hnu1 P hPrefix hJ2 hJ3 hJ4
    l L m n (hnl.trans hlm) v
  have htri := Homogenization.IndependentSums.gammaTriangleConst_pos (σ := (1 : ℝ))
  have hsum := gammaSigmaIndependentSumConst_one_pos
  have hU' : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) U
      (localizationT2PrintedSumConst d * localizationAverageNormalisedAmplitude d m l) := by
    apply hU.mono_scale
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (localizationT2Printed_color_decay (d := d) hnl hlm)
        (mul_nonneg htri.le hsum.le)) (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1
    unfold localizationT2PrintedSumConst
    ring
  have hWpos : 0 < localizationAveragePrintedWeightConst d := by
    have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hc := localizationDisplayI_weightConst_pos d
    unfold localizationAveragePrintedWeightConst localizationT2PrintedWeightConst
    positivity
  have hUpos : 0 < localizationT2PrintedSumConst d := by
    unfold localizationT2PrintedSumConst
    positivity
  have hraw := localizationAverage_T2_of_factor_bound P _ _ U hfactor
    (localizationAverageWbarAmplitude_nonneg hWpos.le hnu.le l L m n v)
    (mul_nonneg hUpos.le (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le) hW hU'
  have heq : SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
      (localizationAverageWbarAmplitude (localizationAveragePrintedWeightConst d) nu l L m n v *
        (localizationT2PrintedSumConst d * localizationAverageNormalisedAmplitude d m l)) =
      localizationAverageT2RawAmplitude
        (localizationAveragePrintedWeightConst d * localizationT2PrintedSumConst d) nu l L m n v := by
    unfold localizationAverageT2RawAmplitude localizationAverageWbarAmplitude
    ring
  change Homogenization.IndependentSums.IsBigO _ _ _
    (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
      (localizationAverageWbarAmplitude (localizationAveragePrintedWeightConst d) nu l L m n v *
        (localizationT2PrintedSumConst d * localizationAverageNormalisedAmplitude d m l))) at hraw
  rw [heq] at hraw
  exact hraw.mono_scale (localizationAverage_T2_rawAmplitude_le
    (mul_pos hWpos hUpos) hnu hnu1 l L m n v)



/-- The dimension-only constant for the first summand. -/
noncomputable def localizationAveragePrintedT1Const (d : ℕ) : ℝ :=
  localizationAverageT1Const * localizationAverageT1CubeBoundConst
    (localizationDisplayKConst d + localizationDisplayKConst d ^ 2)
    (SuperdiffusionCLT.Probability.orliczProductConst 1 1) (localizationDisplayGConst d)

/-- The first summand, with every per-cube estimate supplied by the shell laws. -/
theorem localizationAveragePrinted_T1_bound [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (m n l L : ℕ) (hnl : n ≤ l) (hlm : l ≤ m) (v : Homogenization.BlockVec d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3))
      (localizationT1Carrier nu l L m n v)
      (localizationAverageEnvelopeT1 (localizationAveragePrintedT1Const d) nu l L n v) := by
  have hCd : 0 < localizationDisplayKConst d + localizationDisplayKConst d ^ 2 :=
    add_pos_of_pos_of_nonneg localizationDisplayKConst_pos (sq_nonneg _)
  unfold localizationAveragePrintedT1Const
  refine localizationAverage_T1_of_descendantGrid_cubeBounds
    (KY := SuperdiffusionCLT.Probability.orliczProductConst 1 1)
    (CR := localizationDisplayGConst d) hCd hnu P l L m n v
    (localizationDz nu l L) (fun R => localizationB nu l L R v)
    (localizationT1Carrier nu l L m n v)
    (fun omega => ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
      ∑ R ∈ localizationAverageGrid d m n, localizationDz nu l L R omega ^ 2)
    (fun omega => ((localizationAverageGrid d m n).card : ℝ)⁻¹ *
      ∑ R ∈ localizationAverageGrid d m n, localizationB nu l L R v omega ^ 2)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_
    (fun R => localizationY nu l R ^ 2) (fun R => localizationR nu l L R v)
    (SuperdiffusionCLT.Probability.orliczProductConst_pos 1 1)
    localizationDisplayGConst_pos ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun R _ omega => localizationD_nonneg hnu l L R omega
  · exact localizationB_nonneg_on_grid hnu l L m n v
  · exact fun h R _ omega => localizationD_eq_zero_of_not_lt h R omega
  · exact localizationDz_measurable_on_grid (nu := nu) l L m n
  · exact localizationB_measurable_on_grid hnu l L m n v
  · exact localizationDisplayK_hDd_grid hPrefix hJ3 hnu hnu1 hnl (hnl.trans hlm) L
  · exact fun _ _ _ => sq_nonneg _
  · exact fun _ _ _ => sq_nonneg _
  · exact fun R _ omega =>
      localizationB_sq_le_localizationY_sq_mul_localizationR hnu l L R v omega
  · exact fun h _ _ omega => localizationB_eq_zero_of_dot_eq_zero h omega
  · exact localizationY_sq_isBigO_on_grid_of_lawBinders_four P hnu hPrefix hJ2 hJ3 hJ4 l m n
  · exact localizationDisplayG_R_on_grid P hPrefix hJ2 hJ3 hJ4 hnu hnu1 l L m n hnl v

/-- A constant depending on the dimension alone for the full comparison. -/
noncomputable def localizationAveragePrintedConst (d : ℕ) : ℝ :=
  orliczAssemblyConst * max (localizationAveragePrintedT1Const d)
    (SuperdiffusionCLT.Probability.orliczProductConst 1 1 *
      (localizationAveragePrintedWeightConst d * localizationT2PrintedSumConst d))

/-- The witness estimate for every allowed scale, with no residual analytic premise. -/
theorem localizationAveragePrinted_witness {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (m n l L : ℕ) (hnl : n ≤ l) (hlm : l ≤ m) (hlL : l ≤ L)
    (v : Homogenization.BlockVec d) :
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X
        (localizationAverageEnvelope (localizationAveragePrintedConst d) nu l L m n v) ∧
      ∀ omega, |averagedGaugeComparison nu l L P m n v omega| ≤ X omega := by
  have : NeZero d := ⟨by have hd := hPrefix.dimension; omega⟩
  have hC1 : 0 < localizationAveragePrintedT1Const d :=
    mul_pos localizationAverageT1Const_pos
      (localizationAverageT1CubeBoundConst_pos
        (add_pos_of_pos_of_nonneg localizationDisplayKConst_pos (sq_nonneg _)))
  have hT1nn : ∀ omega, 0 ≤ localizationT1Carrier nu l L m n v omega := by
    intro omega
    unfold localizationT1Carrier
    refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg ?_)
    intro R hR
    exact mul_nonneg (localizationD_nonneg hnu l L R omega)
      (localizationB_nonneg_on_grid hnu l L m n v R hR omega)
  exact localization_average_witness_of_summandData hC1 hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4
    m n l L hnl hlm hlL v (localizationT1Carrier nu l L m n v)
    (fun omega => |localizationT2 nu l L P m n v omega|)
    (localizationT1Carrier_measurable hnu l L m n v)
    (continuous_abs.measurable.comp (measurable_localizationT2 hnu l L P m n v))
    hT1nn (fun _ => abs_nonneg _)
    (abs_averagedGaugeComparison_le_T1_add_localizationT2 nu l L P m n v
      (localizationDz nu l L) (localizationT1Carrier nu l L m n v) (fun _ => rfl)
      (fun R _ omega => localization_display_e_hpoint hnu hlL R v omega))
    (localizationAveragePrinted_T1_bound hnu hnu1 P hPrefix hJ2 hJ3 hJ4 m n l L hnl hlm v)
    ((localizationAveragePrinted_T2_bound hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 hnl hlm L v).of_abs_le
      (fun _ => le_of_eq (abs_abs _)))

/-- The exact localization-average conclusion, with its uniform constant. -/
theorem localization_average_of_printedT2
    (d : ℕ) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m n l L : ℕ, n ≤ l → l ≤ m → l ≤ L →
            ∀ Pvec : Homogenization.BlockVec d,
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma ((1 : ℝ) / 3)) X
                    (C * nu ^ (-(3 : ℝ)) *
                      Homogenization.blockVecDot Pvec Pvec *
                      ((if l < L then
                            (L : ℝ) * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ))
                          else 0) +
                        max 1 (l : ℝ) * max 1 (L : ℝ) * max 1 ((m - n : ℕ) : ℝ) *
                          (3 : ℝ) ^
                            (-((d : ℝ) / 2 * ((m - l : ℕ) : ℝ))))) ∧
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    |((Homogenization.descendantsAtDepth
                            (Homogenization.originCube d (m : ℤ))
                            (m - n)).card : ℝ)⁻¹ *
                        ∑ R ∈ Homogenization.descendantsAtDepth
                            (Homogenization.originCube d (m : ℤ)) (m - n),
                          Homogenization.blockVecDot Pvec
                            (Homogenization.blockMatVecMul
                              (Homogenization.ofFullBlockMat
                                (Homogenization.toFullBlockMat
                                    (Homogenization.coarseBlockMatrix
                                      (Homogenization.cubeSet R)
                                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                          nu omega L).toCoeffField) -
                                  Homogenization.toFullBlockMat
                                    (Homogenization.Book.Ch02.blockMatMul
                                      (Homogenization.Book.Ch02.blockMatTranspose
                                        (Homogenization.Book.Ch02.blockG
                                          (-Homogenization.volumeAverageMat
                                            (Homogenization.cubeSet R)
                                            (fun y =>
                                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                                omega l L y))))
                                      (Homogenization.Book.Ch02.blockMatMul
                                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix
                                          nu l P
                                          (Homogenization.cubeSet
                                            (Homogenization.originCube d (n : ℤ))))
                                        (Homogenization.Book.Ch02.blockG
                                          (-Homogenization.volumeAverageMat
                                            (Homogenization.cubeSet R)
                                            (fun y =>
                                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                                omega l L y)))))))
                              Pvec)| ≤
                      X omega := by
  refine ⟨localizationAveragePrintedConst d, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 m n l L hnl hlm hlL v
  exact localizationAveragePrinted_witness hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4
    m n l L hnl hlm hlL v

end SuperdiffusionCLT.Section2.Localization
