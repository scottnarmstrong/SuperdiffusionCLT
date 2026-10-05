/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.MeanValue
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayD
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB

/-!
# The gauge estimate and the per-cube localization weight

In the proof of `l.localization.average`, the squared gauge average
has `Γ₁` amplitude `C (L - l)`, and the weight `W_z` has amplitude
`C nu⁻¹ (1 ∨ l) (1 ∨ L) |P|²`. This file proves both from the shell laws.

The first spatial moment of the finite increment already has `Gamma_2`
amplitude `C sqrt (L - l)` by the independent-shell concentration and Jensen
averaging in `IncrementPthMoment`. The norm of its matrix average is at most
`d` times this moment. The power rule gives the squared gauge estimate.
The deterministic gauge inequality and DisplayD's envelope bound then give
`localizationDisplayI_hcube` with no intermediate probabilistic premises.

All cubes and all natural cutoffs are covered, including an empty shell
interval. The factor `1 ∨ (m - n)` belongs to the subsequent finite maximum
over cubes, and is absent from the individual-cube bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

variable {d : ℕ}
/-- The gauge shear increases squared length by at most `2 (1 + |h|²)`. -/
theorem localizationDisplayI_gauge_norm_sq_le (h : Homogenization.Mat d)
    (P : Homogenization.BlockVec d) :
    SuperdiffusionCLT.Section2.Carriers.blockVecNorm
      (Homogenization.blockMatVecMul (Homogenization.Book.Ch02.blockG h) P) ^ 2 ≤
      2 * (1 + Homogenization.Book.Ch02.matrixOperatorNorm h ^ 2) *
        Homogenization.blockVecDot P P := by
  have ha := Homogenization.vecNormSq_add_le (Homogenization.matVecMul h P.1) P.2
  have hb := Homogenization.Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq h P.1
  have hp := Homogenization.vecNormSq_nonneg P.1
  have hq := Homogenization.vecNormSq_nonneg P.2
  have hprod := mul_nonneg (sq_nonneg (Homogenization.Book.Ch02.matrixOperatorNorm h)) hq
  rw [SuperdiffusionCLT.Section2.Carriers.blockVecNorm_sq]
  simp only [Homogenization.blockVecDot, Homogenization.blockMatVecMul,
    Homogenization.Book.Ch02.blockG, Homogenization.matVecMul_one,
    Homogenization.zero_matVecMul, add_zero]
  change Homogenization.vecNormSq P.1 +
    Homogenization.vecNormSq (Homogenization.matVecMul h P.1 + P.2) ≤ _
  change _ ≤ 2 * (1 + Homogenization.Book.Ch02.matrixOperatorNorm h ^ 2) *
    (Homogenization.vecNormSq P.1 + Homogenization.vecNormSq P.2)
  nlinarith only [ha, hb, hp, hprod]

/-- The gauge average is controlled by the first absolute spatial moment. -/
theorem localizationDisplayI_average_norm_le (l L : ℕ) (R : Homogenization.TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    Homogenization.Book.Ch02.matrixOperatorNorm (localizationGaugeAverage l L R omega) ≤
      (d : ℝ) * Homogenization.volumeAverage (Homogenization.cubeSet R)
        (fun x => Homogenization.Book.Ch02.matrixOperatorNorm
          (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x)) := by
  let f := SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L
  let g := fun x => Homogenization.Book.Ch02.matrixOperatorNorm (f x)
  have hg : Continuous g :=
    SuperdiffusionCLT.Section2.Estimates.Stream.continuous_matrixOperatorNorm_finiteShellIncrement omega l L
  have hint : MeasureTheory.IntegrableOn g (Homogenization.cubeSet R) MeasureTheory.volume :=
    (hg.locallyIntegrable.integrableOn_isCompact
      (Homogenization.isBounded_cubeSet R).isCompact_closure).mono_set subset_closure
  have hnn : 0 ≤ Homogenization.volumeAverage (Homogenization.cubeSet R) g :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (MeasureTheory.integral_nonneg fun x => Homogenization.Book.Ch02.matrixOperatorNorm_nonneg (f x))
  apply SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_le_of_entry_bound _ hnn
  intro i j
  change |(MeasureTheory.volume (Homogenization.cubeSet R)).toReal⁻¹ *
    ∫ x in Homogenization.cubeSet R, f x i j| ≤ _
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  calc |∫ x in Homogenization.cubeSet R, f x i j|
      ≤ ∫ x in Homogenization.cubeSet R, |f x i j| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ x in Homogenization.cubeSet R, g x := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => abs_nonneg _
      · exact hint
      · exact Filter.Eventually.of_forall fun x =>
          Homogenization.Book.Ch02.abs_entry_le_matrixOperatorNorm (f x) i j

/-- Dimension-only amplitude of the gauge average. -/
noncomputable def localizationDisplayI_gaugeConst (d : ℕ) : ℝ :=
  (d : ℝ) * (Real.exp 1 * (Homogenization.IndependentSums.gammaMomentConst 2 *
    SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst d))

/-- The gauge average has a square-root-gap `Gamma_2` tail on every cube. -/
theorem localizationDisplayI_gauge_tail
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l L : ℕ) (R : Homogenization.TriadicCube d) :
    Homogenization.IndependentSums.IsBigOWith P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2)
      (fun omega => Homogenization.Book.Ch02.matrixOperatorNorm
        (localizationGaugeAverage l L R omega))
      (localizationDisplayI_gaugeConst d * Real.sqrt ((L - l : ℕ) : ℝ)) := by
  by_cases hlL : l < L
  · have hav := SuperdiffusionCLT.Section2.Estimates.Stream.isBigOWith_gammaSigma_finiteShellIncrementPthMoment
      hPrefix hJ2 hJ3 hJ4 (p := 1) le_rfl hlL R
    simp only [div_one, Real.rpow_one] at hav
    have hs := hav.const_mul (c := (d : ℝ)) (Nat.cast_nonneg d)
    have heq : (d : ℝ) * (Real.exp 1 * (Homogenization.IndependentSums.gammaMomentConst 2 *
        (SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst d *
          Real.sqrt ((L - l : ℕ) : ℝ)))) =
        localizationDisplayI_gaugeConst d * Real.sqrt ((L - l : ℕ) : ℝ) := by
      unfold localizationDisplayI_gaugeConst
      ring
    rw [heq] at hs
    exact hs.of_le fun omega => localizationDisplayI_average_norm_le l L R omega
  · have hzero : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
        localizationGaugeAverage l L R omega = 0 := by
      intro omega
      have hi : Finset.Ioc l L = ∅ := Finset.Ioc_eq_empty hlL
      simp only [localizationGaugeAverage, SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement,
        hi, Finset.sum_empty, Homogenization.RegCoeffField.zero_apply]
      ext i j
      simp only [Homogenization.volumeAverageMat, Homogenization.volumeAverage,
        Matrix.zero_apply, MeasureTheory.integral_zero, mul_zero]
    intro t ht
    have hevent : Homogenization.IndependentSums.upperTailEvent
        (fun omega => Homogenization.Book.Ch02.matrixOperatorNorm
          (localizationGaugeAverage l L R omega))
        (localizationDisplayI_gaugeConst d * Real.sqrt ((L - l : ℕ) : ℝ) * t) = ∅ := by
      have hgap : L - l = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlL)
      ext omega
      simp only [Homogenization.IndependentSums.mem_upperTailEvent, hzero, hgap,
        Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul,
        Homogenization.Book.Ch02.matrixOperatorNorm_zero, lt_self_iff_false, Set.mem_empty_iff_false]
    rw [hevent, MeasureTheory.measureReal_empty,
      Homogenization.IndependentSums.gammaSigma_inv]
    exact (Real.exp_pos _).le

/-- The squared gauge average has the printed linear gap amplitude. -/
theorem localizationDisplayI_gauge_sq_tail
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l L : ℕ) (R : Homogenization.TriadicCube d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => Homogenization.Book.Ch02.matrixOperatorNorm
        (localizationGaugeAverage l L R omega) ^ 2)
      (localizationDisplayI_gaugeConst d ^ 2 * ((L - l : ℕ) : ℝ)) := by
  have hc : 0 ≤ localizationDisplayI_gaugeConst d := by
    unfold localizationDisplayI_gaugeConst
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2)).le
        (SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst_pos hPrefix).le))
  have hs := Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow
    (p := 2) (by norm_num) (mul_nonneg hc (Real.sqrt_nonneg _))
    (fun omega => Homogenization.Book.Ch02.matrixOperatorNorm_nonneg
      (localizationGaugeAverage l L R omega))
    (localizationDisplayI_gauge_tail hPrefix hJ2 hJ3 hJ4 l L R)
  have hh : (2 : ℝ) / 2 = 1 := by norm_num
  simp only [hh, Real.rpow_two, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (L - l))] at hs
  exact (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (fun _ => sq_nonneg _)).mp hs

/-- The pointwise gauge estimate in the localization carriers. -/
theorem localizationDisplayI_gaugeVector_sq_le (l L : ℕ) (R : Homogenization.TriadicCube d)
    (Pvec : Homogenization.BlockVec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    SuperdiffusionCLT.Section2.Carriers.blockVecNorm
      (localizationGaugeVector l L R Pvec omega) ^ 2 ≤
      2 * (1 + Homogenization.Book.Ch02.matrixOperatorNorm
        (localizationGaugeAverage l L R omega) ^ 2) * Homogenization.blockVecDot Pvec Pvec := by
  have h := localizationDisplayI_gauge_norm_sq_le
    (-localizationGaugeAverage l L R omega) Pvec
  rw [SuperdiffusionCLT.Frozen.Assumptions.ShellField.matrixOperatorNorm_neg_eq] at h
  exact h

/-- The squared gauge vector has the printed amplitude, with no stochastic estimate assumed. -/
theorem localizationDisplayI_gaugeVector_tail
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l L : ℕ) (R : Homogenization.TriadicCube d) (Pvec : Homogenization.BlockVec d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => SuperdiffusionCLT.Section2.Carriers.blockVecNorm
        (localizationGaugeVector l L R Pvec omega) ^ 2)
      ((2 * (1 + localizationDisplayI_gaugeConst d ^ 2)) * max 1 (L : ℝ) *
        Homogenization.blockVecDot Pvec Pvec) := by
  let X := fun omega => Homogenization.Book.Ch02.matrixOperatorNorm
    (localizationGaugeAverage l L R omega) ^ 2
  let A := localizationDisplayI_gaugeConst d ^ 2 * ((L - l : ℕ) : ℝ)
  have hx : Homogenization.IndependentSums.IsBigOWith P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) X A :=
    (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
      (fun _ => sq_nonneg _)).mpr (localizationDisplayI_gauge_sq_tail hPrefix hJ2 hJ3 hJ4 l L R)
  have hplus : Homogenization.IndependentSums.IsBigOWith P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) (fun omega => 1 + X omega) (1 + A) := by
    intro t ht
    refine (MeasureTheory.measureReal_mono ?_).trans (hx ht)
    intro omega homega
    change (1 + A) * t < 1 + X omega at homega
    change A * t < X omega
    nlinarith only [homega, ht]
  have hd : 0 ≤ Homogenization.blockVecDot Pvec Pvec := SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg _
  have hs := hplus.const_mul (c := 2 * Homogenization.blockVecDot Pvec Pvec)
    (mul_nonneg (by norm_num) hd)
  have hdom : Homogenization.IndependentSums.IsBigOWith P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => SuperdiffusionCLT.Section2.Carriers.blockVecNorm
        (localizationGaugeVector l L R Pvec omega) ^ 2)
      ((2 * Homogenization.blockVecDot Pvec Pvec) * (1 + A)) := by
    refine hs.of_le fun omega => ?_
    convert localizationDisplayI_gaugeVector_sq_le l L R Pvec omega using 1
    ring
  apply (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (fun _ => sq_nonneg _)).mp
  refine hdom.mono_scale ?_
  have hgap : ((L - l : ℕ) : ℝ) ≤ max 1 (L : ℝ) :=
    (Nat.cast_le.mpr (Nat.sub_le L l)).trans (le_max_right _ _)
  have hmax : (1 : ℝ) ≤ max 1 (L : ℝ) := le_max_left _ _
  have ha : 1 + A ≤ (1 + localizationDisplayI_gaugeConst d ^ 2) * max 1 (L : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hgap (sq_nonneg (localizationDisplayI_gaugeConst d))
    dsimp [A]
    nlinarith only [hm, hmax]
  have hm := mul_le_mul_of_nonneg_left ha (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd)
  nlinarith only [hm]

/-- The per-cube weight bound `hcube`, from the shell-law assumptions. -/
theorem localizationDisplayI_hcube
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (l L m n : ℕ) (Pvec : Homogenization.BlockVec d) :
    ∀ R ∈ localizationAverageGrid d m n,
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1) (localizationW nu l L R Pvec)
        (localizationAverageWbarCubeAmplitude
          ((1 + 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) *
            (2 * (1 + localizationDisplayI_gaugeConst d ^ 2))) nu l L Pvec) := by
  apply localizationW_isBigO_on_grid_of_gaugeVectorNormSq hnu hnu1 l L m n Pvec P
    (CG := 2 * (1 + localizationDisplayI_gaugeConst d ^ 2)) (by positivity)
  intro R _
  exact localizationDisplayI_gaugeVector_tail hPrefix hJ2 hJ3 hJ4 l L R Pvec

/-- The constant supplied to the per-cube weight estimate is strictly positive. -/
theorem localizationDisplayI_weightConst_pos (d : ℕ) :
    0 < (1 + 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d) *
      (2 * (1 + localizationDisplayI_gaugeConst d ^ 2)) := by
  have hc := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst_pos d
  positivity

end SuperdiffusionCLT.Section2.Localization
