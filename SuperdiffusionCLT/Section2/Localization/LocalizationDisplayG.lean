/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationCubePassage
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB
public import SuperdiffusionCLT.Section2.Estimates.Stream.TranslatedIncrementLinfty

/-!
# The printed fourth-power localization display

The printed fourth-power estimate holds with a
constant depending only on dimension. The gauge leaves the first block fixed;
the second block of the envelope has no scale factor. Keeping these blocks
separate gives a bound by `C nu⁻¹ ((1 ∨ l) + S²) |P|²`, where `S` is the
translated increment supremum. Its existing `Gamma₂` bound has amplitude
`C sqrt (L-l)`. The power and sum rules, followed by the product rule, yield
the printed `Gamma_{1/2}` amplitude without a product of the two scales.

`localizationDisplayG_R_on_grid` supplies the printed `hR` display on the grid. Its
constant depends only on dimension.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

variable {d : ℕ}

/-- The gauge preserves the first block and changes only the second block. -/
theorem localizationDisplayG_gauge (h : Homogenization.Mat d)
    (v : Homogenization.BlockVec d) :
    Homogenization.blockMatVecMul (Homogenization.Book.Ch02.blockG h) v =
      (v.1, Homogenization.matVecMul h v.1 + v.2) := by
  rcases v with ⟨p, q⟩
  change (Homogenization.matVecMul 1 p + Homogenization.matVecMul 0 q,
    Homogenization.matVecMul h p + Homogenization.matVecMul 1 q) = _
  rw [Homogenization.matVecMul_one, Homogenization.zero_matVecMul,
    Homogenization.matVecMul_one, add_zero]

/-- The exact anisotropic envelope quadratic form after a gauge change. -/
theorem localizationDisplayG_quadratic {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (R : Homogenization.TriadicCube d) (v : Homogenization.BlockVec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    localizationW nu l L R v omega =
      SuperdiffusionCLT.Section2.Annealed.envelopeUpperScalar d nu l *
        Homogenization.vecNormSq v.1 +
      SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar d nu *
        Homogenization.vecNormSq
          (Homogenization.matVecMul (-Homogenization.volumeAverageMat
            (Homogenization.cubeSet R)
            (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
              omega l L y)) v.1 + v.2) := by
  rw [localizationW_eq_envelopeBlockMat hnu, localizationGaugeVector,
    localizationDisplayG_gauge]
  exact SuperdiffusionCLT.Section2.Annealed.blockVecDot_blockDiag_smul_one _ _ _ _

/-- Averaging the increment on a smaller cube preserves its supremum bound. -/
theorem localizationDisplayG_average_le
    (l L : ℕ) (R : Homogenization.TriadicCube d) (hRl : R.scale ≤ (l : ℤ))
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    Homogenization.Book.Ch02.matrixOperatorNorm
      (Homogenization.volumeAverageMat (Homogenization.cubeSet R)
        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L y)) ≤
      (d : ℝ) * SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound
        (Homogenization.cubeCenter R) l L omega := by
  have heq : Homogenization.volumeAverageMat (Homogenization.cubeSet R)
      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L y) =
      Homogenization.volumeAverageMat (Homogenization.openCubeSet R)
      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L y) := by
    ext i j
    exact localizationCubePassage_volumeAverage R _
  rw [heq]
  apply SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_volumeAverageMat_le
    (ne_of_lt (Homogenization.volume_openCubeSet_lt_top R))
    (SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound_nonneg _ _ _ _)
  intro y hy i j
  refine (Homogenization.Book.Ch02.abs_entry_le_matrixOperatorNorm _ i j).trans ?_
  have hsmall : y - Homogenization.cubeCenter R ∈
      Homogenization.openCubeSet (Homogenization.originCube d R.scale) := by
    rw [Homogenization.mem_openCubeSet_originCube_iff]
    intro k
    have hk := hy k
    change ((R.index k : ℝ) - 1/2) * (3 : ℝ)^R.scale < y k ∧
      y k < ((R.index k : ℝ) + 1/2) * (3 : ℝ)^R.scale at hk
    change -(1 / 2 : ℝ) * (3 : ℝ)^R.scale < y k - (R.index k : ℝ)*(3 : ℝ)^R.scale ∧
      y k - (R.index k : ℝ)*(3 : ℝ)^R.scale < (1 / 2 : ℝ) * (3 : ℝ)^R.scale
    constructor <;> linarith only [hk.1, hk.2]
  have hlarge := SuperdiffusionCLT.Frozen.Assumptions.ShellField.openCubeSet_originCube_subset_of_le hRl hsmall
  have h := SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_finiteShellIncrement_le_translatedIncrementSupBound
    (Homogenization.cubeCenter R) omega l L hlarge
  simpa only [add_sub_cancel] using h

/-- Keeping the lower block separate avoids multiplying the increment by the scale. -/
theorem localizationDisplayG_W_le {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (l L : ℕ) (R : Homogenization.TriadicCube d) (hRl : R.scale ≤ (l : ℤ))
    (v : Homogenization.BlockVec d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    localizationW nu l L R v omega ≤
      (1 + 6 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
        4 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d * (d : ℝ)^2) *
      nu⁻¹ *
      (max 1 (l : ℝ) +
        (SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound
          (Homogenization.cubeCenter R) l L omega)^2) * Homogenization.blockVecDot v v := by
  let C := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d
  let S := SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound
    (Homogenization.cubeCenter R) l L omega
  let H := Homogenization.volumeAverageMat (Homogenization.cubeSet R)
    (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L y)
  have hC : 0 < C := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst_pos d
  have hS : 0 ≤ S :=
    SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound_nonneg _ _ _ _
  have hH : Homogenization.Book.Ch02.matrixOperatorNorm H ≤ (d : ℝ) * S :=
    localizationDisplayG_average_le l L R hRl omega
  have hHsq := pow_le_pow_left₀ (Homogenization.Book.Ch02.matrixOperatorNorm_nonneg H) hH 2
  have hp := Homogenization.vecNormSq_nonneg v.1
  have hq := Homogenization.vecNormSq_nonneg v.2
  have hmul := Homogenization.Book.Ch02.vecNormSq_matVecMul_le_matrixOperatorNorm_sq_mul_vecNormSq
    (-H) v.1
  have hneg : Homogenization.Book.Ch02.matrixOperatorNorm (-H) =
      Homogenization.Book.Ch02.matrixOperatorNorm H := by
    unfold Homogenization.Book.Ch02.matrixOperatorNorm
    rw [map_neg, norm_neg]
  rw [hneg] at hmul
  have htri := Homogenization.vecNormSq_add_le (Homogenization.matVecMul (-H) v.1) v.2
  have hbound : Homogenization.vecNormSq (Homogenization.matVecMul (-H) v.1 + v.2) ≤
      2 * ((d : ℝ)^2 * S^2 * Homogenization.vecNormSq v.1 + Homogenization.vecNormSq v.2) := by
    have hs := mul_le_mul_of_nonneg_right hHsq hp
    nlinarith only [htri, hmul, hs]
  have hu := envelopeUpperScalar_le_nuInv_mul_max (d := d) hnu hnu1 l
  have hl : 0 ≤ SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar d nu :=
    (SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar_pos hnu d).le
  have hfirst := mul_le_mul_of_nonneg_right hu hp
  have hsecond := mul_le_mul_of_nonneg_left hbound hl
  rw [localizationDisplayG_quadratic hnu]
  change _ ≤ (1 + 6*C + 4*C*(d : ℝ)^2) * nu⁻¹ *
    (max 1 (l : ℝ) + S^2) * (Homogenization.vecNormSq v.1 + Homogenization.vecNormSq v.2)
  change _ + SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar d nu *
    Homogenization.vecNormSq (Homogenization.matVecMul (-H) v.1 + v.2) ≤ _
  apply (add_le_add hfirst hsecond).trans
  dsimp only [SuperdiffusionCLT.Section2.Annealed.envelopeLowerScalar]
  have ha : 1 ≤ max 1 (l : ℝ) := le_max_left _ _
  have hi : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hD : 0 ≤ (d : ℝ)^2 := sq_nonneg _
  have hS2 : 0 ≤ S^2 := sq_nonneg _
  change (1 + 2*C) * nu⁻¹ * max 1 (l : ℝ) * Homogenization.vecNormSq v.1 +
    (2*C*nu⁻¹) * (2*((d : ℝ)^2*S^2*Homogenization.vecNormSq v.1 + Homogenization.vecNormSq v.2)) ≤ _
  have hpcoef : (1+2*C)*max 1 (l : ℝ) + 4*C*(d : ℝ)^2*S^2 ≤
      (1+6*C+4*C*(d : ℝ)^2)*(max 1 (l : ℝ)+S^2) := by
    nlinarith only [mul_nonneg hC.le (le_trans zero_le_one ha),
      mul_nonneg (mul_nonneg hC.le hD) (le_trans zero_le_one ha),
      mul_nonneg hC.le hS2, hS2]
  have hqcoef : 4*C ≤ (1+6*C+4*C*(d : ℝ)^2)*(max 1 (l : ℝ)+S^2) := by
    have hbase : 4*C ≤ (1+6*C+4*C*(d : ℝ)^2) := by
      nlinarith only [hC, mul_nonneg hC.le hD]
    have hpos : 0 ≤ 1+6*C+4*C*(d : ℝ)^2 := le_trans (by positivity) hbase
    have hmon := mul_le_mul_of_nonneg_left (show 1 ≤ max 1 (l : ℝ)+S^2 by linarith only [ha,hS2]) hpos
    rw [mul_one] at hmon
    exact hbase.trans hmon
  have hh1 := mul_le_mul_of_nonneg_right hpcoef (mul_nonneg hi hp)
  have hh2 := mul_le_mul_of_nonneg_right hqcoef (mul_nonneg hi hq)
  nlinarith only [hh1, hh2]

/-- The deterministic coefficient in the blockwise estimate. -/
noncomputable def localizationDisplayGEnvelopeConst (d : ℕ) : ℝ :=
  1 + 6 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d +
    4 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d * (d : ℝ)^2

/-- A dimension-only constant for the printed fourth-power estimate. -/
noncomputable def localizationDisplayGConst (d : ℕ) : ℝ :=
  8 * (localizationDisplayGEnvelopeConst d * Homogenization.IndependentSums.gammaTriangleConst 1 *
    (1 + SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst d ^ 2)) ^ 2 +
    (1 + 2 * SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst d)^2

theorem localizationDisplayGConst_pos : 0 < localizationDisplayGConst d := by
  have hC := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst_pos d
  unfold localizationDisplayGConst
  exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) (sq_nonneg _))
    (sq_pos_of_pos (by linarith only [hC]))

/-- The scale sum can be squared without a product of the two scales. -/
theorem localizationDisplayG_square_sum {a b g : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hg : 0 ≤ g) :
    (a + b*g)^2 ≤ 2*(1+b)^2*(a^2+g^2) := by
  have hm : a + b*g ≤ (1+b)*(a+g) := by
    nlinarith only [mul_nonneg hb ha, hg]
  have hs := pow_le_pow_left₀ (add_nonneg ha (mul_nonneg hb hg)) hm 2
  have hadd : (a+g)^2 ≤ 2*(a^2+g^2) := by
    nlinarith only [sq_nonneg (a-g)]
  have hmul := mul_le_mul_of_nonneg_left hadd (sq_nonneg (1+b))
  nlinarith only [hs, hmul]

/-- The probability estimate for the scalar envelope of the blockwise bound. -/
theorem localizationDisplayG_scalar_tail
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {l L : ℕ} (hlL : l < L) (z : Homogenization.Vec d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1)
      (fun omega => max 1 (l : ℝ) +
        (SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound z l L omega)^2)
      (Homogenization.IndependentSums.gammaTriangleConst 1 *
        (max 1 (l : ℝ) +
          SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst d ^ 2 *
            ((L-l : ℕ) : ℝ))) := by
  let S := SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound z l L
  have hS : ∀ omega, 0 ≤ S omega :=
    SuperdiffusionCLT.Section2.Estimates.Stream.translatedIncrementSupBound_nonneg z l L
  have hC := SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst_pos hPrefix
  have hg : 0 < ((L-l : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlL
  have hraw := SuperdiffusionCLT.Section2.Estimates.Stream.isBigOWith_gammaSigma_translatedIncrementSupBound
    hPrefix hJ2 hJ3 hJ4 hlL z
  have ht : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) S
      (SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst d *
        Real.sqrt ((L-l : ℕ) : ℝ)) := by
    simpa only [Homogenization.IndependentSums.IsBigO, abs_of_nonneg (hS _)] using hraw
  have hsq := SuperdiffusionCLT.Probability.isBigO_gammaSigma_rpow_fwd
    (p := (2 : ℝ)) (by norm_num) (mul_nonneg hC.le (Real.sqrt_nonneg _)) hS ht
  have hsq' : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) (fun omega => S omega ^ 2)
      (SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst d ^ 2 *
        ((L-l : ℕ) : ℝ)) := by
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_two, mul_pow,
      Real.sq_sqrt hg.le] using hsq
  have ha : 0 < max 1 (l : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc := isBigO_gammaSigma_of_abs_le_const (μ := P.toMeasure) (σ := (1 : ℝ))
    ha.le (fun _ : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      le_of_eq (abs_of_pos ha))
  exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_add_of_isBigO
    (by norm_num) ha (mul_pos (sq_pos_of_pos hC) hg) hc hsq'
    measurable_const
    ((SuperdiffusionCLT.Section2.Estimates.Stream.measurable_translatedIncrementSupBound z l L).pow_const 2)

/-- The printed fourth-power estimate when the upper increment is nonempty. -/
theorem localizationDisplayG_R_of_lt
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {l L : ℕ} (hlL : l < L) (R : Homogenization.TriadicCube d)
    (hRl : R.scale ≤ (l : ℤ)) (v : Homogenization.BlockVec d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ)/2))
      (localizationR nu l L R v)
      (localizationAverageT1FourthAmplitude (localizationDisplayGConst d) nu l L v) := by
  let K := localizationDisplayGEnvelopeConst d
  let T := Homogenization.IndependentSums.gammaTriangleConst 1
  let B := SuperdiffusionCLT.Section2.Estimates.Stream.streamLinftyConst d ^ 2
  let a := max 1 (l : ℝ)
  let g : ℝ := ((L-l : ℕ) : ℝ)
  let N := Homogenization.blockVecDot v v
  let A := K * nu⁻¹ * N * (T * (a+B*g))
  have hC := SuperdiffusionCLT.Section2.Annealed.cutoffEnvelopeConst_pos d
  have hK : 0 ≤ K := by dsimp [K, localizationDisplayGEnvelopeConst]; positivity
  have hN : 0 ≤ N := SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg v
  have hi : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hT : 0 ≤ T := Homogenization.IndependentSums.gammaTriangleConst_pos.le
  have ha : 0 ≤ a := le_trans zero_le_one (le_max_left _ _)
  have hB : 0 ≤ B := sq_nonneg _
  have hg : 0 ≤ g := Nat.cast_nonneg _
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hK hi) hN)
    (mul_nonneg hT (add_nonneg ha (mul_nonneg hB hg)))
  have hs := (localizationDisplayG_scalar_tail P hPrefix hJ2 hJ3 hJ4 hlL
    (Homogenization.cubeCenter R)).const_mul
      (c := K * nu⁻¹ * N) (mul_nonneg (mul_nonneg hK hi) hN)
  have hW : Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) (localizationW nu l L R v) A := by
    refine hs.of_abs_le ?_
    intro omega
    rw [abs_of_nonneg (localizationW_nonneg nu l L R v omega)]
    refine (localizationDisplayG_W_le hnu hnu1 l L R hRl v omega).trans ?_
    change K*nu⁻¹*(a+_) * N ≤ |K*nu⁻¹*N*(a+_)|
    calc K*nu⁻¹*(a+_) * N = K*nu⁻¹*N*(a+_) := by ring
      _ ≤ |K*nu⁻¹*N*(a+_)| := le_abs_self _
  apply localizationR_isBigO_gammaSigma_half_of_amplitude_le P l L R v hA _ hW
  rw [orliczProductConst_one_one]
  have hsum := localizationDisplayG_square_sum ha hB hg
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 4*(K*T)^2*(nu⁻¹)^2*N^2 by positivity)
  have hbase : 4*(A*A) ≤
      localizationAverageT1FourthAmplitude (8*(K*T*(1+B))^2) nu l L v := by
    unfold localizationAverageT1FourthAmplitude
    rw [Real.rpow_neg hnu.le 2, Real.rpow_two, ← inv_pow]
    change 4*(A*A) ≤ 8*(K*T*(1+B))^2*(nu⁻¹)^2*(a^2+g^2)*N^2
    dsimp only [A]
    nlinarith only [hmul]
  refine hbase.trans (localizationAverageT1FourthAmplitude_mono_const ?_ hnu.le l L v)
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The printed estimate with a dimension-only constant, including the empty increment. -/
theorem localizationDisplayG_R
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (l L : ℕ) (R : Homogenization.TriadicCube d)
    (hRl : R.scale ≤ (l : ℤ)) (v : Homogenization.BlockVec d) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma ((1 : ℝ)/2))
      (localizationR nu l L R v)
      (localizationAverageT1FourthAmplitude (localizationDisplayGConst d) nu l L v) := by
  by_cases hlL : l < L
  · exact localizationDisplayG_R_of_lt P hPrefix hJ2 hJ3 hJ4 hnu hnu1 hlL R hRl v
  · apply (localizationR_isBigO_of_not_lt P hnu hnu1 hlL R v).mono_scale
    apply localizationAverageT1FourthAmplitude_mono_const _ hnu.le l L v
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg _))

/-- The exact `hR` input of the localization-average consumer, with no residual display. -/
theorem localizationDisplayG_R_on_grid
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (l L m n : ℕ) (hnl : n ≤ l) (v : Homogenization.BlockVec d) :
    ∀ R ∈ localizationAverageGrid d m n,
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1 : ℝ)/2))
        (localizationR nu l L R v)
        (localizationAverageT1FourthAmplitude (localizationDisplayGConst d) nu l L v) := by
  intro R hR
  apply localizationDisplayG_R P hPrefix hJ2 hJ3 hJ4 hnu hnu1 l L R _ v
  have hs := Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hR
  change R.scale = (m : ℤ) - ((m-n : ℕ) : ℤ) at hs
  omega

end SuperdiffusionCLT.Section2.Localization
