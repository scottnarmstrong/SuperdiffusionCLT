/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayF
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayA
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB

/-!
# The per-cube localization error from the shell laws

The Gaussian gradient estimate `e.nabla.kmn.Linfty` (Section 2),
stationarity, and the centered oscillation bound give the
`Gamma_2` estimate for `localizationPerturbSize`. The small cube contributes
its side length `3^n`, and the translated derivative gauge contributes
`3^(-l)`. Their product is the printed decay `3^(-(l-n))`.

DisplayF's scalar polynomial rule then gives `hDd` at
`Γ₁`, with a constant depending only on dimension. The result uses only
the prefix and J3 laws. No intermediate tail bound is assumed. The final
`localizationDisplayK_hDd_grid` supplies the per-cube tail input `hDd` of the
localization average; the empty shell interval is included.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open scoped BigOperators Matrix.Norms.Elementwise

variable {d : ℕ}

/-- On a translated small cube the derivative is bounded by the translated
larger-cube derivative observable. -/
theorem localizationDisplayK_derivative_le {n l : ℕ} (hnl : n ≤ l)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (j : SuperdiffusionCLT.Frozen.Assumptions.ShellField d) :
    SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm (Homogenization.cubeSet R) j ≤
      SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellCubeDerivNorm l
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translate (Homogenization.cubeCenter R) j) := by
  apply SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm_le
    (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellCubeDerivNorm_nonneg l _)
  intro x hx
  exact (SuperdiffusionCLT.Section2.Estimates.Stream.matrixDerivativeNorm_deriv_le_shellCubeDerivNorm_translate_cubeSet
    n j (Homogenization.cubeCenter R)
    (SuperdiffusionCLT.Section2.Estimates.Stream.sub_cubeCenter_mem_cubeSet_originCube hR hx)).trans
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellCubeDerivNorm_mono hnl _)

/-- The centered increment is bounded by the translated derivative gauge,
with the side length of the small cube retained explicitly. -/
theorem localizationDisplayK_perturbSize_le {n l : ℕ} (hnl : n ≤ l) (L : ℕ)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    localizationPerturbSize l L R omega ≤
      (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge l L
          (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
            (Homogenization.cubeCenter R) omega)) := by
  let U := Homogenization.cubeSet R
  let omega' := SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
    (Homogenization.cubeCenter R) omega
  let g := SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge l L omega'
  have hg : 0 ≤ g := SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge_nonneg l L omega'
  have hUb := Homogenization.isBounded_cubeSet R
  have hUpos : MeasureTheory.volume U ≠ 0 := by
    intro hz
    have hv := Homogenization.volume_cubeSet_toReal R
    rw [hz, ENNReal.toReal_zero] at hv
    exact (Homogenization.cubeVolume_pos R).ne' hv.symm
  have hdist : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ (3 : ℝ) ^ n := by
    intro x hx y hy
    have hd := SuperdiffusionCLT.Section2.Estimates.Stream.dist_le_of_mem_cubeSet R hx hy
    simpa only [dist_eq_norm, hR, zpow_natCast] using hd
  have hpair : ∀ x ∈ U, ∀ y ∈ U,
      ‖SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x -
        SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L y‖ ≤
        Real.sqrt d * (3 : ℝ) ^ n * g := by
    intro x hx y hy
    rw [SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply,
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc
      ∑ k ∈ Finset.Ioc l L,
          ‖SuperdiffusionCLT.Section2.Cutoff.shellReg omega k x -
            SuperdiffusionCLT.Section2.Cutoff.shellReg omega k y‖ ≤
        ∑ k ∈ Finset.Ioc l L, Real.sqrt d * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellCubeDerivNorm l (omega' k) := by
        apply Finset.sum_le_sum
        intro k _
        have hs := SuperdiffusionCLT.Section2.Carriers.norm_shell_sub_le hUb
          (SuperdiffusionCLT.Section2.Estimates.Stream.convex_cubeSet R) (omega k) hy hx
        have hk := localizationDisplayK_derivative_le hnl R hR (omega k)
        calc
          _ ≤ Real.sqrt d *
              SuperdiffusionCLT.Section2.Carriers.shellDerivLinftyNorm U (omega k) * ‖x - y‖ := hs
          _ ≤ Real.sqrt d *
              SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellCubeDerivNorm l (omega' k) *
                (3 : ℝ) ^ n :=
            mul_le_mul (mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg _))
              (hdist x hx y hy) (norm_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg _)
                (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellCubeDerivNorm_nonneg l _))
          _ = _ := by ring
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hbound : ∀ x ∈ U, Homogenization.Book.Ch02.matrixOperatorNorm
      (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x -
        localizationGaugeAverage l L R omega) ≤ (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n * g) := by
    intro x hx
    have hn := SuperdiffusionCLT.Section2.Carriers.norm_sub_volumeAverageMat_le hUb hUpos
      (fun i j => SuperdiffusionCLT.Section2.Cutoff.integrableOn_entry_of_isBounded
        (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L) hUb i j)
      (hpair x hx)
    apply SuperdiffusionCLT.Section2.Estimates.Stream.matrixOperatorNorm_le_of_entry_bound _
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) hg)
    intro i j
    have he := Matrix.norm_entry_le_entrywise_sup_norm
      (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x -
        localizationGaugeAverage l L R omega) (i := i) (j := j)
    exact (show |(_ : Homogenization.Mat d) i j| ≤ ‖(_ : Homogenization.Mat d)‖ by
      exact he).trans hn
  apply csSup_le (Set.range_nonempty (localizationPerturbSizeAtIndex l L R omega))
  rintro _ ⟨o, rfl⟩
  cases o with
  | none => exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) hg)
  | some x => exact hbound x.1 x.2

/-- The spatial scale factor is the ratio of the two cube side lengths. -/
theorem localizationDisplayK_scale_eq {n l : ℕ} (hnl : n ≤ l) :
    (3 : ℝ) ^ n * ((3 : ℝ) ^ l)⁻¹ = (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast,
    pow_sub₀ (3 : ℝ) (by norm_num : (3 : ℝ) ≠ 0) hnl, mul_inv_rev, inv_inv]

/-- The dimension-only Gaussian amplitude for the centered perturbation. -/
noncomputable def localizationDisplayKConst (d : ℕ) : ℝ :=
  (d : ℝ) * Real.sqrt d * Homogenization.IndependentSums.gammaTriangleConst 2

/-- The amplitude is positive in positive dimension. -/
theorem localizationDisplayKConst_pos [NeZero d] : 0 < localizationDisplayKConst d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast (NeZero.pos d)
  exact mul_pos (mul_pos hd (Real.sqrt_pos.mpr hd))
    Homogenization.IndependentSums.gammaTriangleConst_pos

/-- The centered perturbation has the Gaussian spatial-decay estimate from
stationarity and the shell regularity law. -/
theorem localizationDisplayK_perturbSize_gamma_two
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    {n l L : ℕ} (hnl : n ≤ l) (hlL : l < L)
    (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ)) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 2) (localizationPerturbSize l L R)
      (localizationDisplayKConst d * (3 : ℝ) ^ (-((l - n : ℕ) : ℝ))) := by
  have ht := SuperdiffusionCLT.Section2.Estimates.Stream.isBigOWith_gammaSigma_finiteShellDerivGauge_translate
    hPrefix hJ3 hlL (Homogenization.cubeCenter R)
  have hc : 0 ≤ (d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n) := by positivity
  have hs := ht.const_mul hc
  have hdom : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      localizationPerturbSize l L R omega ≤
      ((d : ℝ) * (Real.sqrt d * (3 : ℝ) ^ n)) *
        SuperdiffusionCLT.Section2.Estimates.Stream.finiteShellDerivGauge l L
          (SuperdiffusionCLT.Frozen.Assumptions.ShellField.translateSequence
            (Homogenization.cubeCenter R) omega) := by
    intro omega
    simpa only [mul_assoc] using localizationDisplayK_perturbSize_le hnl L R hR omega
  have htail := (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (localizationPerturbSize_nonneg l L R)).mp (hs.of_le hdom)
  convert htail using 1
  unfold localizationDisplayKConst
  rw [← localizationDisplayK_scale_eq hnl]
  ring

/-- The printed `hDd` estimate follows from the shell laws with no analytic
residual. The empty shell interval is included. -/
theorem localizationDisplayK_hDd [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {n l : ℕ} (hnl : n ≤ l)
    (L : ℕ) (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ)) :
    Homogenization.IndependentSums.IsBigO P.toMeasure
      (Homogenization.IndependentSums.gammaSigma 1) (localizationDz nu l L R)
      (localizationAverageT1CubeAmplitude
        (localizationDisplayKConst d + localizationDisplayKConst d ^ 2) nu l n) := by
  have hC := localizationDisplayKConst_pos (d := d)
  by_cases hlL : l < L
  · have hq : 0 ≤ (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hq1 : (3 : ℝ) ^ (-((l - n : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg _))
    have ht := localizationDisplayF_scaled_quadratic_gaussian_tail hnu hnu1 hC.le hq hq1
      (localizationDisplayK_perturbSize_gamma_two hPrefix hJ3 hnl hlL R hR)
    have heq : (fun omega => nu⁻¹ * |localizationPerturbSize l L R omega| +
        nu⁻¹ ^ 2 * localizationPerturbSize l L R omega ^ 2) = localizationDz nu l L R := by
      funext omega
      rw [abs_of_nonneg (localizationPerturbSize_nonneg l L R omega)]
      rfl
    rw [heq] at ht
    simpa only [localizationAverageT1CubeAmplitude, Real.rpow_neg hnu.le,
      Real.rpow_two, inv_pow] using ht
  · exact localizationDz_isBigO_of_not_lt (add_pos_of_pos_of_nonneg hC (sq_nonneg _))
      hnu l L n R P hlL

/-- The exact grid-quantified `hDd` input for the localization-average assembly. -/
theorem localizationDisplayK_hDd_grid [NeZero d]
    {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {n l m : ℕ}
    (hnl : n ≤ l) (hnm : n ≤ m) (L : ℕ) :
    ∀ R ∈ localizationAverageGrid d m n,
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma 1) (localizationDz nu l L R)
        (localizationAverageT1CubeAmplitude
          (localizationDisplayKConst d + localizationDisplayKConst d ^ 2) nu l n) := by
  intro R hR
  exact localizationDisplayK_hDd hPrefix hJ3 hnu hnu1 hnl L R
    (SuperdiffusionCLT.Section2.Estimates.Stream.scale_of_mem_largeCubeSubcubes hnm hR)

end SuperdiffusionCLT.Section2.Localization
