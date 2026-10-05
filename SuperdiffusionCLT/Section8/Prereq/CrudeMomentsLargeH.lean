/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeG
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.DiracJ1Restriction

/-!
# The second moment, and witnesses

For a probability measure the second displacement moment is at most the square root of the fourth
(Cauchy-Schwarz).  Together with the fourth moment bound for times at least one this gives
`∫ ‖y‖ ^ 2 d(S t 0) ≤ sqrt M t (log (K ^ 2 + t)) ^ (4 n)`.  The statements are checked on the zero
field, for which the process is the heat flow, and on the law concentrated on the zero shell
sequence.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open SuperdiffusionCLT.Section8.Common.Regularity.Freezing
open scoped ENNReal NNReal Matrix.Norms.Elementwise

noncomputable section

/-- **Cauchy-Schwarz for the displacement moments of a probability measure.** -/
theorem crudeMomL_lintegral_edist_sq_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] {nu : Measure X} [IsProbabilityMeasure nu] (x : X) {M : ℝ}
    (h : ∫⁻ z, edist z x ^ (4 : ℝ) ∂nu ≤ ENNReal.ofReal M) :
    ∫⁻ z, edist z x ^ (2 : ℝ) ∂nu ≤ ENNReal.ofReal (Real.sqrt M) := by
  have hmeas : Measurable fun z : X ↦ edist z x ^ (2 : ℝ) :=
    (measurable_id.edist measurable_const).pow_const _
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq nu Real.HolderConjugate.two_two
    hmeas.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at hcs
  have h4 : ∫⁻ z, (edist z x ^ (2 : ℝ)) ^ (2 : ℝ) ∂nu = ∫⁻ z, edist z x ^ (4 : ℝ) ∂nu := by
    refine lintegral_congr fun z ↦ ?_
    rw [← ENNReal.rpow_mul]; norm_num
  rw [h4] at hcs
  rcases le_or_gt 0 M with hM | hM
  · refine hcs.trans ?_
    calc (∫⁻ z, edist z x ^ (4 : ℝ) ∂nu) ^ (1 / (2 : ℝ)) ≤ (ENNReal.ofReal M) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow h (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt M) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hM (by norm_num), Real.sqrt_eq_rpow]
  · have h0 : ∫⁻ z, edist z x ^ (4 : ℝ) ∂nu = 0 :=
      le_antisymm (h.trans (by rw [ENNReal.ofReal_of_nonpos hM.le])) zero_le
    rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)] at hcs
    exact hcs.trans zero_le

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d}

/-- **The second moment at the origin of the marginal-field process, for times at least one.** -/
theorem fieldMoment_second_large (D : FieldInputData d nu k) {c0 Kc : ℝ} {n : ℕ} (hc0 : 0 ≤ c0)
    (hKc : 2 ≤ Kc) (hn : 2 ≤ n)
    (hk : ∀ y, matrixOperatorNorm (k y) ≤ c0 * Real.log (Kc ^ 2 + vecNormSq y) ^ n)
    {t : ℝ≥0} (ht : 1 ≤ t) :
    ∫⁻ z, edist z (0 : Vec d) ^ (2 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
      ENNReal.ofReal (Real.sqrt (crudeMomL_const d nu c0
        (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) n) *
        Real.log (Kc ^ 2 + (t : ℝ)) ^ (4 * n) * (t : ℝ)) := by
  have : IsProbabilityMeasure (D.logGrowthBounds.resolvent.kernelSemigroup t 0) :=
    ⟨D.logGrowthBounds.isConservative_kernelSemigroup t 0⟩
  have h4 := fieldMoment_fourth_large D hc0 hKc hn hk ht
  refine (crudeMomL_lintegral_edist_sq_le 0 h4).trans (le_of_eq ?_)
  congr 1
  have hL : 0 ≤ Real.log (Kc ^ 2 + (t : ℝ)) :=
    zero_le_one.trans (crudeMomL_one_le_log hKc (NNReal.coe_nonneg t))
  have hM := crudeMomL_const_nonneg (d := d) nu c0
    (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) n
  have hs : Real.sqrt (Real.log (Kc ^ 2 + (t : ℝ)) ^ (8 * n)) =
      Real.log (Kc ^ 2 + (t : ℝ)) ^ (4 * n) := by
    rw [show Real.log (Kc ^ 2 + (t : ℝ)) ^ (8 * n) =
      (Real.log (Kc ^ 2 + (t : ℝ)) ^ (4 * n)) ^ 2 by rw [← pow_mul]; ring_nf]
    exact Real.sqrt_sq (by positivity)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hM, hs, Real.sqrt_sq (NNReal.coe_nonneg t)]

/-! ## Satisfiability witnesses -/

/-- The zero field: the process is the heat flow, and both moment bounds hold for it. -/
example (hd : 2 ≤ d) :
    ∃ D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d)), ∀ t : ℝ≥0, 1 ≤ t →
      ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
        ENNReal.ofReal (crudeMomL_const d 1 0
          (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) 2 *
          Real.log ((2 : ℝ) ^ 2 + (t : ℝ)) ^ (8 * 2) * (t : ℝ) ^ 2) ∧
      ∫⁻ z, edist z (0 : Vec d) ^ (2 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
        ENNReal.ofReal (Real.sqrt (crudeMomL_const d 1 0
          (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) 2) *
          Real.log ((2 : ℝ) ^ 2 + (t : ℝ)) ^ (4 * 2) * (t : ℝ)) := by
  let D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d)) :=
    { two_le := hd
      nu_pos := one_pos
      skew := fun _ => by simp [matTranspose]
      contDiff := contDiff_const
      gradConst := 0
      gradConst_nonneg := le_rfl
      grad_le := fun y => by simp }
  have hk : ∀ y : Vec d, matrixOperatorNorm ((fun _ : Vec d => (0 : Mat d)) y) ≤
      (0 : ℝ) * Real.log ((2 : ℝ) ^ 2 + vecNormSq y) ^ 2 := fun y => by
    simp [matrixOperatorNorm]
  exact ⟨D, fun t ht => ⟨fieldMoment_fourth_large D le_rfl le_rfl le_rfl hk ht,
    fieldMoment_second_large D le_rfl le_rfl le_rfl hk ht⟩⟩

/-- The almost-sure statements hold for the law concentrated on the zero shell sequence. -/
example (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∃ C : ℝ, ∀ σ : ℝ, 0 < σ → ∃ Kfun : ShellSeq d → ℝ, Measurable Kfun ∧
      (∀ omega, (27 : ℝ) ≤ Kfun omega) ∧
      (∃ B : ℝ, IndependentSums.IsBigO
        (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure
        (IndependentSums.gammaSigma (2 * σ)) (fun omega => Real.log (Kfun omega)) B) ∧
      ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
        ∃ D : FieldInputData d nu (fullStreamRecentered omega),
          ∀ t : ℝ≥0, 1 ≤ t →
            ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
              ENNReal.ofReal (crudeMomL_const d nu (Real.sqrt (max C 0))
                (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) ⌈1 + σ⌉₊ *
                Real.log (Kfun omega ^ 2 + (t : ℝ)) ^ (8 * ⌈1 + σ⌉₊) * (t : ℝ) ^ 2) :=
  fieldMoment_ae_fourth_large
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ1Restriction_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw hnu

end

end SuperdiffusionCLT.Section8
