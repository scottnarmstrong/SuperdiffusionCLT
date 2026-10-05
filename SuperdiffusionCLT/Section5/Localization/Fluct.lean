/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.Size
public import SuperdiffusionCLT.Probability.OrliczMoments
public import SuperdiffusionCLT.Section5.Localization.SubcubeAvg
public import SuperdiffusionCLT.Section5.Response.DerivativeMoments

/-!
# The fourth moment of the cutoff field on a cube

Step 3 of the proof of `lem.localization` weighs the coefficient by the oscillations of the response
fields through the normalized `L̲²(Q)` norm of the block matrix; the coefficient enters through
`|k_m(x)|²`.  Here `E[⨍_Q |k_m|⁴] ≤ C (m+1)²` on every triadic cube `Q`, by Tonelli and the pointwise
`Γ₂` tail of `k_m(x)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

variable {d : ℕ}

/-- The fourth moment constant of the pointwise value tail of `k_m`. -/
noncomputable def locKConst (d : ℕ) : ℝ :=
  SuperdiffusionCLT.Section2.Cutoff.cutoffValueConst d ^ 4 *
    (1 + Real.Gamma ((4 : ℝ) / 2 + 1))

/-- The fourth moment of `‖k_m(x)‖` at a fixed point. -/
theorem loc_lintegral_kFour_pointwise {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (x : Vec d) :
    ∫⁻ omega, ENNReal.ofReal (Homogenization.Book.Ch02.matrixOperatorNorm
        (streamCutoff omega m x)) ^ (4 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal (locKConst d * (((m : ℝ) + 1)) ^ 2) := by
  have hbo := (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (fun omega => Homogenization.Book.Ch02.matrixOperatorNorm_nonneg (streamCutoff omega m x))).1
    (isBigOWith_gammaSigma_matrixOperatorNorm_streamCutoff hPrefix hJ2 hJ3 hJ4 m x)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hPrefix.dimension
  have hA : 0 < cutoffValueConst d * Real.sqrt ((m : ℝ) + 1) :=
    mul_pos (cutoffValueConst_pos hPrefix) (Real.sqrt_pos.2 (by positivity))
  have hm := (measurable_matrixOperatorNorm_streamCutoff (d := d) m x).aemeasurable (μ := P.toMeasure)
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    (mu := P.toMeasure) hA hm hbo 4
  have hint := SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
    (mu := P.toMeasure) hA hm hbo 4
  have hnn : ∀ omega, 0 ≤ Homogenization.Book.Ch02.matrixOperatorNorm (streamCutoff omega m x) :=
    fun omega => Homogenization.Book.Ch02.matrixOperatorNorm_nonneg _
  have hfun : (fun omega => ENNReal.ofReal (Homogenization.Book.Ch02.matrixOperatorNorm
      (streamCutoff omega m x)) ^ (4 : ℕ)) = fun omega => ENNReal.ofReal
      (|Homogenization.Book.Ch02.matrixOperatorNorm (streamCutoff omega m x)| ^ ((4 : ℕ) : ℝ)) := by
    funext omega
    rw [abs_of_nonneg (hnn omega), Real.rpow_natCast, ENNReal.ofReal_pow (hnn omega)]
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun omega =>
    Real.rpow_nonneg (abs_nonneg _) _)]
  refine ENNReal.ofReal_le_ofReal (hmom.trans (le_of_eq ?_))
  have hs : Real.sqrt ((m : ℝ) + 1) ^ 4 = ((m : ℝ) + 1) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
  rw [locKConst, Real.rpow_natCast, mul_pow, hs]
  push_cast
  ring

/-- The normalized fourth moment `⨍_Q ‖k_m‖⁴` of the cutoff field on a cube. -/
noncomputable def locKFour (m : ℕ) (Q : TriadicCube d) (omega : ShellSeq d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Homogenization.Book.Ch02.matrixOperatorNorm (streamCutoff omega m x)) ^
    (4 : ℕ) ∂normalizedCubeMeasure Q

theorem loc_measurable_uncurry_kFour (m : ℕ) :
    Measurable (Function.uncurry fun (omega : ShellSeq d) (x : Vec d) =>
      ENNReal.ofReal (Homogenization.Book.Ch02.matrixOperatorNorm (streamCutoff omega m x)) ^
        (4 : ℕ)) := by
  have h := (measurable_uncurry_matrixOperatorNorm_streamCutoff (d := d) m).comp measurable_swap
  exact (ENNReal.measurable_ofReal.comp h).pow_const 4

theorem loc_measurable_kFour (m : ℕ) (Q : TriadicCube d) : Measurable (locKFour m Q) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  exact (loc_measurable_uncurry_kFour (d := d) m).lintegral_prod_right'

/-- **`E[⨍_Q ‖k_m‖⁴] ≤ C (m+1)²`** on every triadic cube. -/
theorem loc_lintegral_kFour_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (m : ℕ) (Q : TriadicCube d) :
    ∫⁻ omega, locKFour m Q omega ∂P.toMeasure ≤
      ENNReal.ofReal (locKConst d * (((m : ℝ) + 1)) ^ 2) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  unfold locKFour
  rw [lintegral_lintegral_swap (loc_measurable_uncurry_kFour (d := d) m).aemeasurable]
  calc _ ≤ ∫⁻ _x, ENNReal.ofReal (locKConst d * (((m : ℝ) + 1)) ^ 2) ∂normalizedCubeMeasure Q :=
        lintegral_mono fun x => loc_lintegral_kFour_pointwise hPrefix hJ2 hJ3 hJ4 m x
    _ = _ := by simp

end SuperdiffusionCLT.Section5
