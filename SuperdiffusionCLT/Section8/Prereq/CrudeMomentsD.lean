/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputL
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsB
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsC

/-!
# The fourth moment at the origin for times at most one

The shift-uniform profile of the marginal field is a tail of the resolvent in the sup-metric ball
about every centre, with radius amplified by the exhaustion scale of the centre.  At the origin the
amplified radius is the radius itself, and at a point `y` with `|y| ≥ 10 r` the amplified radius is
at most `|y| - 2 r`, so the ball of radius `2 r` about the origin lies outside the ball about `y`
carrying the tail.  The far smallness hypothesis of the displacement tail follows once the
profile is at most one half, and the layer cake then gives the fourth moment at the origin, at the
time `t = 1 / mu ≤ 1`, with the logarithmic factor of the cutting radius.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set Filter
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

omit [NeZero d] in
private theorem crudeMom_amp_ge {x : Vec d} {r : ℝ} : r ≤ fieldInput_exhaustionAmp x r := by
  unfold fieldInput_exhaustionAmp
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [NeZero d] in
private theorem crudeMom_measurable_indicator (x : Vec d) (r : ℝ) :
    Measurable fun z ↦ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet.compl

omit [NeZero d] in
private theorem crudeMom_indicator_nonneg (x : Vec d) (r : ℝ) (z : Vec d) :
    0 ≤ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem crudeMom_abs_indicator_le (x : Vec d) (r : ℝ) (z : Vec d) :
    |(Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z| ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem crudeMom_ofReal_indicator (x : Vec d) (r : ℝ) :
    (fun z ↦ ENNReal.ofReal
      ((Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z)) =
      (Metric.ball x r)ᶜ.indicator (1 : Vec d → ℝ≥0∞) := by
  funext z
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> norm_num

/-- **The resolvent tail in the sup-metric ball at every centre.**  The normalized `mu`-potential
of the complement of the ball of radius `amp x r` about `x` is at most the shift-uniform profile
at `sqrt mu * r`, for every centre, radius and shift at least one. -/
theorem LogGrowthBounds.crudeMom_liveTail
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ)) (x : Vec d) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) x
          (Metric.ball x (fieldInput_exhaustionAmp x r))ᶜ ≤
      ENNReal.ofReal (LogGrowthBounds.uniformProfile T (mu : ℝ) (Real.sqrt (mu : ℝ) * r)) := by
  by_cases hcut : LogGrowthBounds.uniformCutoff T (mu : ℝ) < Real.sqrt (mu : ℝ) * r
  · let ar := fieldInput_exhaustionAmp x r
    let f : Vec d → ℝ := fun z ↦ (Metric.ball x ar)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z
    have har : 0 < ar := fieldInput_exhaustionAmp_pos hr
    have hf : Measurable f := crudeMom_measurable_indicator x ar
    have hf0 : ∀ z, 0 ≤ f z := crudeMom_indicator_nonneg x ar
    have hf1 : ∀ z, |f z| ≤ 1 := crudeMom_abs_indicator_le x ar
    have hzero : ∀ z ∈ euclideanBall x ar, f z = 0 := by
      intro z hz
      dsimp only [f]
      rw [Set.indicator_of_notMem]
      exact fun hzcompl ↦ hzcompl
        (Homogenization.euclideanBall_subset_metricBall har hz)
    have hsqrt : 0 ≤ Real.sqrt (mu : ℝ) := Real.sqrt_nonneg _
    have hscale : Real.sqrt (mu : ℝ) * r ≤ Real.sqrt (mu : ℝ) * ar :=
      mul_le_mul_of_nonneg_left crudeMom_amp_ge hsqrt
    have hone : 1 < Real.sqrt (mu : ℝ) * ar :=
      lt_of_le_of_lt (LogGrowthBounds.one_le_uniformCutoff T (mu : ℝ)) (hcut.trans_le hscale)
    have htail := LogGrowthBounds.mul_toReal_minimalResolvent_le_profile
      T mu hmu hf hf0 hf1 har hone hzero
    have hdom := LogGrowthBounds.profile_amp_le_uniform T hmu x hr hcut
    have hreal := htail.trans hdom
    have hfinite := A.analyticMinimalResolvent_ne_top
      mu hf hf0 (by norm_num : (0 : ℝ) ≤ 1) hf1 x
    have hset : R.kernelSemigroup.kernelResolvent (mu : ℝ)
        ((Metric.ball x ar)ᶜ.indicator 1) x =
        R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x ar)ᶜ := by
      rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ)
        (measurable_one.indicator Metric.isOpen_ball.measurableSet.compl) x,
        lintegral_indicator_one Metric.isOpen_ball.measurableSet.compl]
    change ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x ar)ᶜ ≤ _
    rw [← hset, ← crudeMom_ofReal_indicator x ar, hid mu hf hf0 hf1 x]
    rw [← ENNReal.ofReal_toReal hfinite, ← ENNReal.ofReal_mul mu.property.le]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hbelow : Real.sqrt (mu : ℝ) * r ≤ LogGrowthBounds.uniformCutoff T (mu : ℝ) :=
      le_of_not_gt hcut
    calc
      ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.resolventPotential (mu : ℝ) x
            (Metric.ball x (fieldInput_exhaustionAmp x r))ᶜ ≤ 1 :=
        R.kernelSemigroup.ofReal_mul_resolventPotential_le_one mu.property x _
      _ ≤ ENNReal.ofReal
          (LogGrowthBounds.uniformProfile T (mu : ℝ) (Real.sqrt (mu : ℝ) * r)) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
          (LogGrowthBounds.one_le_uniformProfile_of_le_cutoff T hbelow)

omit [NeZero d] in
/-- At the origin the amplified radius is the radius. -/
theorem crudeMom_amp_zero (r : ℝ) :
    fieldInput_exhaustionAmp (0 : Vec d) r = r := by
  unfold fieldInput_exhaustionAmp
  split_ifs with h
  · refine max_eq_left ?_
    have h4 : (4 : ℝ) ≤ r := by
      simpa only [fieldInput_exhaustionRho, norm_zero, add_zero, inv_one, mul_one] using h
    simp only [norm_zero, add_zero, mul_one]
    linarith only [h4]
  · rfl

omit [NeZero d] in
/-- **Far geometry at the origin.**  At a point of sup norm at least `10 r` the amplified radius
is at most the sup norm minus `2 r`. -/
theorem crudeMom_amp_le_of_far {y : Vec d} {r : ℝ} (hr : 0 < r) (hy : 10 * r ≤ ‖y‖) :
    fieldInput_exhaustionAmp y r ≤ ‖y‖ - 2 * r := by
  unfold fieldInput_exhaustionAmp
  split_ifs with h
  · refine max_le (by linarith only [hy, hr]) ?_
    have hn : 0 ≤ ‖y‖ := norm_nonneg y
    have hden : 0 < 1 + ‖y‖ := by linarith only [hn]
    have h4 : 4 ≤ r * (1 + ‖y‖) := by
      unfold fieldInput_exhaustionRho at h
      rw [← div_eq_mul_inv, div_le_iff₀ hden] at h
      linarith only [h]
    by_cases hr2 : (1 / 2 : ℝ) ≤ r
    · linarith only [hy, hr2]
    · replace hr2 := not_le.mp hr2
      have hprod : ‖y‖ * r ≤ ‖y‖ * (1 / 2) := mul_le_mul_of_nonneg_left hr2.le hn
      have hn7 : 7 ≤ ‖y‖ := by linarith only [h4, hprod, hr2]
      linarith only [hn7, hr2]
  · linarith only [hy, hr]

omit [NeZero d] in
/-- **Far geometry at a general centre.**  With the working radius `a = max r (2/3 (1 + |x|))`,
a point at distance at least `10 a` from `x` has amplified radius at most that distance minus
`2 a`. -/
theorem crudeMom_amp_le_of_far_at {x y : Vec d} {r : ℝ} (hr : 0 < r)
    (hy : 10 * max r (2 / 3 * (1 + ‖x‖)) ≤ ‖y - x‖) :
    fieldInput_exhaustionAmp y r ≤ ‖y - x‖ - 2 * max r (2 / 3 * (1 + ‖x‖)) := by
  have hra : r ≤ max r (2 / 3 * (1 + ‖x‖)) := le_max_left _ _
  have hqa : 2 / 3 * (1 + ‖x‖) ≤ max r (2 / 3 * (1 + ‖x‖)) := le_max_right _ _
  have hn : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
  unfold fieldInput_exhaustionAmp
  split_ifs with h
  · exact max_le (by linarith only [hy, hr, hra]) (by linarith only [hy, hqa, hn, hr, hra])
  · linarith only [hy, hr, hra]

end

end SuperdiffusionCLT.Section8
