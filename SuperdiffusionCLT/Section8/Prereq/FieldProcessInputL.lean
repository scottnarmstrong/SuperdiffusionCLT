/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputK
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.Process
public import SuperdiffusionCLT.Section8.Process.Kernel.OnePointExhaustionTail

/-!
# The variable exhaustion-tail input of the marginal field

The amplified pointwise analytic tail is transported to the exhaustion metric and packaged with
the shift-dependent uniform profile.  Above the cubic-log cutoff this is the localized estimate;
below it the normalized potential-mass bound supplies the unit estimate.  The final theorem says
that almost surely the marginal coefficient `fullCoefficientRecentered nu omega` carries a
positive contractive `C₀` resolvent equal to its analytic minimal resolvent, with a conservative
kernel semigroup, and the variable exhaustion-tail input from which the continuous-path process
of `WholeSpaceVariableExhaustionResolventTailInput.wholeSpaceProcess` is built.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

omit [NeZero d] in
private theorem exhaustionAmp_ge {x : Vec d} {r : ℝ} :
    r ≤ fieldInput_exhaustionAmp x r := by
  unfold fieldInput_exhaustionAmp
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

omit [NeZero d] in
private theorem measurable_complBallIndicator (x : Vec d) (r : ℝ) :
    Measurable fun z ↦ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet.compl

omit [NeZero d] in
private theorem complBallIndicator_nonneg (x : Vec d) (r : ℝ) (z : Vec d) :
    0 ≤ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem abs_complBallIndicator_le_one (x : Vec d) (r : ℝ) (z : Vec d) :
    |(Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z| ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
private theorem ofReal_complBallIndicator (x : Vec d) (r : ℝ) :
    (fun z ↦ ENNReal.ofReal
      ((Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z)) =
      (Metric.ball x r)ᶜ.indicator (1 : Vec d → ℝ≥0∞) := by
  funext z
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> norm_num

theorem LogGrowthBounds.liveTail_le_uniform
    (T : LogGrowthBounds Sp)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ)) (x : Vec d) (r : ℝ) (hr : 0 < r) :
    ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) x
          (Metric.ball x (fieldInput_exhaustionAmp x r))ᶜ ≤
      ENNReal.ofReal
        (uniformProfile T (mu : ℝ)
          (Real.sqrt (mu : ℝ) * r)) := by
  by_cases hcut : uniformCutoff T (mu : ℝ) <
      Real.sqrt (mu : ℝ) * r
  · let ar := fieldInput_exhaustionAmp x r
    let f : Vec d → ℝ :=
      fun z ↦ (Metric.ball x ar)ᶜ.indicator (fun _ ↦ (1 : ℝ)) z
    have har : 0 < ar := fieldInput_exhaustionAmp_pos hr
    have hf : Measurable f := measurable_complBallIndicator x ar
    have hf0 : ∀ z, 0 ≤ f z := complBallIndicator_nonneg x ar
    have hf1 : ∀ z, |f z| ≤ 1 := abs_complBallIndicator_le_one x ar
    have hzero : ∀ z ∈ euclideanBall x ar, f z = 0 := by
      intro z hz
      dsimp only [f]
      rw [Set.indicator_of_notMem]
      exact fun hzcompl ↦ hzcompl
        (Homogenization.euclideanBall_subset_metricBall har hz)
    have hsqrt : 0 ≤ Real.sqrt (mu : ℝ) := Real.sqrt_nonneg _
    have hscale : Real.sqrt (mu : ℝ) * r ≤ Real.sqrt (mu : ℝ) * ar :=
      mul_le_mul_of_nonneg_left exhaustionAmp_ge hsqrt
    have hone : 1 < Real.sqrt (mu : ℝ) * ar :=
      lt_of_le_of_lt (one_le_uniformCutoff T (mu : ℝ))
        (hcut.trans_le hscale)
    have htail := mul_toReal_minimalResolvent_le_profile
      T mu hmu hf hf0 hf1 har hone hzero
    have hdom := profile_amp_le_uniform
      T hmu x hr hcut
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
    rw [← hset, ← ofReal_complBallIndicator x ar, hid mu hf hf0 hf1 x]
    rw [← ENNReal.ofReal_toReal hfinite,
      ← ENNReal.ofReal_mul mu.property.le]
    exact ENNReal.ofReal_le_ofReal hreal
  · have hbelow : Real.sqrt (mu : ℝ) * r ≤
        uniformCutoff T (mu : ℝ) := le_of_not_gt hcut
    calc
      ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.resolventPotential (mu : ℝ) x
            (Metric.ball x (fieldInput_exhaustionAmp x r))ᶜ ≤ 1 :=
        R.kernelSemigroup.ofReal_mul_resolventPotential_le_one mu.property x _
      _ ≤ ENNReal.ofReal
          (uniformProfile T (mu : ℝ)
            (Real.sqrt (mu : ℝ) * r)) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
          (one_le_uniformProfile_of_le_cutoff T hbelow)

/-- The uniform profile and reciprocal-norm exhaustion provide the
shift-dependent one-point resolvent-tail input with time exponent `3/2`. -/
def LogGrowthBounds.tailInput
    (T : LogGrowthBounds Sp)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (hcons : R.kernelSemigroup.IsConservative) :
    WholeSpaceVariableExhaustionResolventTailInput R where
  rho := fieldInput_exhaustionRho
  continuous_rho := continuous_fieldInput_exhaustionRho
  rho_pos := fieldInput_exhaustionRho_pos
  lipschitz_rho := lipschitzWith_fieldInput_exhaustionRho
  isCompact_superlevel := fun _epsilon hepsilon ↦
    isCompact_fieldInput_exhaustionRho_superlevel hepsilon
  rho_le_one := fieldInput_exhaustionRho_le_one
  phi := uniformProfile T
  phi_nonneg := uniformProfile_nonneg T
  hasTail := fun mu hmu ↦
    SuperdiffusionCLT.Section8.Process.PositiveC0ContractiveResolvent.hasResolventTail_onePoint_of_amplified R
      hcons fieldInput_exhaustionRho
      continuous_fieldInput_exhaustionRho fieldInput_exhaustionRho_pos
      lipschitzWith_fieldInput_exhaustionRho
      (fun _epsilon hepsilon ↦ isCompact_fieldInput_exhaustionRho_superlevel hepsilon)
      fieldInput_exhaustionAmp
      (fun _x _r _z hdist hlevel ↦
        fieldInput_exhaustionAmp_le_dist hdist hlevel)
      (liveTail_le_uniform T R hid mu hmu)
  cutoff := uniformCutoff T
  cutoff_nonneg := uniformCutoff_nonneg T
  budget := uniformBudget T
  budget_nonneg := uniformBudget_nonneg T
  integral_le := fun mu hmu ↦
    lintegral_uniformProfile_mul_cube_le T hmu
  timeExponent := 3 / 2
  one_lt_timeExponent := by norm_num
  timeExponent_le_two := by norm_num
  cutoffGrowth := uniformGrowth T (3 / 2)
  cutoffGrowth_nonneg := uniformGrowth_nonneg T
    (by norm_num) (by norm_num)
  cutoff_pow_le := fun mu hmu ↦
    uniformCutoff_pow_le T (by norm_num) (by norm_num) hmu

namespace LogGrowthBounds

/-- The variable exhaustion-tail input of the resolvent assembled from the analytic minimal
resolvent. -/
def processInput (T : LogGrowthBounds Sp) :
    WholeSpaceVariableExhaustionResolventTailInput (resolvent T) :=
  tailInput T (resolvent T) (kernelResolventIdentifiesAnalyticMinimal T)
    (isConservative_kernelSemigroup T)

end LogGrowthBounds

/-- **The model-specific input of the construction, for the marginal field.**  Almost surely
there is a positive contractive `C₀` resolvent equal to the analytic minimal resolvent of
`∇·(nu Id + k_omega)∇`, whose kernel semigroup is conservative and which carries the
variable-exhaustion tail input. -/
theorem fieldInput_ae_processInput {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
        A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
          R.kernelSemigroup.IsConservative ∧ A.KernelResolventIdentifiesAnalyticMinimal R ∧
            Nonempty (WholeSpaceVariableExhaustionResolventTailInput R) := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu] with omega hD
  obtain ⟨D⟩ := hD
  exact ⟨D.analyticData, D.logGrowthBounds.resolvent, rfl, rfl,
    D.logGrowthBounds.isConservative_kernelSemigroup,
    D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal, ⟨D.logGrowthBounds.processInput⟩⟩

/-! ## Satisfiability witnesses -/

/-- The process input exists for the law concentrated on the zero shell sequence. -/
example (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ (A : WholeSpaceAnalyticData d) (R : PositiveC0ContractiveResolvent (Vec d)),
        A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
          R.kernelSemigroup.IsConservative ∧ A.KernelResolventIdentifiesAnalyticMinimal R ∧
            Nonempty (WholeSpaceVariableExhaustionResolventTailInput R) :=
  fieldInput_ae_processInput
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

/-- The continuous-path process of the marginal field exists on the one-point compactification,
and started at a live point it almost surely stays live. -/
example {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) (x : Vec d) :
    let H := D.logGrowthBounds.processInput
    let hreg := H.toOnePointRegular
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∀ᵐ path ∂H.wholeSpaceProcess (x : OnePoint (Vec d)),
      ContinuousPath.exitTime (Set.range ((↑) : Vec d → OnePoint (Vec d))) path = ⊤ :=
  D.logGrowthBounds.processInput.wholeSpaceProcess_ae_stays_live
    D.logGrowthBounds.isConservative_kernelSemigroup x

end

end SuperdiffusionCLT.Section8
