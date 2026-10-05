/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpM
public import SuperdiffusionCLT.Section8.Root.AnnealedDtD
public import SuperdiffusionCLT.Section8.Prereq.GradientScaleB
public import SuperdiffusionCLT.Section8.Root.TheoremAAssemblyB

/-!
# The quenched second moment: the random inputs

The tail of the growth scale at the scale `√t`, a process input whose gradient constant is the
measurable gradient scale, and a semigroup-valued function of the sample.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory MarkovProcess
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped ENNReal NNReal Matrix.Norms.Elementwise

variable {d : ℕ}

/-- **The tail of the growth scale at the scale `√t`.** -/
theorem dtExp_measure_K {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Kf : Ω → ℝ} (hK27 : ∀ ω, (27 : ℝ) ≤ Kf ω) {B : ℝ}
    (hB : IndependentSums.IsBigO μ (IndependentSums.gammaSigma (2 * 1))
      (fun ω => Real.log (Kf ω)) B) {t : ℝ} (ht : 10 ≤ t) (hBt : 2 * max B 1 ≤ Real.log t) :
    μ {ω | Real.sqrt t < Kf ω} ≤
      ENNReal.ofReal (Real.exp (-((Real.log t / (2 * max B 1)) ^ 2))) := by
  have hB'0 : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB' := hB.mono_scale (le_max_left B 1)
  set s' : ℝ := Real.log t / (2 * max B 1) with hs'
  have hs'1 : 1 ≤ s' := by rw [hs', le_div_iff₀ (by positivity)]; linarith only [hBt]
  have h1 := (IndependentSums.isBigO_gammaSigma_iff.1 hB') hs'1
  have ht0 : 0 < t := by linarith only [ht]
  have hsub : {ω | Real.sqrt t < Kf ω} ⊆
      IndependentSums.absTailEvent (fun ω => Real.log (Kf ω)) (max B 1 * s') := by
    intro ω hω
    have hK0 : 0 < Kf ω := by linarith only [hK27 ω]
    have hlog : Real.log (Real.sqrt t) < Real.log (Kf ω) :=
      Real.log_lt_log (Real.sqrt_pos.2 ht0) hω
    rw [Real.log_sqrt ht0.le] at hlog
    have hKl : 0 ≤ Real.log (Kf ω) := Real.log_nonneg (by linarith only [hK27 ω])
    simp only [IndependentSums.absTailEvent, IndependentSums.upperTailEvent, Set.mem_ofPred_eq,
      abs_of_nonneg hKl]
    have : max B 1 * s' = Real.log t / 2 := by rw [hs']; field_simp
    rw [this]; exact hlog
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal (h1.trans (le_of_eq ?_))
  congr 2
  rw [show (2 : ℝ) * 1 = 2 by norm_num, Real.rpow_two]

variable [NeZero d]

/-- **A process input with the gradient scale as its constant.** -/
theorem dtExp_dataG {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ ω : ShellSeq d ∂P.toMeasure, ∃ D : FieldInputData d nu (fullStreamRecentered ω),
      D.gradConst = gradScale_G ω := by
  filter_upwards [ae_contDiff_fullStreamRecentered hJ3, ae_fderiv_fullStreamRecentered hJ3,
    gradScale_ae_log_growth hPrefix hJ3] with ω h2 h3 hG
  exact ⟨{ two_le := hPrefix.dimension
           nu_pos := hnu
           skew := fieldInput_matTranspose_recentered ω
           contDiff := h2
           gradConst := gradScale_G ω
           gradConst_nonneg := annDt_G_nonneg hPrefix ω
           grad_le := fun y => by rw [h3]; exact hG y }, rfl⟩

/-- **A semigroup-valued function of the sample.**  There is a function of the sample, equal
almost surely to the kernel semigroup of every process input of the sample, which almost surely
satisfies the specification. -/
theorem dtExp_choice {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∃ S : ShellSeq d → SubMarkovKernelSemigroup (Vec d),
      (∀ᵐ ω : ShellSeq d ∂P.toMeasure,
        IsDivergenceFormFeller (fullCoefficientRecentered nu ω) (S ω)) ∧
      ∀ᵐ ω : ShellSeq d ∂P.toMeasure, ∀ D : FieldInputData d nu (fullStreamRecentered ω),
        S ω = D.logGrowthBounds.resolvent.kernelSemigroup := by
  classical
  have hne := fieldInput_ae_data hPrefix hJ3 hnu
  obtain ⟨ω0, hω0⟩ := hne.exists
  refine ⟨fun ω => if h : Nonempty (FieldInputData d nu (fullStreamRecentered ω)) then
      (Classical.choice h).logGrowthBounds.resolvent.kernelSemigroup
    else (Classical.choice hω0).logGrowthBounds.resolvent.kernelSemigroup, ?_, ?_⟩
  · filter_upwards [hne, thmA_link_data (nu := nu) hJ3] with ω h hl
    simp only [h, ↓reduceDIte]
    exact (hl _).1
  · filter_upwards [hne, thmA_link_data (nu := nu) hJ3] with ω h hl D
    simp only [h, ↓reduceDIte]
    exact ((hl (Classical.choice h)).2.2 _ (hl D).1).symm

/-! ## Satisfiability witnesses -/

/-- The hypotheses of the uniform growth clause hold for the law concentrated on the zero shell
sequence. -/
example (hd : 2 ≤ d) : ∃ Kfun : ShellSeq d → ℝ, Measurable Kfun ∧
    (∀ ω, (27 : ℝ) ≤ Kfun ω) := by
  obtain ⟨_, _, H⟩ := dtExp_growth (d := d)
  obtain ⟨K, hK, hK27, -⟩ := H (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d)
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ1Restriction_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ2_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ4_diracZeroLaw
  exact ⟨K, hK, hK27⟩

/-- The process input with the gradient scale as constant, and the semigroup-valued function of
the sample, exist for the law concentrated on the zero shell sequence. -/
example (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    (∀ᵐ ω : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ D : FieldInputData d nu (fullStreamRecentered ω), D.gradConst = gradScale_G ω) ∧
    ∃ S : ShellSeq d → SubMarkovKernelSemigroup (Vec d),
      ∀ᵐ ω : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
        IsDivergenceFormFeller (fullCoefficientRecentered nu ω) (S ω) :=
  ⟨dtExp_dataG (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
      SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu,
    (dtExp_choice (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
      SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu).imp
      fun _ h => h.1⟩

end SuperdiffusionCLT.Section8
