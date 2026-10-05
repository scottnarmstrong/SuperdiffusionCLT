/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.FieldBridge
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section7.Analytic.CZ.Local
public import SuperdiffusionCLT.Section7.Analytic.Change.SkewShift
public import SuperdiffusionCLT.Section6.Prereq.FullField
public import SuperdiffusionCLT.Section6.Prereq.FullFieldB
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# The frame of the centre `y`

Almost surely, for every centre `y`, the recentered field of the translated sample is the
recentered field of the sample seen from `x + y`, up to a constant skew matrix; weak solutions
on a set `D` correspond to weak solutions on `translateSet (-y) D` of the translated field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-- **F0a — the recentered field of the translated sample.** -/
theorem lip_frame_field (d : ℕ) [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P) (nu : ℝ) :
    ∀ᵐ omega ∂P.toMeasure, ∀ y : Vec d, ∃ S : Mat d, matTranspose S = -S ∧
      ∀ x : Vec d,
        Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega) x =
          Section6.fullCoefficientRecentered nu omega (x + y) + S := by
  filter_upwards [Section6.ae_summable_shellRecentered hJ3] with omega hω y
  refine ⟨-Section6.fullStreamRecentered omega y, ?_, fun x => ?_⟩
  · ext i k
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply]
    rw [Section6.fullStreamRecentered_skew_entry omega y i k]
    ring
  · have hterm : ∀ n, Section6.shellRecentered (ShellField.translateSequence y omega) n x =
        Section6.shellRecentered omega n (x + y) - Section6.shellRecentered omega n y := by
      intro n
      simp only [Section6.shellRecentered, shellReg, ShellField.translateSequence_apply,
        ShellField.forgetShell_apply, ShellField.translate_apply, zero_add]
      abel
    have hs : Section6.fullStreamRecentered (ShellField.translateSequence y omega) x =
        Section6.fullStreamRecentered omega (x + y) - Section6.fullStreamRecentered omega y := by
      rw [Section6.fullStreamRecentered_eq, Section6.fullStreamRecentered_eq,
        Section6.fullStreamRecentered_eq]
      rw [← (hω (x + y)).tsum_sub (hω y)]
      exact tsum_congr hterm
    simp only [Section6.fullCoefficientRecentered, hs]
    abel

private theorem lip_frame_isBounded_translateSet {D : Set (Vec d)} (hD : Bornology.IsBounded D)
    (z : Vec d) : Bornology.IsBounded (translateSet z D) := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hD
  refine Metric.isBounded_iff.mpr ⟨R, fun x hx y hy => ?_⟩
  rw [mem_translateSet_iff_sub_mem] at hx hy
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hR hx hy

private theorem lip_frame_isOpen_translateSet {D : Set (Vec d)} (hD : IsOpen D) (z : Vec d) :
    IsOpen (translateSet z D) := by
  have : translateSet z D = (fun x : Vec d => x - z) ⁻¹' D := by
    ext x
    rw [mem_translateSet_iff_sub_mem]
    rfl
  rw [this]
  exact hD.preimage (continuous_id.sub continuous_const)

/-- **F0b — a solution on a set, seen from the centre `y`.** -/
theorem lip_frame (d : ℕ) [NeZero d]
    {P : ProbabilityMeasure (ShellSeq d)} (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega ∂P.toMeasure, ∀ (y : Vec d) (D : Set (Vec d)), IsOpen D → Bornology.IsBounded D →
      ∀ (f : Vec d → ℝ) (u : H1Function D),
        IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) D u f (fun _ => 0) →
        ∃ v : H1Function (translateSet (-y) D),
          (∀ x, v.toFun x = u.toFun (x + y)) ∧ (∀ x, v.grad x = u.grad (x + y)) ∧
          IsWeakSolutionOn
            (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
            (translateSet (-y) D) v (fun x => f (x + y)) (fun _ => 0) := by
  filter_upwards [lip_frame_field d hJ3 nu, w0_ae_isElliptic_bounded hJ3 hnu] with omega hF hE
    y D hDo hDb f u hu
  obtain ⟨S, hS, hSx⟩ := hF y
  have hWo := lip_frame_isOpen_translateSet hDo (-y)
  have hWb := lip_frame_isBounded_translateSet hDb (-y)
  have : IsFiniteMeasure (volumeMeasureOn (translateSet (-y) D)) :=
    ⟨by
      simp only [volumeMeasureOn, Measure.restrict_apply_univ]
      exact hWb.measure_lt_top⟩
  have hw := IsWeakSolutionOn.translate (-y) hu
  obtain ⟨Lam, hmeas, hell⟩ := hE D hDb hDo.measurableSet
  have hflux : MemVectorL2 (translateSet (-y) D)
      (fun x => matVecMul (Section6.fullCoefficientRecentered nu omega (x - -y))
        ((u.translate (-y)).grad x)) := by
    refine memVectorL2_matVecMul_of_isEllipticFieldOn
      (lam := nu) (Lam := Lam) (a := fun x => Section6.fullCoefficientRecentered nu omega (x - -y))
      ⟨?_, fun x hx => ?_⟩
      ((MeasureTheory.memLp_pi_iff).2 (u.translate (-y)).gradMemL2)
    · classical
      have hm := (Section6.measurable_fullCoefficientRecentered nu omega).comp
        (measurable_id.sub_const (-y))
      refine measurable_matrix_of_entries fun i j => Measurable.ite hWo.measurableSet ?_
        measurable_const
      exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)
    · exact hell _ (by rwa [mem_translateSet_iff_sub_mem] at hx)
  refine ⟨u.translate (-y), fun x => ?_, fun x => ?_, ?_⟩
  · simp only [H1Function.translate_toFun, sub_neg_eq_add]
  · simp only [H1Function.translate_grad, sub_neg_eq_add]
  · have hab : ∀ x, Section6.fullCoefficientRecentered nu
        (ShellField.translateSequence y omega) x =
        Section6.fullCoefficientRecentered nu omega (x - -y) + S := by
      intro x
      rw [hSx x, sub_neg_eq_add]
    have := (isWeakSolutionOn_congr_const_skew hWo hS hab hflux).2 hw
    simpa only [sub_neg_eq_add] using this

/-- Witness: the Dirac zero law meets `J3`, so the frame lemmas are not vacuous. -/
example [NeZero d] (nu : ℝ) :
    ∀ᵐ omega ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ y : Vec d, ∃ S : Mat d, matTranspose S = -S ∧ ∀ x : Vec d,
        Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega) x =
          Section6.fullCoefficientRecentered nu omega (x + y) + S :=
  lip_frame_field d SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw nu

/-- Witness for the solution transfer: the Dirac zero law, and the zero solution on a ball. -/
example [NeZero d] {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ (y : Vec d) (D : Set (Vec d)), IsOpen D → Bornology.IsBounded D →
      ∀ (f : Vec d → ℝ) (u : H1Function D),
        IsWeakSolutionOn (Section6.fullCoefficientRecentered nu omega) D u f (fun _ => 0) →
        ∃ v : H1Function (translateSet (-y) D),
          (∀ x, v.toFun x = u.toFun (x + y)) ∧ (∀ x, v.grad x = u.grad (x + y)) ∧
          IsWeakSolutionOn
            (Section6.fullCoefficientRecentered nu (ShellField.translateSequence y omega))
            (translateSet (-y) D) v (fun x => f (x + y)) (fun _ => 0) :=
  lip_frame d SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end SuperdiffusionCLT.Section7
