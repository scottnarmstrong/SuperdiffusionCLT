/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.ExitEstimate
public import SuperdiffusionCLT.Section8.Prereq.BallExitTimeC

/-!
# Comparison of the exit Laplace transforms of nested balls

For the process of the marginal field, `f_R = 1 - lam w_R` is the Laplace transform of the exit time
from the ball of radius `R` (`ballExit_laplace_convex`).  The restart step of `ExitEstimate.lean`
turns the exit from a smaller concentric ball into a comparison of the corresponding continuous
profiles: if `f_R ≤ M` on the closed ball of radius `ρ < R`, then `f_R ≤ M f_ρ` in the open ball of
radius `ρ`.  This is a statement about continuous functions only; the process enters through the
identification of the Laplace transforms.

* `exitEst_ball_compare`: the comparison, for the positive parts `max (1 - lam w) 0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

/-- Membership in the centred Euclidean ball. -/
theorem exitEst_mem_ball {d : ℕ} (x : Vec d) (r : ℝ) :
    x ∈ euclideanBall (0 : Vec d) r ↔ vecNormSq x < r ^ 2 := by
  simp [euclideanBall, euclideanSqDist]

/-- The closed centred ball of radius `ρ < R` lies in the open ball of radius `R`. -/
theorem exitEst_closedBall_subset {d : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (x : Vec d)
    (hx : vecNormSq x ≤ ρ ^ 2) : x ∈ euclideanBall (0 : Vec d) R := by
  rw [exitEst_mem_ball]
  have : ρ ^ 2 < R ^ 2 := by nlinarith only [hρ, hρR]
  linarith only [hx, this]

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d}

/-- **Comparison of nested balls.**  Let `w_ρ`, `w_R` be the continuous zero-trace profiles of the
balls of radii `ρ < R` (shift `lam`).  If `max (1 - lam w_R) 0 ≤ M` on the closed ball of radius
`ρ`, then `max (1 - lam w_R) 0 ≤ M max (1 - lam w_ρ) 0` in the open ball of radius `ρ`. -/
theorem exitEst_ball_compare (D : FieldInputData d nu k) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {lam : ℝ} (hlam : 0 < lam) {w₁ w₂ : Vec d → ℝ}
    (u₁ : H10Function (euclideanBall (0 : Vec d) ρ)) (hw₁ : Continuous w₁)
    (hoff₁ : ∀ y, y ∉ euclideanBall (0 : Vec d) ρ → w₁ y = 0)
    (hwu₁ : ∀ᵐ y ∂volumeMeasureOn (euclideanBall (0 : Vec d) ρ), w₁ y = u₁.toH1Function.toFun y)
    (hsol₁ : IsScalarForcedWeakSolution D.analyticData.a (euclideanBall (0 : Vec d) ρ)
      (fun y => 1 - lam * u₁.toH1Function.toFun y) u₁.toH1Function)
    (u₂ : H10Function (euclideanBall (0 : Vec d) R)) (hw₂ : Continuous w₂)
    (hoff₂ : ∀ y, y ∉ euclideanBall (0 : Vec d) R → w₂ y = 0)
    (hwu₂ : ∀ᵐ y ∂volumeMeasureOn (euclideanBall (0 : Vec d) R), w₂ y = u₂.toH1Function.toFun y)
    (hsol₂ : IsScalarForcedWeakSolution D.analyticData.a (euclideanBall (0 : Vec d) R)
      (fun y => 1 - lam * u₂.toH1Function.toFun y) u₂.toH1Function)
    {M : ℝ} (hM : ∀ y : Vec d, vecNormSq y ≤ ρ ^ 2 → max (1 - lam * w₂ y) 0 ≤ M)
    {x : Vec d} (hx : vecNormSq x < ρ ^ 2) :
    max (1 - lam * w₂ x) 0 ≤ M * max (1 - lam * w₁ x) 0 := by
  have hV₁ := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) hρ
  have hV₂ := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) (hρ.trans hρR)
  have hrep₁ := ballExit_rep_of_weakSolution D.analyticData hV₁ hlam hwu₁ hsol₁
  have hrep₂ := ballExit_rep_of_weakSolution D.analyticData hV₂ hlam hwu₂ hsol₂
  have hx₁ : x ∈ euclideanBall (0 : Vec d) ρ := (exitEst_mem_ball x ρ).2 hx
  have hM0 : 0 ≤ M := (le_max_right _ _).trans (hM x hx.le)
  have h1 := ballExit_lintegral_exp_neg_exitTime_onePoint D hV₁ ⟨lam, hlam⟩ hw₁ hoff₁ hrep₁ hx₁
  have h2 := fun z (hz : z ∈ euclideanBall (0 : Vec d) R) =>
    ballExit_lintegral_exp_neg_exitTime_onePoint D hV₂ ⟨lam, hlam⟩ hw₂ hoff₂ hrep₂ hz
  let := D.logGrowthBounds.processInput.toOnePointRegular.metricSpace
  let := D.logGrowthBounds.processInput.toOnePointRegular.completeSpace
  have hFeller := D.logGrowthBounds.resolvent.isFellerKernelSemigroup_onePointKernelSemigroup
  have hK := D.logGrowthBounds.processInput.toOnePointRegular.kolmogorovRegular
  have hcompact : IsCompact
      (((↑) : Vec d → OnePoint (Vec d)) '' euclideanClosedBall (0 : Vec d) ρ) :=
    (isCompact_euclideanClosedBall (0 : Vec d) hρ.le).image OnePoint.continuous_coe
  have hcl0 : closure (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall (0 : Vec d) ρ) ⊆
      ((↑) : Vec d → OnePoint (Vec d)) '' euclideanClosedBall (0 : Vec d) ρ := by
    refine closure_minimal (Set.image_mono fun y hy => ?_) hcompact.isClosed
    exact le_of_lt (show euclideanSqDist y 0 < ρ ^ 2 from hy)
  have hcl : closure (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall (0 : Vec d) ρ) ⊆
      ((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall (0 : Vec d) R := by
    refine hcl0.trans (Set.image_mono fun y hy => ?_)
    refine exitEst_closedBall_subset hρ hρR y ?_
    simpa [euclideanClosedBall, euclideanSqDist] using hy
  have hstep := Process.exitEst_lintegral_step
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup hFeller hK
    (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall (0 : Vec d) ρ)
    (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall (0 : Vec d) R)
    (OnePoint.isOpen_image_coe.mpr hV₁.isOpen) (OnePoint.isOpen_image_coe.mpr hV₂.isOpen) hcl
    lam hlam.le (ENNReal.ofReal M) ENNReal.ofReal_ne_top ?_ (x : OnePoint (Vec d)) ⟨x, hx₁, rfl⟩
  · have key : ENNReal.ofReal (1 - lam * w₂ x) ≤
        ENNReal.ofReal M * ENNReal.ofReal (1 - lam * w₁ x) :=
      calc ENNReal.ofReal (1 - lam * w₂ x) =
            _ := (h2 x (exitEst_closedBall_subset hρ hρR x hx.le)).symm
        _ ≤ _ := hstep
        _ = ENNReal.ofReal M * ENNReal.ofReal (1 - lam * w₁ x) :=
          congrArg (ENNReal.ofReal M * ·) h1
    rw [← ENNReal.ofReal_mul hM0, ENNReal.ofReal_le_ofReal_iff' ] at key
    rcases key with hk | hk
    · calc max (1 - lam * w₂ x) 0 ≤ max (M * (1 - lam * w₁ x)) 0 := max_le_max hk le_rfl
        _ = M * max (1 - lam * w₁ x) 0 := by
          rcases le_total (1 - lam * w₁ x) 0 with h | h
          · rw [max_eq_right h, mul_zero, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hM0 h)]
          · rw [max_eq_left h, max_eq_left (mul_nonneg hM0 h)]
    · rw [max_eq_right hk]
      exact mul_nonneg hM0 (le_max_right _ _)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hcl0 hy
    have hz' : vecNormSq z ≤ ρ ^ 2 := by simpa [euclideanClosedBall, euclideanSqDist] using hz
    exact (le_of_eq (h2 z (exitEst_closedBall_subset hρ hρR z hz'))).trans
      (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (hM z hz')))

end

end SuperdiffusionCLT.Section8
