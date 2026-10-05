/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsF
public import SuperdiffusionCLT.Section8.Prereq.DirichletRepresentationD
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateD

/-!
# Continuous Dirichlet solutions on the balls for the rescaled field

For the recentred marginal field `A` carrying the process input `D`, a continuous datum `G`, a
scale `ε' > 0` and a radius `n > 0`: there is a continuous function `w`, vanishing off `B_n`, which
agrees almost everywhere with an `H¹₀(B_n)` function `u` solving
`-∇·(opScale(ε') A(·/ε') ∇u) = G` weakly (`gen_scaled_dirichlet`).  The solution is the dilate of
the zero-trace solution on the ball of radius `n/ε'` of the unscaled problem.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_euclideanBall_zero (r : ℝ) :
    euclideanBall (0 : Vec d) r = euclidBall (d := d) r := by
  ext x
  simp [euclideanBall, euclideanSqDist, euclidBall]

theorem gen_ball_dilate {ε' : ℝ} (hε' : 0 < ε') {n : ℝ} :
    (ε'⁻¹)⁻¹ • euclideanBall (0 : Vec d) (ε'⁻¹ * n) = euclidBall (d := d) n := by
  rw [gen_euclideanBall_zero, decayEst_euclidBall_smul (by simpa using hε'), inv_inv]
  congr 1
  field_simp

theorem gen_scaled_dirichlet [NeZero d] {nu : ℝ}
    {omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega)) (cStar : ℝ) {ε' : ℝ} (hε' : 0 < ε')
    (hs' : 0 < opScale cStar ε') {G : Vec d → ℝ} (hGc : Continuous G)
    (hGs : HasCompactSupport G) {n : ℝ} (hn : 0 < n) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclidBall (d := d) n)), Continuous w ∧
      (∀ y, y ∉ euclidBall (d := d) n → w y = 0) ∧
      (∀ᵐ y ∂volume.restrict (euclidBall (d := d) n), w y = u.toH1Function.toFun y) ∧
      IsWeakSolutionOn (fun x => opScale cStar ε' • epCoeff nu omega ε' x)
        (euclidBall (d := d) n) u.toH1Function G (fun _ => 0) := by
  set c' := opScale cStar ε' with hc'
  have hs : ε'⁻¹ ≠ 0 := inv_ne_zero hε'.ne'
  have hr : 0 < ε'⁻¹ * n := by positivity
  set f : Vec d → ℝ := fun y => (ε' ^ 2 / c') * G (ε' • y) with hf
  have hfc : Continuous f :=
    continuous_const.mul (hGc.comp (continuous_const_smul ε'))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y, |f y| ≤ M := by
    have hcs : HasCompactSupport f := by
      have : HasCompactSupport fun y : Vec d => G (ε' • y) :=
        hGs.comp_isClosedEmbedding ((Homeomorph.smulOfNeZero ε' hε'.ne').isClosedEmbedding)
      exact this.mul_left (f := fun _ => ε' ^ 2 / c')
    obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hcs
    exact ⟨M, fun y => by simpa [Real.norm_eq_abs] using hM y⟩
  obtain ⟨w, u, hwc, hw0, hwu, hsol, -⟩ := dirRep_signed D 0 hr hfc.measurable hM
  have hweakV : IsWeakSolutionOn (fullCoefficientRecentered nu omega) (euclideanBall 0 (ε'⁻¹ * n))
      u.toH1Function f (fun _ => 0) := by
    intro φ
    have := hsol.2 φ
    simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero]
    exact this
  have hdil := IsWeakSolutionOn.dilate_h10 hs hweakV
  have h3 := IsWeakSolutionOn.smul c' hdil
  have hset : (ε'⁻¹)⁻¹ • euclideanBall (0 : Vec d) (ε'⁻¹ * n) = euclidBall (d := d) n :=
    gen_ball_dilate hε'
  have key : ∀ T : Set (Vec d), (ε'⁻¹)⁻¹ • euclideanBall (0 : Vec d) (ε'⁻¹ * n) = T →
      ∃ u' : H10Function T, (∀ x, u'.toH1Function.toFun x = u.toH1Function.toFun (ε'⁻¹ • x)) ∧
        IsWeakSolutionOn (fun x => opScale cStar ε' • epCoeff nu omega ε' x) T u'.toH1Function G
          (fun _ => 0) := by
    intro T hT
    subst hT
    refine ⟨u.dilateArg hs, fun x => by
      simp [H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun], ?_⟩
    refine rc_isWeakSolutionOn_congr (fun _ => rfl) (fun y => ?_) (fun y => ?_) h3
    · simp only [hf, smul_smul, mul_inv_cancel₀ hε'.ne', one_smul]
      field_simp
    · simp
  obtain ⟨u', hu'1, hu'2⟩ := key _ hset
  refine ⟨fun x => w (ε'⁻¹ • x), u', hwc.comp (continuous_const_smul _), fun y hy => hw0 _ ?_,
    ?_, hu'2⟩
  · rw [gen_euclideanBall_zero]
    intro h
    apply hy
    have h' : vecNormSq (ε'⁻¹ • y) < (ε'⁻¹ * n) ^ 2 := h
    rw [vecNormSq_smul, mul_pow] at h'
    have hp : 0 < (ε'⁻¹) ^ 2 := by positivity
    exact lt_of_mul_lt_mul_left h' hp.le
  · have := exitEst_ae_dilate (d := d) hs (euclideanBall (0 : Vec d) (ε'⁻¹ * n))
      (P := fun z => w z = u.toH1Function.toFun z) hwu
    rw [hset] at this
    filter_upwards [this] with y hy
    rw [hu'1]
    exact hy

end SuperdiffusionCLT.Section8
