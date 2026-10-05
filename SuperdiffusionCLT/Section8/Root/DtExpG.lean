/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpF

/-!
# The quenched moments at a fixed sample, before the numerics

For the process input `D` of the sample, the ball of radius `ε⁻¹`, and a continuous-path law `Q`
of the kernel semigroup `S`, the second moment and the mean of `S t 0` are controlled by the
homogenization error `E₀`, the exit probability `p = Q 0 [T ≤ t]`, and a bound `B₄` on the fourth
moment of the sup norm.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped Pointwise ENNReal NNReal Topology

variable {d : ℕ} [NeZero d] {nu : ℝ}

theorem dtExp_det {cStar : ℝ} {omega : ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega))
    (hDa : D.analyticData.a = fullCoefficientRecentered nu omega)
    (ha : ∀ i j, ContDiff ℝ 1 fun y => fullCoefficientRecentered nu omega y i j)
    {ε : ℝ} (hε : 0 < ε) (hs : 0 < opScale cStar ε) {E0 : ℝ} (hE0 : 0 ≤ E0)
    (hA : ∀ (f : Vec d → ℝ) (g u uhom : H1Function ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)),
      IsDirichletSolution (fun x => opScale cStar ε • epField nu omega ε x) _ f g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) _ f g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
          (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)) ≤
        ENNReal.ofReal E0 *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤
              (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹)) +
            eLpNorm f ⊤ (volume.restrict ((ε⁻¹)⁻¹ • euclideanBall (0 : Vec d) ε⁻¹))))
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q) (t : NNReal)
    {B4 : ℝ} (hB4 : 0 ≤ B4)
    (h4 : ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
      ENNReal.ofReal B4) :
    Integrable (fun y : Vec d => vecNormSq y) (D.logGrowthBounds.resolvent.kernelSemigroup t 0) ∧
    (∫ y, vecNormSq y ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
      Real.sqrt ((d : ℝ) ^ 2 * B4)) ∧
    |ε ^ 2 / d * ∫ y, vecNormSq y ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) -
        ε ^ 2 / opScale cStar ε * t| ≤
      2 * (E0 * (2 / d + 1)) +
        ε ^ 2 / d * (Real.sqrt ((d : ℝ) ^ 2 * B4) *
          Real.sqrt ((Q 0).real {w | ContinuousPath.exitTime (euclideanBall (0 : Vec d) ε⁻¹) w ≤
            (t : ℝ≥0∞)}) +
          (ε⁻¹) ^ 2 * (Q 0).real {w | ContinuousPath.exitTime (euclideanBall (0 : Vec d) ε⁻¹) w ≤
            (t : ℝ≥0∞)}) +
        ε ^ 2 / opScale cStar ε * (t * (Q 0).real {w | ContinuousPath.exitTime
          (euclideanBall (0 : Vec d) ε⁻¹) w ≤ (t : ℝ≥0∞)}) ∧
    ∀ i : Fin d, |∫ y, y i ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0)| ≤
      2 * E0 * ε⁻¹ + (Real.sqrt (Real.sqrt ((d : ℝ) ^ 2 * B4)) *
          Real.sqrt ((Q 0).real {w | ContinuousPath.exitTime (euclideanBall (0 : Vec d) ε⁻¹) w ≤
            (t : ℝ≥0∞)}) +
        ε⁻¹ * (Q 0).real {w | ContinuousPath.exitTime (euclideanBall (0 : Vec d) ε⁻¹) w ≤
            (t : ℝ≥0∞)}) := by
  set S := D.logGrowthBounds.resolvent.kernelSemigroup with hS
  set U : Set (Vec d) := euclideanBall (0 : Vec d) ε⁻¹ with hU
  have hRpos : 0 < ε⁻¹ := inv_pos.2 hε
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    (0 : Vec d) hRpos
  have : IsProbabilityMeasure (Q 0) := (hQ 0).1
  have : IsProbabilityMeasure (S t 0) := ⟨D.logGrowthBounds.isConservative_kernelSemigroup t 0⟩
  set A : Set (ContinuousPath (Vec d)) := {w | ContinuousPath.exitTime U w ≤ (t : ℝ≥0∞)} with hA'
  have hAm : MeasurableSet A := dtExp_exit_event_measurable hV.isOpen t
  have hvm : Measurable (fun y : Vec d => vecNormSq y) := by
    unfold vecNormSq vecDot
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul (measurable_pi_apply i)
  obtain ⟨hI4, hm4⟩ := dtExp_four_moment hB4 h4
  have hXm : Measurable (fun w : ContinuousPath (Vec d) => w t) :=
    ContinuousPath.measurable_coordinateProcess t
  obtain ⟨hYm, hYK⟩ := dtExp_stopped_mem hQ hRpos t
  have hmar := thmA_marginal hQ t 0
  have hI4' : Integrable (fun w : ContinuousPath (Vec d) => vecNormSq (w t) ^ 2) (Q 0) := by
    have : Integrable (fun y : Vec d => vecNormSq y ^ 2) ((Q 0).map (fun w => w t)) := by
      rw [hmar]; exact hI4
    exact (integrable_map_measure (hvm.pow_const 2).aestronglyMeasurable hXm.aemeasurable).1 this
  have hm4' : ∫ w, vecNormSq (w t) ^ 2 ∂(Q 0) ≤ (d : ℝ) ^ 2 * B4 := by
    rw [thmA_integral_marginal hQ t 0 (f := fun y : Vec d => vecNormSq y ^ 2)
      (hvm.pow_const 2)]
    exact hm4
  have hXY : ∀ᵐ w ∂(Q 0), w ∉ A → w t = w (ContinuousPath.exitTimeTrunc U t w) := by
    refine Filter.Eventually.of_forall fun w hw => ?_
    rw [dtExp_trunc_eq U t w hw]
  have hR : ∀ᵐ w ∂(Q 0), vecNormSq (w (ContinuousPath.exitTimeTrunc U t w)) ≤ (ε⁻¹) ^ 2 := by
    filter_upwards [hYK] with w hw
    exact dtExp_closure_le hw
  obtain ⟨hint, hb1, hb2, hb3⟩ := dtExp_remove (μ := Q 0) hXm hYm hAm hXY hR hI4' hm4'
  have hm2 : ∫ w, vecNormSq (w t) ∂(Q 0) = ∫ y, vecNormSq y ∂(S t 0) :=
    thmA_integral_marginal hQ t 0 hvm
  have hint' : Integrable (fun y : Vec d => vecNormSq y) (S t 0) := by
    have : Integrable (fun y : Vec d => vecNormSq y) ((Q 0).map (fun w => w t)) := by
      exact (integrable_map_measure hvm.aestronglyMeasurable hXm.aemeasurable).2 hint
    rwa [hmar] at this
  refine ⟨hint', by rw [← hm2]; exact hb1, ?_, fun i => ?_⟩
  · have h2 := dtExp_second_moment D hDa ha hε hs hE0 hA hQ t
    have h3 := dtExp_trunc_gap (U := U) hV.isOpen t (μ := Q 0)
    rw [← hm2]
    set Ysq := ∫ w, vecNormSq (w (ContinuousPath.exitTimeTrunc U t w)) ∂(Q 0)
    set Tm := ∫ w, ((ContinuousPath.exitTimeTrunc U t w : NNReal) : ℝ) ∂(Q 0)
    set m2 := ∫ w, vecNormSq (w t) ∂(Q 0)
    set p := (Q 0).real A
    have hc1 : 0 ≤ ε ^ 2 / d := by positivity
    have hc2 : 0 ≤ ε ^ 2 / opScale cStar ε := by positivity
    have e1 : ε ^ 2 / d * m2 - ε ^ 2 / opScale cStar ε * t =
        (ε ^ 2 / d * Ysq - ε ^ 2 / opScale cStar ε * Tm) + ε ^ 2 / d * (m2 - Ysq) +
          ε ^ 2 / opScale cStar ε * (Tm - t) := by ring
    rw [e1]
    have b1 := abs_mul (ε ^ 2 / d) (m2 - Ysq)
    have b2 := abs_mul (ε ^ 2 / opScale cStar ε) (Tm - t)
    rw [abs_of_nonneg hc1] at b1
    rw [abs_of_nonneg hc2] at b2
    have b3 := abs_add_three (ε ^ 2 / d * Ysq - ε ^ 2 / opScale cStar ε * Tm)
      (ε ^ 2 / d * (m2 - Ysq)) (ε ^ 2 / opScale cStar ε * (Tm - t))
    have b4 : ε ^ 2 / d * |m2 - Ysq| ≤ ε ^ 2 / d * (Real.sqrt ((d : ℝ) ^ 2 * B4) * Real.sqrt p +
        (ε⁻¹) ^ 2 * p) := by gcongr
    have b5 : ε ^ 2 / opScale cStar ε * |Tm - t| ≤ ε ^ 2 / opScale cStar ε * (t * p) := by
      gcongr
    linarith only [b1, b2, b3, b4, b5, h2]
  · have h1 := dtExp_first_moment D hDa ha hε hs hE0 hA (basisVec i) (by
      unfold vecNormSq vecDot basisVec
      simp [Pi.single_apply]) hQ t
    have hrep : ∀ w : ContinuousPath (Vec d), vecDot (basisVec i) (w (ContinuousPath.exitTimeTrunc U t w)) =
        w (ContinuousPath.exitTimeTrunc U t w) i := by
      intro w
      simp [vecDot, basisVec, Pi.single_apply]
    have h1' : |∫ w, w (ContinuousPath.exitTimeTrunc U t w) i ∂(Q 0)| ≤ 2 * E0 * ε⁻¹ := by
      have e : ∫ w, vecDot (basisVec i) (w (ContinuousPath.exitTimeTrunc U t w)) ∂(Q 0) =
          ∫ w, w (ContinuousPath.exitTimeTrunc U t w) i ∂(Q 0) :=
        integral_congr_ae (Filter.Eventually.of_forall hrep)
      rw [← e]; exact h1
    have hcomp : ∫ y, y i ∂(S t 0) = ∫ w, w t i ∂(Q 0) :=
      (thmA_integral_marginal hQ t 0 (f := fun y : Vec d => y i) (measurable_pi_apply i)).symm
    rw [hcomp]
    have h5 := hb3 i
    rw [Real.sqrt_sq hRpos.le] at h5
    have h6 := abs_sub_abs_le_abs_sub (∫ w, w t i ∂(Q 0))
      (∫ w, w (ContinuousPath.exitTimeTrunc U t w) i ∂(Q 0))
    linarith only [h1', h5, h6]

end SuperdiffusionCLT.Section8
