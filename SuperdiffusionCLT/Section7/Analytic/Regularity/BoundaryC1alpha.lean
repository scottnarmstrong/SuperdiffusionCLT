/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HolderGradientB
public import SuperdiffusionCLT.Section7.Analytic.Morrey.W1pD

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Hölder gradient on an axis cube inside an open set

If `w ∈ H¹(U)` has a weak Hessian on `U` whose `L^p` norm on an axis cube `Q ⊆ U` is finite, with
`p > d`, then `∇w` has a continuous representative on `Q`, Hölder continuous of exponent
`1 - d/p`. This is the form used up to the flat face of a half cube, where the axis cubes
`(a, a+s)^{d-1} × (0, s)` lie in the half cube.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Hölder gradient on an axis cube inside `U`.** -/
theorem r3b_holderGradient_axisCube [NeZero d] {U : Set (Vec d)} {z : Vec d}
    {L : ℝ} (hL : 0 < L) (hsub : axisCube z L ⊆ U) {p : ℝ} (hp : (d : ℝ) < p)
    {w : H1Function U} (H : HasWeakHessianOn U w)
    (hH : MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
      (volume.restrict (axisCube z L))) :
    ∃ g : Vec d → Vec d, ContinuousOn g (axisCube z L) ∧
      (∀ i, (fun x => g x i) =ᵐ[volume.restrict (axisCube z L)] fun x => w.grad x i) ∧
      ∀ x ∈ axisCube z L, ∀ y ∈ axisCube z L,
        ‖g x - g y‖ ≤ 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) *
          (eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
            (volume.restrict (axisCube z L))).toReal := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hp0 : 0 < p := by linarith only [hd1, hp]
  have hp1 : (1 : ℝ≥0∞) < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff hp0).2 (by linarith only [hd1, hp])
  let pe : FiniteLpExponent := ⟨ENNReal.ofReal p, hp1, ENNReal.ofReal_lt_top⟩
  have hU := isOpenBoundedConvexDomain_axisCube z L
  have hmeasQ : volume.restrict (axisCube z L) ≤ volume.restrict U :=
    Measure.restrict_mono hsub le_rfl
  have hent : ∀ i j, MemLp (fun x => H.hess i j x) (ENNReal.ofReal p)
      (volume.restrict (axisCube z L)) := fun i j =>
    hH.of_le ((H.hess_memL2 i j).aestronglyMeasurable.mono_measure hmeasQ)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using holderGradient_abs_entry_le (fun a b => H.hess a b x) i j)
  let gc : ∀ i, H1Function (axisCube z L) := fun i =>
    (H.gradCoordH1Function i).restrict hU.isOpen hsub
  have hgrad : ∀ i, GradMemLpOn (axisCube z L) pe.exponent (gc i).grad :=
    fun i j => hent i j
  let uA : ∀ i, W1pFunction (axisCube z L) (ENNReal.ofReal p) := fun i =>
    (gc i).toW1pOfGradMemLp hU pe (hgrad i)
  have hrep := fun i => w1p_exists_continuous_representative hd0 hL hp (uA i)
  choose ub hubc hubae hubb using hrep
  refine ⟨fun x i => ub i x, ?_, ?_, ?_⟩
  · rw [continuousOn_pi]; exact fun i => hubc i
  · intro i
    exact hubae i
  · intro x hx y hy
    set N := (eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
      (volume.restrict (axisCube z L))).toReal with hN
    have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
    have hα : 0 < 1 - (d : ℝ) / p := by
      have : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hp
      linarith only [this]
    have hC0 : 0 ≤ 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) := by
      have : 0 < 1 / (1 - (d : ℝ) / p) := one_div_pos.2 hα
      positivity
    have hMx : 0 ≤ 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) :=
      mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg _) _)
    have hrow : ∀ i, (eLpNorm (fun w => ‖(uA i).grad w‖) (ENNReal.ofReal p)
        (volume.restrict (axisCube z L))).toReal ≤ N := by
      intro i
      have hmono : eLpNorm (fun w => ‖(uA i).grad w‖) (ENNReal.ofReal p)
          (volume.restrict (axisCube z L)) ≤ eLpNorm
            (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
            (volume.restrict (axisCube z L)) :=
        eLpNorm_mono ((aemeasurable_pi_iff.2
          fun j => (hent i j).aestronglyMeasurable.aemeasurable).aestronglyMeasurable :
            AEStronglyMeasurable (fun w => (uA i).grad w) _).norm fun x => by
          rw [norm_norm]; exact holderGradient_row_norm_le (fun a b => H.hess a b x) i
      exact ENNReal.toReal_mono hH.eLpNorm_ne_top hmono
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hMx hN0)).2 fun i => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact (hubb i x hx y hy).trans (mul_le_mul_of_nonneg_left (hrow i) hMx)

end SuperdiffusionCLT.Section7
