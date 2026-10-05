/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HolderGradient
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Duality

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Hölder gradient on a cube from an `L^p` weak Hessian

If `w ∈ H¹(Q)` has a weak Hessian `D²w ∈ L̲^p(Q)` with `p > d`, then `∇w` has a continuous
representative on the open cube `Q`, which is Hölder continuous of exponent `1 - d/p`:
`|∇w(x) - ∇w(y)| ≤ 4d/(1-d/p) |x-y|^{1-d/p} |Q|^{1/p} ‖D²w‖_{L̲^p(Q)}`.
Each `∂ᵢw` is a `W^{1,p}` function (`toW1pOfGradMemLp`), and the `W^{1,p}` Morrey inequality
applies on the cube, which is an axis cube.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The pointwise Hessian row is bounded by the Hilbert norm of the Hessian matrix. -/
theorem holderGradient_row_norm_le (A : Mat d) (i : Fin d) :
    ‖(fun j => A i j : Vec d)‖ ≤ ‖HilbertMat.ofMat A‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
    simpa only [Real.norm_eq_abs] using holderGradient_abs_entry_le A i j

/-- **Hölder gradient on a cube**: a weak Hessian in `L̲^p`, `p > d`, makes `∇w` Hölder
continuous of exponent `1 - d/p` on the open cube, with the stated constant. -/
theorem holderGradient_of_weakHessian [NeZero d] (Q : TriadicCube d) {p : ℝ}
    (hp : (d : ℝ) < p) {w : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) w)
    (hH : MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
      (normalizedCubeMeasure Q)) :
    ∃ g : Vec d → Vec d, ContinuousOn g (openCubeSet Q) ∧
      (∀ i, (fun x => g x i) =ᵐ[volume.restrict (openCubeSet Q)] fun x => w.grad x i) ∧
      ∀ x ∈ openCubeSet Q, ∀ y ∈ openCubeSet Q,
        ‖g x - g y‖ ≤ 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * ‖x - y‖ ^ (1 - (d : ℝ) / p) *
          (cubeScaleFactor Q ^ ((d : ℝ) / p) *
            cubeLpNorm Q (ENNReal.ofReal p)
              (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hp0 : 0 < p := by linarith only [hd1, hp]
  have hp1 : (1 : ℝ≥0∞) < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff hp0).2 (by linarith only [hd1, hp])
  let pe : FiniteLpExponent := ⟨ENNReal.ofReal p, hp1, ENNReal.ofReal_lt_top⟩
  have hU := isOpenBoundedConvexDomain_openCubeSet Q
  have hmat := holderGradient_memLp_restrict Q hH
  have hent : ∀ i j, MemLp (fun x => H.hess i j x) (ENNReal.ofReal p)
      (volume.restrict (openCubeSet Q)) := fun i j =>
    hmat.of_le (H.hess_memL2 i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using holderGradient_abs_entry_le (fun a b => H.hess a b x) i j)
  have hgrad : ∀ i, GradMemLpOn (openCubeSet Q) pe.exponent (H.gradCoordH1Function i).grad :=
    fun i j => hent i j
  let uW : ∀ i, W1pFunction (openCubeSet Q) (ENNReal.ofReal p) := fun i =>
    (H.gradCoordH1Function i).toW1pOfGradMemLp hU pe (hgrad i)
  have hset := CubeCalderonZygmund.openCubeSet_eq_axisCube_triadicCube Q
  have hL : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale
  let uA : ∀ i, W1pFunction (axisCube (CubeCalderonZygmund.triadicCubeAxisCorner Q) (cubeScaleFactor Q))
      (ENNReal.ofReal p) := fun i =>
    { toFun := (uW i).toFun
      grad := (uW i).grad
      memLp := by rw [← hset]; exact (uW i).memLp
      gradMemLp := by rw [← hset]; exact (uW i).gradMemLp
      hasWeakGradient := by rw [← hset]; exact (uW i).hasWeakGradient }
  have hr : volume.restrict (axisCube (CubeCalderonZygmund.triadicCubeAxisCorner Q)
      (cubeScaleFactor Q)) = volume.restrict (openCubeSet Q) := by rw [← hset]
  have hrep := fun i => w1p_exists_continuous_representative hd0 hL hp (uA i)
  choose ub hubc hubae hubb using hrep
  refine ⟨fun x i => ub i x, ?_, ?_, ?_⟩
  · rw [hset, continuousOn_pi]; exact fun i => hubc i
  · intro i
    rw [← hr]
    exact hubae i
  · intro x hx y hy
    have hxA : x ∈ axisCube (CubeCalderonZygmund.triadicCubeAxisCorner Q) (cubeScaleFactor Q) := hset ▸ hx
    have hyA : y ∈ axisCube (CubeCalderonZygmund.triadicCubeAxisCorner Q) (cubeScaleFactor Q) := hset ▸ hy
    set N := cubeLpNorm Q (ENNReal.ofReal p)
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) with hN
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
        (volume.restrict (axisCube (CubeCalderonZygmund.triadicCubeAxisCorner Q) (cubeScaleFactor Q)))).toReal ≤
          cubeScaleFactor Q ^ ((d : ℝ) / p) * N := by
      intro i
      rw [hr]
      have hmono : eLpNorm (fun w => ‖(uA i).grad w‖) (ENNReal.ofReal p)
          (volume.restrict (openCubeSet Q)) ≤ eLpNorm
            (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
            (volume.restrict (openCubeSet Q)) :=
        eLpNorm_mono ((aemeasurable_pi_iff.2
          fun j => (hent i j).aestronglyMeasurable.aemeasurable).aestronglyMeasurable : AEStronglyMeasurable
            (fun w => (uA i).grad w) _).norm fun x => by
          rw [norm_norm]; exact holderGradient_row_norm_le (fun a b => H.hess a b x) i
      have hfin : eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
          (ENNReal.ofReal p) (volume.restrict (openCubeSet Q)) ≠ ⊤ := hmat.eLpNorm_ne_top
      refine (ENNReal.toReal_mono hfin hmono).trans ?_
      have hle := holderGradient_eLpNorm_restrict_le Q (p := ENNReal.ofReal p)
        (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
      have hfin2 : ENNReal.ofReal (cubeVolume Q) ^ (1 / ENNReal.ofReal p).toReal *
          eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (ENNReal.ofReal p)
            (normalizedCubeMeasure Q) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
          ENNReal.ofReal_ne_top) hH.eLpNorm_ne_top
      refine (ENNReal.toReal_mono hfin2 hle).trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (cubeVolume_pos Q).le]
      congr 1
      have : (1 / ENNReal.ofReal p).toReal = p⁻¹ := by
        rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le]
      rw [this]
      show (cubeScaleFactor Q ^ d) ^ p⁻¹ = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
      congr 1
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hMx (mul_nonneg
      (Real.rpow_nonneg hL.le _) hN0))).2 fun i => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact (hubb i x hxA y hyA).trans (mul_le_mul_of_nonneg_left (hrow i) hMx)

end SuperdiffusionCLT.Section7
