/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsI
public import SuperdiffusionCLT.Section8.Prereq.ResolventEstimateC
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationB
public import SuperdiffusionCLT.Section8.Prereq.ExitEstimateC

/-!
# Comparison of the Dirichlet solution on a ball with the homogenized solution

`gen_hom_bound`: from the resolvent estimate for the ball `B_m` at one scale (with zero shift and
zero boundary datum), a continuous representative `w` of the zero-trace solution of
`∇·(a∇w) = -G`, `G = -s · ½Δu₀`, is within `Ce · sup|G|` of `s u₀` everywhere.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
  SuperdiffusionCLT.Section7 SuperdiffusionCLT.Section8.DivergenceForm
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_hom_bound [NeZero d] {nu cs ε' : ℝ}
    {omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d} {m : ℝ} (hm : 1 ≤ m)
    {Ce : ℝ} (hCe : 0 ≤ Ce)
    (hhom : ∀ (f : Vec d → ℝ) (g u uhom : H1Function (euclidBall (d := d) m)),
      IsDirichletSolution (fun x => opScale cs ε' • epField nu omega ε' x) (euclidBall m)
        (fun x => f x - 0 * u.toFun x) g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclidBall m)
        (fun x => f x - 0 * uhom.toFun x) g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict (euclidBall m)) ≤
        ENNReal.ofReal Ce *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (euclidBall m)) +
            eLpNorm (fun x => f x - 0 * u.toFun x) ⊤ (volume.restrict (euclidBall m))))
    {u0 : Vec d → ℝ} (hu0 : ContDiff ℝ (⊤ : ℕ∞) u0) (hu0s : tsupport u0 ⊆ euclidBall (d := d) 1)
    (s : ℝ) {G : Vec d → ℝ}
    (hG : ∀ y, G y = -(s * ((1 / 2) * Brownian.vecLaplacian u0 y))) (hGc : Continuous G)
    {Gb : ℝ} (hGb : ∀ y, |G y| ≤ Gb)
    {wR : Vec d → ℝ} (hwc : Continuous wR) (hw0 : ∀ y, y ∉ euclidBall (d := d) m → wR y = 0)
    (uR : H10Function (euclidBall (d := d) m))
    (hae : ∀ᵐ y ∂volume.restrict (euclidBall (d := d) m), wR y = uR.toH1Function.toFun y)
    (hsol : IsWeakSolutionOn (fun x => opScale cs ε' • epCoeff nu omega ε' x)
      (euclidBall (d := d) m) uR.toH1Function G (fun _ => 0)) :
    ∀ y, |wR y - s * u0 y| ≤ Ce * Gb := by
  have hm0 : 0 < m := by linarith only [hm]
  have hcvx := gen_cvx (d := d) hm0
  have hGb0 : 0 ≤ Gb := (abs_nonneg _).trans (hGb 0)
  have hsub1 : euclidBall (d := d) 1 ⊆ euclidBall (d := d) m := euclidBall_mono zero_le_one hm
  have hh2 : ContDiff ℝ 2 fun y => s * u0 y :=
    contDiff_const.mul (hu0.of_le (by simp))
  set uhom : H1Function (euclidBall (d := d) m) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hcvx (hh2.of_le (by norm_num)) with huhom
  have huhomf : uhom.toFun = fun y => s * u0 y := rfl
  have hhalf : ∀ x, -(divForm 1 (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (fun y => s * u0 y) x) =
      G x := fun x => by
    rw [divForm_const_smul_one _ _ hh2,
      exitEst_lap_const_mul s (hu0.of_le (by simp)).contDiffAt, hG]
    ring
  have hweakhom : IsWeakSolutionOn (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclidBall m) uhom
      (fun x => G x - 0 * uhom.toFun x) (fun _ => 0) := by
    have h := (domId_weak_of_classical hcvx (a := fun _ => (1 / 2 : ℝ) • (1 : Mat d))
      (fun i j => contDiff_const) hh2).2
    intro φ
    have := h φ
    have h0 : ∫ x in euclidBall (d := d) m, vecDot ((fun _ => (0 : Vec d)) x) (φ.toH1Function.grad x) = 0 := by
      simp [vecDot]
    rw [h0, add_zero]
    refine this.trans (integral_congr_ae (Eventually.of_forall fun x => ?_))
    show -(divForm 1 (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (fun y => s * u0 y) x) * φ.toFun x =
      (G x - 0 * uhom.toFun x) * φ.toH1Function.toFun x
    rw [hhalf x]; ring
  have hK : IsCompact (tsupport u0) := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _) ?_
    exact (Metric.isBounded_ball.subset (euclidBall_subset_ball zero_lt_one)).subset hu0s
  have hhomH10 : MemH10 (euclidBall (d := d) m) (fun x => uhom.toFun x - (0 : H1Function (euclidBall (d := d) m)).toFun x) := by
    have := memH10_of_compactSupport hcvx uhom hK (hu0s.trans hsub1) (fun x hx => by
      have : u0 x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [huhomf, this])
    simpa using this
  have hDhom : IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclidBall m)
      (fun x => G x - 0 * uhom.toFun x) 0 uhom := ⟨hweakhom, hhomH10⟩
  have hDu : IsDirichletSolution (fun x => opScale cs ε' • epField nu omega ε' x) (euclidBall m)
      (fun x => G x - 0 * uR.toH1Function.toFun x) 0 uR.toH1Function :=
    ⟨rc_isWeakSolutionOn_congr (fun _ => rfl) (fun x => by simp) (fun _ => rfl) hsol,
      ⟨uR, by funext x; simp⟩⟩
  have hb := hhom G 0 uR.toH1Function uhom hDu hDhom
  have hg0 : eLpNorm (fun x => eucNorm ((0 : H1Function (euclidBall (d := d) m)).grad x)) ⊤
      (volume.restrict (euclidBall m)) = 0 := by
    have : (fun x => eucNorm ((0 : H1Function (euclidBall (d := d) m)).grad x)) = fun _ => 0 := by
      funext x; simp [eucNorm, vecNormSq, vecDot]
    rw [this]; simp
  have hG2 : eLpNorm (fun x => G x - 0 * uR.toH1Function.toFun x) ⊤
      (volume.restrict (euclidBall m)) ≤ ENNReal.ofReal Gb := by
    simp only [zero_mul, sub_zero]
    have := eLpNorm_le_of_ae_bound (μ := volume.restrict (euclidBall (d := d) m)) (p := ⊤)
      (f := G) hGc.aestronglyMeasurable (C := Gb) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hGb x)
    simpa using this
  rw [hg0, zero_add] at hb
  have hb2 := hb.trans (mul_le_mul_right hG2 _)
  have hfin : eLpNorm (fun x => uR.toH1Function.toFun x - uhom.toFun x) ⊤
      (volume.restrict (euclidBall m)) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb2
  have hae1 := resEst_ae_abs_le (U := euclidBall (d := d) m) hfin
  have hval : (eLpNorm (fun x => uR.toH1Function.toFun x - uhom.toFun x) ⊤
      (volume.restrict (euclidBall m))).toReal ≤ Ce * Gb := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top) hb2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCe, ENNReal.toReal_ofReal hGb0] at this
  have hae2 : ∀ᵐ y ∂volume.restrict (euclidBall (d := d) m), |wR y - s * u0 y| ≤ Ce * Gb := by
    filter_upwards [hae1, hae] with y h1 h2
    rw [h2]
    exact h1.trans hval
  intro y
  by_cases hy : y ∈ euclidBall (d := d) m
  · exact gen_abs_le_of_ae (isOpen_euclidBall _) (f := fun y => wR y - s * u0 y)
      (hwc.sub (continuous_const.mul hu0.continuous)) hae2 y hy
  · have h0 : u0 y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hsub1 (hu0s h))
    rw [hw0 y hy, h0]
    simpa using mul_nonneg hCe hGb0

end SuperdiffusionCLT.Section8
