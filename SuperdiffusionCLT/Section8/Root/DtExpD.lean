/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpC
public import SuperdiffusionCLT.Section8.Root.TheoremAAssemblyB

/-!
# The quenched second moment: polynomial data, bump functions, and the stopped position

The quadratic and linear comparison functions with their derivatives, a bump function equal to one
on the ball, the approximation of the stopped integral by a comparison function, and the fact that
the paths of a continuous-path law start at the starting point almost surely.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section8.Brownian (vecLaplacian)
open scoped Pointwise ENNReal NNReal Topology

variable {d : ℕ}

/-- The bilinear form `(x, h) ↦ ∑ x i h i`. -/
noncomputable def dtExp_lam (d : ℕ) : Vec d →L[ℝ] Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

theorem dtExp_lam_apply (x h : Vec d) : dtExp_lam d x h = vecDot x h := by
  simp [dtExp_lam, vecDot]

theorem dtExp_hasFDerivAt_quad (c : ℝ) (x : Vec d) :
    HasFDerivAt (fun y : Vec d => c * vecNormSq y) ((2 * c) • dtExp_lam d x) x := by
  have hs : HasFDerivAt (fun y : Vec d => ∑ i, y i * y i)
      (∑ i : Fin d, (x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) +
        x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) x := by
    refine HasFDerivAt.fun_sum fun i _ => ?_
    exact (hasFDerivAt_apply i x).mul (hasFDerivAt_apply i x)
  have hEq : (∑ i : Fin d, (x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) +
        x i • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) = (2 : ℝ) • dtExp_lam d x := by
    ext h
    simp [dtExp_lam_apply, vecDot, Finset.sum_add_distrib, two_mul]
  have h1 : HasFDerivAt (fun y : Vec d => vecNormSq y) ((2 : ℝ) • dtExp_lam d x) x :=
    hs.congr_fderiv hEq
  have h2 := h1.const_mul c
  have e : c • (2 : ℝ) • dtExp_lam d x = (2 * c) • dtExp_lam d x := by
    rw [smul_smul, mul_comm]
  rw [e] at h2
  exact h2

theorem dtExp_fderiv_quad (c : ℝ) :
    fderiv ℝ (fun y : Vec d => c * vecNormSq y) = fun x => (2 * c) • dtExp_lam d x := by
  funext x
  exact (dtExp_hasFDerivAt_quad c x).fderiv

theorem dtExp_fderiv_quad_basis (c : ℝ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (fun y : Vec d => c * vecNormSq y) x (basisVec i) = 2 * c * x i := by
  rw [dtExp_fderiv_quad]
  simp [dtExp_lam_apply, vecDot, basisVec, Pi.single_apply]

theorem dtExp_vecLaplacian_quad (c : ℝ) (x : Vec d) :
    vecLaplacian (fun y : Vec d => c * vecNormSq y) x = 2 * c * d := by
  rw [Brownian.vecLaplacian_eq_sum_fderiv, dtExp_fderiv_quad]
  have h : fderiv ℝ (fun x : Vec d => (2 * c) • dtExp_lam d x) =
      fun _ => (2 * c) • dtExp_lam d := by
    funext y
    exact (((2 * c) • dtExp_lam d : Vec d →L[ℝ] Vec d →L[ℝ] ℝ).hasFDerivAt (x := y)).fderiv
  rw [h]
  simp [dtExp_lam_apply, vecDot, Pi.single_apply]
  ring

theorem dtExp_contDiff_quad (c : ℝ) : ContDiff ℝ 2 (fun y : Vec d => c * vecNormSq y) := by
  unfold vecNormSq vecDot
  exact contDiff_const.mul (ContDiff.sum fun i _ =>
    (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i))

theorem dtExp_fderiv_lin (e : Vec d) :
    fderiv ℝ (fun y : Vec d => vecDot e y) = fun _ => dtExp_lam d e := by
  funext x
  have : (fun y : Vec d => vecDot e y) = fun y => dtExp_lam d e y := by
    funext y; rw [dtExp_lam_apply]
  rw [this]
  exact ((dtExp_lam d e).hasFDerivAt (x := x)).fderiv

theorem dtExp_fderiv_lin_basis (e x : Vec d) (i : Fin d) :
    fderiv ℝ (fun y : Vec d => vecDot e y) x (basisVec i) = e i := by
  rw [dtExp_fderiv_lin]
  simp [dtExp_lam_apply, vecDot, basisVec, Pi.single_apply]

theorem dtExp_vecLaplacian_lin (e x : Vec d) : vecLaplacian (fun y : Vec d => vecDot e y) x = 0 := by
  rw [Brownian.vecLaplacian_eq_sum_fderiv, dtExp_fderiv_lin]
  simp

theorem dtExp_contDiff_lin (e : Vec d) : ContDiff ℝ 2 (fun y : Vec d => vecDot e y) := by
  unfold vecDot
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i)


/-- A Euclidean ball lies in the sup-norm ball of the same radius. -/
theorem dtExp_norm_lt_of_mem {R : ℝ} (hR : 0 < R) {y : Vec d} (hy : y ∈ euclideanBall (0 : Vec d) R) :
    ‖y‖ < R := by
  simp only [euclideanBall, euclideanSqDist, sub_zero, Set.mem_ofPred_eq] at hy
  rw [pi_norm_lt_iff hR]
  intro i
  have h1 : y i * y i ≤ vecNormSq y := by
    unfold vecNormSq vecDot
    exact Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  exact abs_lt_of_sq_lt_sq (by nlinarith only [h1, hy]) hR.le

/-- **A bump function** equal to one near the ball. -/
theorem dtExp_bump {R : ℝ} (hR : 0 < R) :
    ∃ χ : Vec d → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧
      ∀ y ∈ euclideanBall (0 : Vec d) R, χ =ᶠ[nhds y] fun _ => 1 := by
  let φ : ContDiffBump (0 : Vec d) := ⟨R, 2 * R, hR, by linarith only [hR]⟩
  refine ⟨φ, φ.contDiff, φ.hasCompactSupport, fun y hy => ?_⟩
  have hy' : y ∈ Metric.ball (0 : Vec d) R := by
    rw [mem_ball_zero_iff]; exact dtExp_norm_lt_of_mem hR hy
  exact Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hy') fun z hz =>
    φ.one_of_mem_closedBall (by simpa [φ] using Metric.ball_subset_closedBall hz)

/-- **Approximation of a stopped integral.**  If `Φ` is within `Err` of the bounded comparison
function `P` on a set `K` carrying the stopped position, the integrals differ by at most `Err`. -/
theorem dtExp_integral_approx {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {Y : α → Vec d} (hY : Measurable Y) {K : Set (Vec d)}
    (hYK : ∀ᵐ x ∂μ, Y x ∈ K) {Φ P : Vec d → ℝ} (hΦ : Continuous Φ) (hP : Continuous P)
    {Err M : ℝ} (hK : ∀ y ∈ K, |Φ y - P y| ≤ Err) (hM : ∀ y ∈ K, |P y| ≤ M) :
    |(∫ x, Φ (Y x) ∂μ) - ∫ x, P (Y x) ∂μ| ≤ Err := by
  have hPint : Integrable (fun x => P (Y x)) μ :=
    Integrable.of_bound (hP.measurable.comp hY).aestronglyMeasurable M
      (hYK.mono fun x hx => by simpa [Real.norm_eq_abs] using hM _ hx)
  have hΦint : Integrable (fun x => Φ (Y x)) μ :=
    Integrable.of_bound (hΦ.measurable.comp hY).aestronglyMeasurable (M + Err)
      (hYK.mono fun x hx => by
        rw [Real.norm_eq_abs]
        have h1 := hK _ hx
        have h2 := hM _ hx
        have h3 : |Φ (Y x)| ≤ |P (Y x)| + |Φ (Y x) - P (Y x)| := by
          have := abs_add_le (P (Y x)) (Φ (Y x) - P (Y x))
          simpa using this
        linarith only [h1, h2, h3])
  rw [← integral_sub hΦint hPint]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => Φ (Y x) - P (Y x)) (C := Err)
    (hYK.mono fun x hx => by simpa [Real.norm_eq_abs] using hK _ hx)
  simpa [Real.norm_eq_abs] using this

/-- The paths of a continuous-path law start at the starting point, almost surely. -/
theorem dtExp_ae_start {S : SubMarkovKernelSemigroup (Vec d)}
    {Q : Vec d → Measure (ContinuousPath (Vec d))} (hQ : IsContinuousPathLaw S Q) (x : Vec d) :
    ∀ᵐ path ∂(Q x), path 0 = x := by
  have h := thmA_marginal hQ 0 x
  have h0 : S 0 x = Measure.dirac x := by
    show S.kernel 0 x = _
    rw [S.kernel_zero]; exact ProbabilityTheory.Kernel.id_apply x
  rw [h0] at h
  have hae : ∀ᵐ y ∂(Measure.dirac x), y = x := by
    rw [ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  rw [← h] at hae
  exact ae_of_ae_map (ContinuousPath.measurable_coordinateProcess 0).aemeasurable hae

end SuperdiffusionCLT.Section8
