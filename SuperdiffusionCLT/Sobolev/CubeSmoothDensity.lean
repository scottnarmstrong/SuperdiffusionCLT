/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
public import Homogenization.Sobolev.H1.BasicLemmas
public import Homogenization.Sobolev.Foundations.CoerciveH1
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ
public import Homogenization.Multiscale.NormalizedNorms
public import Homogenization.Geometry.CubeMetric

/-!
# Smooth density of `H¹` on a cube in the gradient `L̲²` norm

The paper defines `‖F‖_{Ĥ̲^{-1}(U)}` as a
supremum over *smooth* mean-zero test functions with `‖∇g‖_{L̲²(U)} ≤ 1`. To
realize that supremum at the gradient of an `H¹` solution one needs the smooth
functions to be dense in `H¹(openCubeSet Q)` for the gradient `L̲²` norm alone.
This file proves exactly that, on CoarseGraining's `H1Function` carrier and
against the normalized cube measure.

## The route

CoarseGraining's convex-approximation lane already smooths on a bounded open
convex domain with an interior closed ball, which is exactly the situation of
`openCubeSet Q` and the concentric ball of half the cube radius. Two of its
theorems combine:

* `Homogenization.HasWeakGradientOn.convexApproxSmoothRepresentative` transports
  the weak gradient: the globally smooth representative
  `convexApproxSmoothRepresentative` of `u` has weak gradient `(1 - t)` times the
  same smoothing applied to the weak gradient of `u`;
* `Homogenization.tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn`
  converges *values* in `L^p` for a merely `L^p` input.

The point is to apply the second theorem to the weak gradient `∇u` rather than
to `u`. The smoothed function is globally `C^∞`, so its classical gradient is a
weak gradient too, and weak gradients on an open set are almost everywhere
unique; hence the classical gradient of the smoothed function agrees almost
everywhere on the cube with `(1 - t)` times the smoothing of `∇u`. Writing

`(1 - t)·S_t(∇u) - ∇u = (1 - t)·(S_t(∇u) - ∇u) - t·∇u`

shows that the `(1 - t)` factor of the transport step costs only the second
term, which is `t` times a fixed finite `L²` norm and therefore vanishes with
`t`. There is no domain shrinkage to repair: `convexApproxSmoothRepresentative`
is defined on all of `Vec d` and agrees with the smoothing operator at every
point of the cube, and both convergence statements are already stated on the
whole of `volume.restrict (openCubeSet Q)`.

## Two normalizations

The statements below use the normalized cube measure
`Homogenization.normalizedCubeMeasure Q`, which is
`ENNReal.ofReal (cubeVolume Q)⁻¹` times `volume.restrict (cubeSet Q)`, and the
latter equals `volume.restrict (openCubeSet Q)`. So the passage between the
working measure and the statement measure is one positive finite scalar factor,
recorded in `eLpNorm_normalizedCubeMeasure_eq`.

The pointwise magnitude is the Euclidean one of the paper, carried by
`Homogenization.HilbertVec.ofVec`; the ambient `Vec d = Fin d → ℝ` has the
supremum norm instead. The elementary comparison used here is `|v| ≤ ∑ i |v i|`,
in the form `eLpNorm_ofVec_le_sum`.

## Main results

* `exists_cubeH1SmoothGradientApprox`: for every `u : H1Function (openCubeSet Q)`
  and every `ε > 0` there is a globally smooth `g : Vec d → ℝ` with
  `‖∇g - ∇u‖_{L̲²(Q)} < ε`.
* `exists_cubeH1MeanZeroSmoothGradientApprox`: the same with `cubeAverage Q g = 0`,
  obtained by subtracting a constant, which does not change the gradient.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Sobolev

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The concentric interior ball -/

private theorem half_cubeRadius_pos (Q : TriadicCube d) : 0 < cubeRadius Q / 2 :=
  half_pos (cubeRadius_pos Q)

private theorem closedBall_half_cubeRadius_subset (Q : TriadicCube d) :
    Metric.closedBall (cubeCenter Q) (cubeRadius Q / 2) ⊆ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.closedBall_subset_ball (half_lt_self (cubeRadius_pos Q))

/-! ## The smoothing scale -/

/-- The smoothing scales `1/(n+2)`, all strictly between `0` and `1`. -/
private def cubeSmoothingScale (n : ℕ) : ℝ := unitConvexApproxScale (n + 1)

private theorem cubeSmoothingScale_pos (n : ℕ) : 0 < cubeSmoothingScale n := by
  have h : (0 : ℝ) < ((n : ℝ) + 1) + 1 := by positivity
  simpa [cubeSmoothingScale, unitConvexApproxScale] using one_div_pos.2 h

private theorem cubeSmoothingScale_lt_one (n : ℕ) : cubeSmoothingScale n < 1 := by
  have h : (1 : ℝ) < ((n : ℝ) + 1) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hn]
  have h0 : (0 : ℝ) < ((n : ℝ) + 1) + 1 := by positivity
  simpa [cubeSmoothingScale, unitConvexApproxScale] using (div_lt_one h0).2 h

private theorem tendsto_cubeSmoothingScale_zero :
    Filter.Tendsto cubeSmoothingScale Filter.atTop (nhds 0) :=
  tendsto_unitConvexApproxScale_zero.comp (Filter.tendsto_add_atTop_nat 1)

/-! ## The smoothing family on a cube -/

/-- The globally smooth convex-approximation representative of `f` on the open
cube `openCubeSet Q`, at smoothing parameter `t`, built from CoarseGraining's
unit kernel and the concentric interior ball of half the cube radius. -/
private def cubeSmoothing (Q : TriadicCube d) (f : Vec d → ℝ) (t : ℝ) : Vec d → ℝ :=
  convexApproxSmoothRepresentative (openCubeSet Q) (unitConvexApproxKernel (d := d)) f
    (cubeCenter Q) (cubeRadius Q / 2) t

private theorem contDiff_cubeSmoothing {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeSmoothing Q f t) :=
  contDiff_convexApproxSmoothRepresentative (isOpen_openCubeSet Q).measurableSet
    (isConvexApproxKernel_unitConvexApproxKernel (d := d))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf (half_cubeRadius_pos Q) ht

private theorem continuous_cubeSmoothing {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) {t : ℝ} (ht : 0 < t) :
    Continuous (cubeSmoothing Q f t) :=
  (contDiff_cubeSmoothing hf ht).continuous

private theorem cubeSmoothing_apply_of_mem {Q : TriadicCube d} {f : Vec d → ℝ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeSmoothing Q f t x =
      convexApproxSmoothing (unitConvexApproxKernel (d := d)) f (cubeCenter Q)
        (cubeRadius Q / 2) t x :=
  convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hx
    (closedBall_half_cubeRadius_subset Q) (half_cubeRadius_pos Q) ht0 ht1

private theorem locallyIntegrableOn_of_memL2On {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) :
    LocallyIntegrableOn f (openCubeSet Q) volume := by
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact IntegrableOn.locallyIntegrableOn
    (hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

private theorem locallyIntegrableOn_of_continuous {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Continuous f) : LocallyIntegrableOn f U volume :=
  hf.locallyIntegrable.locallyIntegrableOn U

private theorem continuous_euclideanGradient_apply {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    Continuous (fun x : Vec d => euclideanGradient g x i) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  exact hfd.clm_apply continuous_const

/-- **The transport step.** The classical gradient of the smoothed function
agrees, almost everywhere on the cube, with `(1 - t)` times the smoothing of the
weak gradient of `u`: both are weak partial derivatives of the same function on
an open set, and both are continuous, hence locally integrable. -/
private theorem euclideanGradient_cubeSmoothing_ae_eq {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (i : Fin d) :
    (fun x => euclideanGradient (cubeSmoothing Q u.toFun t) x i)
      =ᵐ[volume.restrict (openCubeSet Q)]
        fun x => (1 - t) * cubeSmoothing Q (fun y => u.grad y i) t x := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (cubeSmoothing Q u.toFun t) :=
    contDiff_cubeSmoothing u.memL2 ht0
  have hclassical : HasWeakPartialDerivOn (openCubeSet Q) i (cubeSmoothing Q u.toFun t)
      (fun x => euclideanGradient (cubeSmoothing Q u.toFun t) x i) :=
    HasWeakGradientOn.of_contDiff
      (U := openCubeSet Q) (hsmooth.of_le (by simp)) i
  have htransport : HasWeakGradientOn (openCubeSet Q) (cubeSmoothing Q u.toFun t)
      (fun x j => (1 - t) * cubeSmoothing Q (fun y => u.grad y j) t x) :=
    HasWeakGradientOn.convexApproxSmoothRepresentative
      (isOpenBoundedConvexDomain_openCubeSet Q)
      (locallyIntegrableOn_of_memL2On u.memL2)
      (fun j => locallyIntegrableOn_of_memL2On (u.grad_memL2 j))
      u.hasWeakGradient (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (closedBall_half_cubeRadius_subset Q) (half_cubeRadius_pos Q) ht0 ht1
  exact HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
    (locallyIntegrableOn_of_continuous (continuous_euclideanGradient_apply hsmooth i))
    (locallyIntegrableOn_of_continuous
      (continuous_const.mul (continuous_cubeSmoothing (u.grad_memL2 i) ht0)))
    hclassical (htransport i)

/-! ## Two elementary reductions -/

/-- The Euclidean magnitude of a vector field is controlled in `L^p` by the sum
of the `L^p` norms of its coordinates. -/
private theorem eLpNorm_ofVec_le_sum {μ : Measure (Vec d)} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (H : Vec d → Vec d) (hH : ∀ i : Fin d, AEStronglyMeasurable (fun x => H x i) μ) :
    eLpNorm (fun x => HilbertVec.ofVec (H x)) p μ ≤
      ∑ i : Fin d, eLpNorm (fun x => H x i) p μ := by
  have hbasis : ∀ i : Fin d, ‖HilbertVec.ofVec (basisVec (d := d) i)‖ = 1 := by
    intro i
    have hsingle : HilbertVec.ofVec (basisVec (d := d) i)
        = EuclideanSpace.single i (1 : ℝ) := rfl
    rw [hsingle]
    simp
  have hdecomp : (fun x => HilbertVec.ofVec (H x))
      = ∑ i : Fin d, fun x => H x i • HilbertVec.ofVec (basisVec (d := d) i) := by
    funext x
    rw [Finset.sum_apply]
    refine PiLp.ext (fun j => ?_)
    simp [HilbertVec.ofVec, Finset.sum_apply]
  rw [hdecomp]
  refine le_trans (eLpNorm_sum_le hp)
    (Finset.sum_le_sum fun i _ => ?_)
  refine eLpNorm_mono_enorm ((hH i).smul_const _) (fun x => ?_)
  have hnorm : ‖H x i • HilbertVec.ofVec (basisVec (d := d) i)‖ = ‖H x i‖ := by
    rw [norm_smul, hbasis i, mul_one]
  rw [← ofReal_norm, ← ofReal_norm, hnorm]

/-- The normalized cube measure is one positive finite multiple of the volume
restricted to the open cube, so the two `L^p` norms differ by that factor. -/
private theorem eLpNorm_normalizedCubeMeasure_eq (Q : TriadicCube d) {E : Type*}
    [NormedAddCommGroup E] (f : Vec d → E) {p : ℝ≥0∞} (_hp : p ≠ ⊤) :
    eLpNorm f p (normalizedCubeMeasure Q)
      = ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / p).toReal *
        eLpNorm f p (volume.restrict (openCubeSet Q)) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos Q))).ne', smul_eq_mul]

/-! ## Convergence of the smoothed gradients -/

private theorem tendsto_eLpNorm_grad_component (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (i : Fin d) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm
        (fun x => euclideanGradient (cubeSmoothing Q u.toFun (cubeSmoothingScale n)) x i -
          u.grad x i) 2 (volume.restrict (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
  have hGmem : MemL2On (openCubeSet Q) (fun y => u.grad y i) := u.grad_memL2 i
  have hGmeas : AEStronglyMeasurable (fun y => u.grad y i)
      (volume.restrict (openCubeSet Q)) := hGmem.aestronglyMeasurable
  have hGtop : eLpNorm (fun y => u.grad y i) 2 (volume.restrict (openCubeSet Q)) ≠ ⊤ :=
    hGmem.eLpNorm_lt_top.ne
  have hvalue : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x =>
        convexApproxSmoothing (unitConvexApproxKernel (d := d)) (fun y => u.grad y i)
          (cubeCenter Q) (cubeRadius Q / 2) (cubeSmoothingScale n) x - u.grad x i) 2
        (volume.restrict (openCubeSet Q)))
      Filter.atTop (nhds 0) :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      (isOpenBoundedConvexDomain_openCubeSet Q)
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hGmem
      (closedBall_half_cubeRadius_subset Q) (half_cubeRadius_pos Q)
      tendsto_cubeSmoothingScale_zero
      (Filter.Eventually.of_forall cubeSmoothingScale_pos)
      (Filter.Eventually.of_forall cubeSmoothingScale_lt_one)
  have hrep : ∀ n : ℕ,
      eLpNorm (fun x => cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x -
          u.grad x i) 2 (volume.restrict (openCubeSet Q))
        = eLpNorm (fun x =>
            convexApproxSmoothing (unitConvexApproxKernel (d := d)) (fun y => u.grad y i)
              (cubeCenter Q) (cubeRadius Q / 2) (cubeSmoothingScale n) x - u.grad x i) 2
            (volume.restrict (openCubeSet Q)) := by
    intro n
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
    rw [cubeSmoothing_apply_of_mem (cubeSmoothingScale_pos n) (cubeSmoothingScale_lt_one n) hx]
  have hbound : ∀ n : ℕ,
      eLpNorm (fun x =>
          euclideanGradient (cubeSmoothing Q u.toFun (cubeSmoothingScale n)) x i -
            u.grad x i) 2 (volume.restrict (openCubeSet Q))
        ≤ eLpNorm (fun x =>
            cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i) 2
            (volume.restrict (openCubeSet Q))
          + ENNReal.ofReal (cubeSmoothingScale n) *
            eLpNorm (fun y => u.grad y i) 2 (volume.restrict (openCubeSet Q)) := by
    intro n
    have ht0 := cubeSmoothingScale_pos n
    have ht1 := cubeSmoothingScale_lt_one n
    have hmeas1 : AEStronglyMeasurable
        (fun x => (1 - cubeSmoothingScale n) *
          (cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i))
        (volume.restrict (openCubeSet Q)) :=
      (aestronglyMeasurable_const.mul
        ((continuous_cubeSmoothing (u.grad_memL2 i) ht0).aestronglyMeasurable.sub hGmeas))
    have hmeas2 : AEStronglyMeasurable
        (fun x => -cubeSmoothingScale n * u.grad x i)
        (volume.restrict (openCubeSet Q)) := aestronglyMeasurable_const.mul hGmeas
    have hae : (fun x =>
        euclideanGradient (cubeSmoothing Q u.toFun (cubeSmoothingScale n)) x i - u.grad x i)
        =ᵐ[volume.restrict (openCubeSet Q)] fun x =>
          (1 - cubeSmoothingScale n) *
              (cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i)
            + -cubeSmoothingScale n * u.grad x i := by
      filter_upwards [euclideanGradient_cubeSmoothing_ae_eq u ht0 ht1 i] with x hx
      rw [hx]
      ring
    rw [eLpNorm_congr_ae hae]
    have hadd := eLpNorm_add_le (p := (2 : ℝ≥0∞))
      (μ := volume.restrict (openCubeSet Q))
      (f := fun x => (1 - cubeSmoothingScale n) *
        (cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i))
      (g := fun x => -cubeSmoothingScale n * u.grad x i)
      (by norm_num)
    have hsmul1 : eLpNorm (fun x => (1 - cubeSmoothingScale n) *
          (cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i)) 2
          (volume.restrict (openCubeSet Q))
        ≤ ‖1 - cubeSmoothingScale n‖ₑ *
          eLpNorm (fun x =>
            cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i) 2
            (volume.restrict (openCubeSet Q)) := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        (eLpNorm_const_smul_le (p := (2 : ℝ≥0∞)) (μ := volume.restrict (openCubeSet Q))
          (c := 1 - cubeSmoothingScale n)
          (f := fun x => cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x -
            u.grad x i))
    have hsmul2 : eLpNorm (fun x => -cubeSmoothingScale n * u.grad x i) 2
          (volume.restrict (openCubeSet Q))
        ≤ ‖-cubeSmoothingScale n‖ₑ *
          eLpNorm (fun y => u.grad y i) 2 (volume.restrict (openCubeSet Q)) := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        (eLpNorm_const_smul_le (p := (2 : ℝ≥0∞)) (μ := volume.restrict (openCubeSet Q))
          (c := -cubeSmoothingScale n) (f := fun y => u.grad y i))
    have hcoef1 : ‖1 - cubeSmoothingScale n‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by linarith only [ht1] : (0:ℝ) ≤ 1 - cubeSmoothingScale n)]
      simpa using ENNReal.ofReal_le_ofReal (by linarith only [ht0] : 1 - cubeSmoothingScale n ≤ 1)
    have hcoef2 : ‖-cubeSmoothingScale n‖ₑ = ENNReal.ofReal (cubeSmoothingScale n) := by
      rw [Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg ht0.le]
    calc eLpNorm (fun x =>
            (1 - cubeSmoothingScale n) *
                (cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i)
              + -cubeSmoothingScale n * u.grad x i) 2 (volume.restrict (openCubeSet Q))
        ≤ eLpNorm (fun x => (1 - cubeSmoothingScale n) *
              (cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i)) 2
              (volume.restrict (openCubeSet Q))
            + eLpNorm (fun x => -cubeSmoothingScale n * u.grad x i) 2
              (volume.restrict (openCubeSet Q)) := by
          simpa only [Pi.add_def] using hadd
      _ ≤ ‖1 - cubeSmoothingScale n‖ₑ *
              eLpNorm (fun x =>
                cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i) 2
                (volume.restrict (openCubeSet Q))
            + ‖-cubeSmoothingScale n‖ₑ *
              eLpNorm (fun y => u.grad y i) 2 (volume.restrict (openCubeSet Q)) :=
          add_le_add hsmul1 hsmul2
      _ ≤ 1 * eLpNorm (fun x =>
                cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i) 2
                (volume.restrict (openCubeSet Q))
            + ENNReal.ofReal (cubeSmoothingScale n) *
              eLpNorm (fun y => u.grad y i) 2 (volume.restrict (openCubeSet Q)) := by
          rw [hcoef2]
          exact add_le_add (mul_le_mul_left hcoef1 _) le_rfl
      _ = eLpNorm (fun x =>
              cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i) 2
              (volume.restrict (openCubeSet Q))
            + ENNReal.ofReal (cubeSmoothingScale n) *
              eLpNorm (fun y => u.grad y i) 2 (volume.restrict (openCubeSet Q)) := by
          rw [one_mul]
  have hfirst : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x =>
        cubeSmoothing Q (fun y => u.grad y i) (cubeSmoothingScale n) x - u.grad x i) 2
        (volume.restrict (openCubeSet Q))) Filter.atTop (nhds 0) := by
    simpa only [hrep] using hvalue
  have hsecond : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (cubeSmoothingScale n) *
        eLpNorm (fun y => u.grad y i) 2 (volume.restrict (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
    have hofReal : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (cubeSmoothingScale n))
        Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_cubeSmoothingScale_zero
    simpa using ENNReal.Tendsto.mul_const hofReal (Or.inr hGtop)
  have hupper := hfirst.add hsecond
  rw [add_zero] at hupper
  exact ENNReal.tendsto_nhds_zero.2 fun η hη =>
    (ENNReal.tendsto_nhds_zero.1 hupper η hη).mono fun n hn => le_trans (hbound n) hn

private theorem tendsto_eLpNorm_ofVec_grad (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x => HilbertVec.ofVec
        (euclideanGradient (cubeSmoothing Q u.toFun (cubeSmoothingScale n)) x - u.grad x)) 2
        (normalizedCubeMeasure Q)) Filter.atTop (nhds 0) := by
  have hK : ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top).ne
  have hs : Filter.Tendsto
      (fun n : ℕ => ∑ i : Fin d, eLpNorm (fun x =>
        euclideanGradient (cubeSmoothing Q u.toFun (cubeSmoothingScale n)) x i - u.grad x i) 2
        (volume.restrict (openCubeSet Q))) Filter.atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      (fun i (_ : i ∈ Finset.univ) => tendsto_eLpNorm_grad_component Q u i)
    simpa using h
  have hsum : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal *
        ∑ i : Fin d, eLpNorm (fun x =>
          euclideanGradient (cubeSmoothing Q u.toFun (cubeSmoothingScale n)) x i - u.grad x i)
          2 (volume.restrict (openCubeSet Q))) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hs (Or.inr hK)
  refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
  refine (ENNReal.tendsto_nhds_zero.1 hsum η hη).mono fun n hn => le_trans ?_ hn
  rw [eLpNorm_normalizedCubeMeasure_eq Q _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  refine mul_le_mul_right (eLpNorm_ofVec_le_sum (by norm_num) _ fun i => ?_) _
  exact ((continuous_euclideanGradient_apply
      (contDiff_cubeSmoothing u.memL2 (cubeSmoothingScale_pos n)) i).aestronglyMeasurable).sub
    (u.grad_memL2 i).aestronglyMeasurable

/-! ## The density theorems -/

/-- Subtracting its own cube average makes a continuous function mean zero on the
cube. -/
private theorem cubeAverage_sub_self_eq_zero (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : Continuous g) : cubeAverage Q (fun x => g x - cubeAverage Q g) = 0 := by
  have hint : IntegrableOn g (cubeSet Q) volume :=
    (hg.continuousOn.integrableOn_compact
      ((isBounded_cubeSet Q).isCompact_closure)).mono_set subset_closure
  have hconst : IntegrableOn (fun _ : Vec d => cubeAverage Q g) (cubeSet Q) volume :=
    integrableOn_const (volume_cubeSet_lt_top Q).ne (by simp)
  have hvol : (volume : Measure (Vec d)).real (cubeSet Q) = cubeVolume Q := by
    rw [Measure.real_def, volume_cubeSet_toReal]
  have hne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  rw [cubeAverage, integral_sub hint hconst, setIntegral_const, hvol, smul_eq_mul,
    cubeAverage, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, sub_self, mul_zero]

/-- **Smooth density of `H¹` on a cube in the gradient `L̲²` norm.** For every
`H¹` function on the interior of a triadic cube and every `ε > 0` there is a
globally smooth function on `Vec d` whose Euclidean gradient is within `ε` of the
weak gradient of `u` in the normalized `L̲²(Q)` norm. -/
theorem exists_cubeH1SmoothGradientApprox (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      eLpNorm (fun x => HilbertVec.ofVec (euclideanGradient g x - u.grad x)) 2
        (normalizedCubeMeasure Q) < ε := by
  obtain ⟨n, hn⟩ :=
    ((tendsto_order.1 (tendsto_eLpNorm_ofVec_grad Q u)).2 ε hε).exists
  exact ⟨cubeSmoothing Q u.toFun (cubeSmoothingScale n),
    contDiff_cubeSmoothing u.memL2 (cubeSmoothingScale_pos n), hn⟩

/-- **The mean-zero variant.** Subtracting the cube average of the approximant
leaves its gradient unchanged, so the same approximation can be realized inside
the mean-zero class of the paper. -/
theorem exists_cubeH1MeanZeroSmoothGradientApprox (Q : TriadicCube d)
    (u : H1MeanZeroFunction (openCubeSet Q)) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ cubeAverage Q g = 0 ∧
      eLpNorm (fun x => HilbertVec.ofVec (euclideanGradient g x - u.toH1Function.grad x)) 2
        (normalizedCubeMeasure Q) < ε := by
  obtain ⟨g, hgsmooth, hgclose⟩ :=
    exists_cubeH1SmoothGradientApprox Q u.toH1Function ε hε
  refine ⟨fun x => g x - cubeAverage Q g, hgsmooth.sub contDiff_const,
    cubeAverage_sub_self_eq_zero Q hgsmooth.continuous, ?_⟩
  · have hgrad : euclideanGradient (fun x => g x - cubeAverage Q g) = euclideanGradient g := by
      funext x
      funext i
      simp [euclideanGradient, euclideanCoordDeriv, fderiv_sub_const]
    rw [hgrad]
    exact hgclose

end

end Sobolev
end SuperdiffusionCLT
