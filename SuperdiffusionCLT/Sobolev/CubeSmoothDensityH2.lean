/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
public import Homogenization.Sobolev.H1.BasicLemmas
public import Homogenization.Sobolev.Foundations.WeakHessianEuclidean
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ
public import Homogenization.Multiscale.NormalizedNorms
public import Homogenization.Geometry.CubeMetric

/-!
# The second-order transport of the convex-approximation smoothing on a cube

`Sobolev/CubeSmoothDensity.lean` smooths an `H¹` function on the interior of a
triadic cube and transports its weak gradient through the smoothing: for the
globally smooth representative `S_t u` one has, almost everywhere on the cube,
`∂_i(S_t u) = (1 - t) S_t(∂_i u)`. This module runs the same argument one
derivative higher, which is what the `H²` smooth-density hypothesis of
`Section2/Norms/FractionalDensityB.lean` needs.

## The route

Two facts do all the work, both already in the pinned `CoarseGraining` lane:

* `Homogenization.HasWeakPartialDerivOn.convexApproxSmoothRepresentative`
  transports one weak partial derivative through the smoothing: if `g` is the
  weak `j`-th derivative of `f` on the open convex domain, then
  `(1 - t) S_t g` is the weak `j`-th derivative of `S_t f`;
* `Homogenization.tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn`
  converges the smoothing of an `L²` datum in `L²` of the domain.

The transport statement is upgraded here from "almost everywhere" to
"everywhere on the open cube". Both sides are continuous — the smoothed
functions are globally `C^∞` — and two continuous functions that agree almost
everywhere on an open set agree at every point of it, because a nonempty open
subset of `Vec d` has positive Lebesgue measure. That upgrade is what makes a
*second* differentiation legitimate: differentiation is not an almost-everywhere
operation, so the order-one identity has to hold on a neighbourhood of each
point before it may be differentiated again.

With the pointwise identity in hand the second derivative is immediate. On the
open cube,

`∂_i(S_t w) = (1 - t) S_t(∂_i w)`,

and the right-hand side is a constant multiple of the smoothing of the datum
`∂_i w`, whose weak `j`-th derivative is the Hessian coordinate `H_{ij}`; one
more application of the same transport gives, again everywhere on the open cube,

`∂_j∂_i(S_t w) = (1 - t)² S_t(H_{ij})`.

## Convergence

`cubeH2SmoothingScale n = 1/(n + 2)` is the scale sequence. Both transported
identities carry a power of `1 - t` in front of the smoothing, so the
convergence statement needed is that `c_n S_{t_n} f - f` vanishes in `L²(Q)`
whenever `|c_n| ≤ 1` and `c_n → 1`; splitting
`c_n S f - f = c_n (S f - f) + (c_n - 1) f` reduces this to the upstream
convergence and to `|c_n - 1| ‖f‖_{L²} → 0`. Both `c_n = 1 - t_n` and
`c_n = (1 - t_n)²` qualify.

## Main definitions

* `cubeH2Smoothing`: the globally smooth convex-approximation representative on
  the interior of a triadic cube, at a given smoothing parameter.
* `cubeH2SmoothingScale`: the scale sequence `1/(n + 2)`.

## Main results

* `eqOn_euclideanGradient_cubeH2Smoothing`: the order-one transport, everywhere
  on the open cube.
* `eqOn_euclideanGradient_euclideanGradient_cubeH2Smoothing`: the order-two
  transport `∂_j∂_i(S_t w) = (1 - t)² S_t(H_{ij})`, everywhere on the open cube.
* `tendsto_eLpNorm_smul_cubeH2Smoothing_sub`: the `L²(Q)` convergence of
  `c_n S_{t_n} f` to `f`.
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

private theorem half_cubeRadius_pos' (Q : TriadicCube d) : 0 < cubeRadius Q / 2 :=
  half_pos (cubeRadius_pos Q)

private theorem closedBall_half_cubeRadius_subset' (Q : TriadicCube d) :
    Metric.closedBall (cubeCenter Q) (cubeRadius Q / 2) ⊆ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.closedBall_subset_ball (half_lt_self (cubeRadius_pos Q))

/-! ## The smoothing scale -/

/-- The smoothing scales `1/(n + 2)`, all strictly between `0` and `1`. -/
def cubeH2SmoothingScale (n : ℕ) : ℝ := unitConvexApproxScale (n + 1)

theorem cubeH2SmoothingScale_pos (n : ℕ) : 0 < cubeH2SmoothingScale n := by
  have h : (0 : ℝ) < ((n : ℝ) + 1) + 1 := by positivity
  simpa [cubeH2SmoothingScale, unitConvexApproxScale] using one_div_pos.2 h

theorem cubeH2SmoothingScale_lt_one (n : ℕ) : cubeH2SmoothingScale n < 1 := by
  have h : (1 : ℝ) < ((n : ℝ) + 1) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hn]
  have h0 : (0 : ℝ) < ((n : ℝ) + 1) + 1 := by positivity
  simpa [cubeH2SmoothingScale, unitConvexApproxScale] using (div_lt_one h0).2 h

theorem tendsto_cubeH2SmoothingScale_zero :
    Filter.Tendsto cubeH2SmoothingScale Filter.atTop (nhds 0) :=
  tendsto_unitConvexApproxScale_zero.comp (Filter.tendsto_add_atTop_nat 1)

/-! ## The smoothing family on a cube -/

/-- The globally smooth convex-approximation representative of `f` on the open
cube `openCubeSet Q`, at smoothing parameter `t`, built from CoarseGraining's
unit kernel and the concentric interior ball of half the cube radius. -/
def cubeH2Smoothing (Q : TriadicCube d) (f : Vec d → ℝ) (t : ℝ) : Vec d → ℝ :=
  convexApproxSmoothRepresentative (openCubeSet Q) (unitConvexApproxKernel (d := d)) f
    (cubeCenter Q) (cubeRadius Q / 2) t

theorem contDiff_cubeH2Smoothing {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeH2Smoothing Q f t) :=
  contDiff_convexApproxSmoothRepresentative (isOpen_openCubeSet Q).measurableSet
    (isConvexApproxKernel_unitConvexApproxKernel (d := d))
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf (half_cubeRadius_pos' Q) ht

theorem continuous_cubeH2Smoothing {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) {t : ℝ} (ht : 0 < t) :
    Continuous (cubeH2Smoothing Q f t) :=
  (contDiff_cubeH2Smoothing hf ht).continuous

theorem cubeH2Smoothing_apply_of_mem {Q : TriadicCube d} {f : Vec d → ℝ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeH2Smoothing Q f t x =
      convexApproxSmoothing (unitConvexApproxKernel (d := d)) f (cubeCenter Q)
        (cubeRadius Q / 2) t x :=
  convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hx
    (closedBall_half_cubeRadius_subset' Q) (half_cubeRadius_pos' Q) ht0 ht1

/-! ## Two local integrability reductions -/

private theorem locallyIntegrableOn_of_memL2On' {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) :
    LocallyIntegrableOn f (openCubeSet Q) volume := by
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  exact IntegrableOn.locallyIntegrableOn
    (hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))

private theorem locallyIntegrableOn_of_continuous' {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : Continuous f) : LocallyIntegrableOn f U volume :=
  hf.locallyIntegrable.locallyIntegrableOn U

private theorem continuous_euclideanGradient_apply' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    Continuous (fun x : Vec d => euclideanGradient g x i) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  exact hfd.clm_apply continuous_const

/-! ## From almost everywhere to everywhere on an open set -/

/-- Two continuous functions that agree almost everywhere on an open subset of
`Vec d` agree at every point of it: the set where they differ is open, and a
nonempty open set has positive Lebesgue measure. -/
theorem eqOn_of_continuous_of_ae_eq_restrict {U : Set (Vec d)} (hU : IsOpen U)
    {f g : Vec d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[volume.restrict U] g) : Set.EqOn f g U := by
  intro x hx
  by_contra hne
  have hopen : IsOpen ({y : Vec d | f y ≠ g y} ∩ U) :=
    (isOpen_ne_fun hf hg).inter hU
  have hzero : volume ({y : Vec d | f y ≠ g y} ∩ U) = 0 := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet] at h
    refine measure_mono_null ?_ h
    intro y hy hmem
    exact hy.1 (hmem hy.2)
  exact Set.eq_empty_iff_forall_notMem.1
    ((hopen.measure_eq_zero_iff volume).1 hzero) x ⟨hne, hx⟩

/-! ## The transport step, everywhere on the open cube -/

/-- **The transport step.** If `g` is a weak `j`-th derivative of `f` on the
open cube, then at every point of the open cube the classical `j`-th derivative
of the smoothed `f` equals `(1 - t)` times the smoothed `g`. Both sides are
continuous, both are weak `j`-th derivatives of `cubeH2Smoothing Q f t` on the
open cube, and weak derivatives on an open set are almost everywhere unique. -/
theorem eqOn_euclideanCoordDeriv_cubeH2Smoothing {Q : TriadicCube d}
    {f g : Vec d → ℝ} {j : Fin d} (hf : MemL2On (openCubeSet Q) f)
    (hg : MemL2On (openCubeSet Q) g)
    (hweak : HasWeakPartialDerivOn (openCubeSet Q) j f g)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Set.EqOn (fun x => euclideanGradient (cubeH2Smoothing Q f t) x j)
      (fun x => (1 - t) * cubeH2Smoothing Q g t x) (openCubeSet Q) := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (cubeH2Smoothing Q f t) :=
    contDiff_cubeH2Smoothing hf ht0
  have hclassical : HasWeakPartialDerivOn (openCubeSet Q) j (cubeH2Smoothing Q f t)
      (fun x => euclideanGradient (cubeH2Smoothing Q f t) x j) :=
    HasWeakGradientOn.of_contDiff
      (U := openCubeSet Q) (hsmooth.of_le (by simp)) j
  have htransport : HasWeakPartialDerivOn (openCubeSet Q) j (cubeH2Smoothing Q f t)
      (fun x => (1 - t) * cubeH2Smoothing Q g t x) :=
    HasWeakPartialDerivOn.convexApproxSmoothRepresentative
      (isOpenBoundedConvexDomain_openCubeSet Q)
      (locallyIntegrableOn_of_memL2On' hf) (locallyIntegrableOn_of_memL2On' hg)
      hweak (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (closedBall_half_cubeRadius_subset' Q) (half_cubeRadius_pos' Q) ht0 ht1
  refine eqOn_of_continuous_of_ae_eq_restrict (isOpen_openCubeSet Q)
    (continuous_euclideanGradient_apply' hsmooth j)
    (continuous_const.mul (continuous_cubeH2Smoothing hg ht0)) ?_
  exact HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
    (locallyIntegrableOn_of_continuous'
      (continuous_euclideanGradient_apply' hsmooth j))
    (locallyIntegrableOn_of_continuous'
      (continuous_const.mul (continuous_cubeH2Smoothing hg ht0)))
    hclassical htransport

/-- **The order-one transport for an `H¹` function**, everywhere on the open
cube: `∂_i(S_t w) = (1 - t) S_t(∂_i w)`. -/
theorem eqOn_euclideanGradient_cubeH2Smoothing {Q : TriadicCube d}
    (w : H1Function (openCubeSet Q)) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (i : Fin d) :
    Set.EqOn (fun x => euclideanGradient (cubeH2Smoothing Q w.toFun t) x i)
      (fun x => (1 - t) * cubeH2Smoothing Q (fun y => w.grad y i) t x)
      (openCubeSet Q) :=
  eqOn_euclideanCoordDeriv_cubeH2Smoothing w.memL2 (w.grad_memL2 i)
    (w.hasWeakGradient i) ht0 ht1

/-- **The order-two transport**, everywhere on the open cube:
`∂_j∂_i(S_t w) = (1 - t)² S_t(H_{ij})` for a weak Hessian witness `H` of `w`.

The order-one identity holds at every point of the open cube, hence on a
neighbourhood of each of its points, so it may be differentiated once more; the
derivative of the right-hand side is `(1 - t)` times the transport of the weak
`j`-th derivative of `∂_i w`, which is the Hessian coordinate `H_{ij}`. -/
theorem eqOn_euclideanGradient_euclideanGradient_cubeH2Smoothing
    {Q : TriadicCube d} {w : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) w) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (i j : Fin d) :
    Set.EqOn
      (fun x => euclideanGradient
        (fun y => euclideanGradient (cubeH2Smoothing Q w.toFun t) y i) x j)
      (fun x => (1 - t) ^ 2 * cubeH2Smoothing Q (H.hess i j) t x)
      (openCubeSet Q) := by
  have hgradsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (cubeH2Smoothing Q (fun y => w.grad y i) t) :=
    contDiff_cubeH2Smoothing (w.grad_memL2 i) ht0
  have hsecond := eqOn_euclideanCoordDeriv_cubeH2Smoothing (Q := Q)
    (f := fun y => w.grad y i) (g := H.hess i j) (j := j) (w.grad_memL2 i)
    (H.hess_memL2 i j) (H.weak_second i j) ht0 ht1
  intro x hx
  have hev : (fun y => euclideanGradient (cubeH2Smoothing Q w.toFun t) y i)
      =ᶠ[nhds x]
        fun y => (1 - t) * cubeH2Smoothing Q (fun z => w.grad z i) t y :=
    Filter.eventuallyEq_of_mem ((isOpen_openCubeSet Q).mem_nhds hx)
      (eqOn_euclideanGradient_cubeH2Smoothing w ht0 ht1 i)
  have hdiff : DifferentiableAt ℝ
      (cubeH2Smoothing Q (fun y => w.grad y i) t) x :=
    (hgradsmooth.differentiable (by simp)).differentiableAt
  have hfd : fderiv ℝ
        (fun y => euclideanGradient (cubeH2Smoothing Q w.toFun t) y i) x
      = fderiv ℝ
        (fun y => (1 - t) * cubeH2Smoothing Q (fun z => w.grad z i) t y) x :=
    hev.fderiv_eq
  show fderiv ℝ
      (fun y => euclideanGradient (cubeH2Smoothing Q w.toFun t) y i) x
      (basisVec j) = _
  rw [hfd, fderiv_const_mul hdiff]
  show (1 - t) * fderiv ℝ (cubeH2Smoothing Q (fun y => w.grad y i) t) x
      (basisVec j) = _
  have hval : euclideanGradient (cubeH2Smoothing Q (fun y => w.grad y i) t) x j
      = (1 - t) * cubeH2Smoothing Q (H.hess i j) t x := hsecond hx
  rw [show fderiv ℝ (cubeH2Smoothing Q (fun y => w.grad y i) t) x (basisVec j)
      = euclideanGradient (cubeH2Smoothing Q (fun y => w.grad y i) t) x j from rfl,
    hval]
  ring

/-! ## `L²` convergence of the smoothing -/

/-- The smoothing of an `L²(Q)` datum converges to it in `L²` of the open
cube. This is CoarseGraining's convergence for the smoothing *operator*,
transferred to the smooth global representative, which agrees with it at every
point of the open cube. -/
theorem tendsto_eLpNorm_cubeH2Smoothing_sub (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemL2On (openCubeSet Q) f) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm
        (fun x => cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
        (volume.restrict (openCubeSet Q))) Filter.atTop (nhds 0) := by
  have hvalue : Filter.Tendsto
      (fun n : ℕ => eLpNorm (fun x =>
        convexApproxSmoothing (unitConvexApproxKernel (d := d)) f
          (cubeCenter Q) (cubeRadius Q / 2) (cubeH2SmoothingScale n) x - f x) 2
        (volume.restrict (openCubeSet Q))) Filter.atTop (nhds 0) :=
    tendsto_eLpNorm_sub_zero_convexApproxSmoothing_of_memLpOn
      (isOpenBoundedConvexDomain_openCubeSet Q)
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hf
      (closedBall_half_cubeRadius_subset' Q) (half_cubeRadius_pos' Q)
      tendsto_cubeH2SmoothingScale_zero
      (Filter.Eventually.of_forall cubeH2SmoothingScale_pos)
      (Filter.Eventually.of_forall cubeH2SmoothingScale_lt_one)
  have hrep : ∀ n : ℕ,
      eLpNorm (fun x => cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
          (volume.restrict (openCubeSet Q))
        = eLpNorm (fun x =>
            convexApproxSmoothing (unitConvexApproxKernel (d := d)) f
              (cubeCenter Q) (cubeRadius Q / 2) (cubeH2SmoothingScale n) x - f x)
            2 (volume.restrict (openCubeSet Q)) := by
    intro n
    refine eLpNorm_congr_ae ?_
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
    rw [cubeH2Smoothing_apply_of_mem (cubeH2SmoothingScale_pos n)
      (cubeH2SmoothingScale_lt_one n) hx]
  simpa only [hrep] using hvalue

/-- **The weighted convergence.** Both transported identities carry a power of
`1 - t` in front of the smoothing, so what is needed is the convergence of
`c_n S_{t_n} f` to `f` in `L²(Q)` for a coefficient sequence with `|c_n| ≤ 1`
and `c_n → 1`. Splitting `c_n S f - f = c_n (S f - f) + (c_n - 1) f` reduces it
to `tendsto_eLpNorm_cubeH2Smoothing_sub` and to `|c_n - 1| ‖f‖_{L²(Q)} → 0`. -/
theorem tendsto_eLpNorm_smul_cubeH2Smoothing_sub (Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : MemL2On (openCubeSet Q) f) {c : ℕ → ℝ}
    (hc : Filter.Tendsto c Filter.atTop (nhds 1)) (hcb : ∀ n : ℕ, |c n| ≤ 1) :
    Filter.Tendsto
      (fun n : ℕ => eLpNorm
        (fun x => c n * cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
        (volume.restrict (openCubeSet Q))) Filter.atTop (nhds 0) := by
  have hfmeas : AEStronglyMeasurable f (volume.restrict (openCubeSet Q)) :=
    hf.aestronglyMeasurable
  have hftop : eLpNorm f 2 (volume.restrict (openCubeSet Q)) ≠ ⊤ :=
    hf.eLpNorm_lt_top.ne
  have hbound : ∀ n : ℕ,
      eLpNorm (fun x =>
          c n * cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
          (volume.restrict (openCubeSet Q))
        ≤ eLpNorm (fun x =>
              cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
              (volume.restrict (openCubeSet Q))
            + ENNReal.ofReal |c n - 1| *
              eLpNorm f 2 (volume.restrict (openCubeSet Q)) := by
    intro n
    have hsm : Continuous (cubeH2Smoothing Q f (cubeH2SmoothingScale n)) :=
      continuous_cubeH2Smoothing hf (cubeH2SmoothingScale_pos n)
    have hmeas1 : AEStronglyMeasurable
        (fun x => c n * (cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x))
        (volume.restrict (openCubeSet Q)) :=
      aestronglyMeasurable_const.mul (hsm.aestronglyMeasurable.sub hfmeas)
    have hmeas2 : AEStronglyMeasurable (fun x => (c n - 1) * f x)
        (volume.restrict (openCubeSet Q)) :=
      aestronglyMeasurable_const.mul hfmeas
    have hsplit : (fun x =>
        c n * cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x)
        = fun x => c n * (cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x)
            + (c n - 1) * f x := by
      funext x
      ring
    rw [hsplit]
    have hadd := eLpNorm_add_le (p := (2 : ℝ≥0∞))
      (μ := volume.restrict (openCubeSet Q))
      (f := fun x => c n * (cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x))
      (g := fun x => (c n - 1) * f x) (by norm_num)
    have hsmul1 : eLpNorm
          (fun x => c n * (cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x))
          2 (volume.restrict (openCubeSet Q))
        ≤ ‖c n‖ₑ * eLpNorm
            (fun x => cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
            (volume.restrict (openCubeSet Q)) := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        (eLpNorm_const_smul_le (p := (2 : ℝ≥0∞))
          (μ := volume.restrict (openCubeSet Q)) (c := c n)
          (f := fun x =>
            cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x))
    have hsmul2 : eLpNorm (fun x => (c n - 1) * f x) 2
          (volume.restrict (openCubeSet Q))
        ≤ ‖c n - 1‖ₑ * eLpNorm f 2 (volume.restrict (openCubeSet Q)) := by
      simpa only [Pi.smul_def, smul_eq_mul] using
        (eLpNorm_const_smul_le (p := (2 : ℝ≥0∞))
          (μ := volume.restrict (openCubeSet Q)) (c := c n - 1) (f := f))
    have hcoef1 : ‖c n‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      simpa using ENNReal.ofReal_le_ofReal (hcb n)
    have hcoef2 : ‖c n - 1‖ₑ = ENNReal.ofReal |c n - 1| := by
      rw [Real.enorm_eq_ofReal_abs]
    calc eLpNorm (fun x =>
            c n * (cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x)
              + (c n - 1) * f x) 2 (volume.restrict (openCubeSet Q))
        ≤ eLpNorm (fun x =>
              c n * (cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x)) 2
              (volume.restrict (openCubeSet Q))
            + eLpNorm (fun x => (c n - 1) * f x) 2
              (volume.restrict (openCubeSet Q)) := by
          simpa only [Pi.add_def] using hadd
      _ ≤ ‖c n‖ₑ * eLpNorm (fun x =>
              cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
              (volume.restrict (openCubeSet Q))
            + ‖c n - 1‖ₑ * eLpNorm f 2 (volume.restrict (openCubeSet Q)) :=
          add_le_add hsmul1 hsmul2
      _ ≤ 1 * eLpNorm (fun x =>
              cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
              (volume.restrict (openCubeSet Q))
            + ENNReal.ofReal |c n - 1| *
              eLpNorm f 2 (volume.restrict (openCubeSet Q)) := by
          rw [hcoef2]
          exact add_le_add (mul_le_mul_left hcoef1 _) le_rfl
      _ = eLpNorm (fun x =>
              cubeH2Smoothing Q f (cubeH2SmoothingScale n) x - f x) 2
              (volume.restrict (openCubeSet Q))
            + ENNReal.ofReal |c n - 1| *
              eLpNorm f 2 (volume.restrict (openCubeSet Q)) := by
          rw [one_mul]
  have hsecond : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal |c n - 1| *
        eLpNorm f 2 (volume.restrict (openCubeSet Q)))
      Filter.atTop (nhds 0) := by
    have habs : Filter.Tendsto (fun n : ℕ => |c n - 1|) Filter.atTop (nhds 0) := by
      have h := (hc.sub_const 1).abs
      simpa using h
    have hofReal : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal |c n - 1|)
        Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal habs
    simpa using ENNReal.Tendsto.mul_const hofReal (Or.inr hftop)
  have hupper := (tendsto_eLpNorm_cubeH2Smoothing_sub Q hf).add hsecond
  rw [add_zero] at hupper
  exact ENNReal.tendsto_nhds_zero.2 fun η hη =>
    (ENNReal.tendsto_nhds_zero.1 hupper η hη).mono fun n hn =>
      le_trans (hbound n) hn

end

end Sobolev
end SuperdiffusionCLT
