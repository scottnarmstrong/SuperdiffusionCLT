/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.EllsepTesting
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
public import Homogenization.Sobolev.H1.Algebra.H1Function
public import Homogenization.Sobolev.Truncation.WeakGradientLimit
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-!
# The weak product rule behind the drift datum of `e.ellsep.testing`

The integration by parts that leads to `e.ellsep.testing` asserts

`∇·((k_{L'} − k_ℓ)∇u_m) = (f_{L'} − f_ℓ)·∇u_m`,

i.e. that the divergence of the skew flux loses the Hessian contraction.  The
module docstring of `EllsepEquation.lean` records the two inputs
that assertion needs: a *weak product
rule* for `K·V` with `K` of class `C¹` and `V ∈ H¹`, and a weak Hessian for the
maximizer.  This file supplies the first, in the generality in which it is
true, together with the Schwarz symmetry of a weak Hessian, and assembles the
weak Jacobian of `x ↦ K x ∇u x` from them.

## Why a new proof is needed

`Homogenization.HasWeakPartialDerivOn` tests against *smooth* compactly
supported functions.  The upstream product rules
`Homogenization.H1Function.mulContDiffMemLpTop` and
`mulContDiffHasCompactSupport` therefore require the multiplier to be
`ContDiff ℝ ⊤`: their proofs test the weak derivative of the `H¹` factor
against `ψ φ`, which is smooth only when `φ` is.  The stream matrix of
`StreamCutoffAPI.lean` is a finite sum of shells of the shell field,
which stores one value and two derivatives: it is `C²`, never `C^∞`, so no upstream
product rule applies to it.

## The route

The convex-domain smoothing lane of CoarseGraining converges *uniformly on the
domain* for continuous data
(`Homogenization.eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous`)
and, for `C¹` data, so does its coordinate derivative
(`..._fderiv_..._of_contDiff`).  Its globally smooth representative
`convexApproxSmoothRepresentative` agrees with the smoothing at every point of
the domain, hence has the same derivative there.  So a `C¹` factor `g` is the
uniform limit on the cube, together with its gradient, of globally smooth
functions `cubeSmoothSeq Q g n`.  The upstream smooth product rule applies to
each of them; uniform convergence on a bounded set is `L²` convergence, and
`Homogenization.HasWeakPartialDerivOn.of_tendsto_eLpNorm_two` passes to the
limit.

## Main results

* `hasWeakGradientOn_mul_of_contDiff_one` — **the weak product rule**:
  `∇(g v) = g ∇v + v ∇g` weakly on an open cube, for `g` of class `C¹` and
  `v ∈ H¹`.
* `hess_ae_eq_swap` — **Schwarz symmetry of a weak Hessian**: `∂_j∂_i u` and
  `∂_i∂_j u` agree almost everywhere, both being read off `∂_i∂_j` of the test
  function.
* `hasWeakJacobianOn_matVecMul_of_contDiff_one` — the weak Jacobian of
  `x ↦ K x ∇u x` for a `C¹` matrix field `K` and an `H¹` function `u` with a
  weak Hessian, in the shape `Sobolev/DirichletW2pDivergence.lean` consumes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L^p` data from continuity on a cube -/

/-- A continuous scalar field lies in every `L^p` of an open triadic cube: the
cube sits in a compact ball on which the field is bounded, and the cube has
finite measure.  This is the `L^p` form of
`Section3/Terms/EllsepEquation.memL2On_openCubeSet_of_continuous`, needed at
`p = ⊤` for the multipliers of the upstream smooth product rule. -/
theorem memLpOn_openCubeSet_of_continuous (Q : TriadicCube d) {p : ℝ≥0∞}
    {f : Vec d → ℝ} (hf : Continuous f) : MemLpOn (openCubeSet Q) p f := by
  have hsub : openCubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    ProperSpace.isCompact_closedBall _ _
  have hbdd : BddAbove ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    hK.bddAbove_image hf.norm.continuousOn
  refine MeasureTheory.MemLp.of_bound hf.aestronglyMeasurable
    (sSup ((fun y : Vec d => ‖f y‖) ''
      Metric.closedBall (cubeCenter Q) (cubeRadius Q))) ?_
  filter_upwards
    [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with y hy
  exact le_csSup hbdd (Set.mem_image_of_mem _ (hsub hy))

private theorem halfCubeRadiusPos (Q : TriadicCube d) : 0 < cubeRadius Q / 2 := by
  have := cubeRadius_pos Q
  linarith only [this]

private theorem closedBallHalfSubset (Q : TriadicCube d) :
    Metric.closedBall (cubeCenter Q) (cubeRadius Q / 2) ⊆ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet Q]
  intro y hy
  have hy' : dist y (cubeCenter Q) ≤ cubeRadius Q / 2 := hy
  have hpos := cubeRadius_pos Q
  exact Metric.mem_ball.2 (by linarith only [hy', hpos])

/-! ## The smoothing scale -/

private def smoothScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

private theorem smoothScalePos (n : ℕ) : 0 < smoothScale n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have : (0 : ℝ) < (n : ℝ) + 2 := by linarith only [hn]
  exact div_pos one_pos this

private theorem smoothScaleLtOne (n : ℕ) : smoothScale n < 1 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith only [hn]
  rw [smoothScale, div_lt_one h2]
  linarith only [hn]

private theorem tendstoSmoothScale :
    Filter.Tendsto smoothScale Filter.atTop (nhds 0) := by
  have hbase : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h := hbase.inv_tendsto_atTop
  refine h.congr fun n => ?_
  simp [smoothScale, one_div]

/-! ## The globally smooth approximating sequence on a cube -/

/-- The globally smooth convex-approximation sequence of a continuous field on a
triadic cube. -/
private def cubeSmoothSeq (Q : TriadicCube d) (g : Vec d → ℝ) (n : ℕ) : Vec d → ℝ :=
  convexApproxSmoothRepresentative (openCubeSet Q) unitConvexApproxKernel g
    (cubeCenter Q) (cubeRadius Q / 2) (smoothScale n)

private theorem contDiffCubeSmoothSeq (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : Continuous g) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeSmoothSeq Q g n) :=
  contDiff_convexApproxSmoothRepresentative (p := 2)
    (isOpen_openCubeSet Q).measurableSet isConvexApproxKernel_unitConvexApproxKernel
    (by norm_num) (memLpOn_openCubeSet_of_continuous Q hg)
    (halfCubeRadiusPos Q) (smoothScalePos n)

private theorem cubeSmoothSeqEqOn (Q : TriadicCube d) (g : Vec d → ℝ) (n : ℕ)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    cubeSmoothSeq Q g n x =
      convexApproxSmoothing unitConvexApproxKernel g (cubeCenter Q)
        (cubeRadius Q / 2) (smoothScale n) x :=
  convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
    (isOpenBoundedConvexDomain_openCubeSet Q)
    isConvexApproxKernel_unitConvexApproxKernel hx (closedBallHalfSubset Q)
    (halfCubeRadiusPos Q) (smoothScalePos n) (smoothScaleLtOne n)

private theorem cubeSmoothSeqFDerivEq (Q : TriadicCube d) (g : Vec d → ℝ) (n : ℕ)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    fderiv ℝ (cubeSmoothSeq Q g n) x =
      fderiv ℝ (convexApproxSmoothing unitConvexApproxKernel g (cubeCenter Q)
        (cubeRadius Q / 2) (smoothScale n)) x := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [(isOpen_openCubeSet Q).mem_nhds hx] with y hy
  exact cubeSmoothSeqEqOn Q g n hy

private theorem cubeSmoothSeqUniform (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : Continuous g) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ x ∈ openCubeSet Q, |cubeSmoothSeq Q g n x - g x| ≤ δ := by
  filter_upwards [eventually_forall_abs_convexApproxSmoothing_sub_le_of_continuous
    (isOpenBoundedConvexDomain_openCubeSet Q)
    isConvexApproxKernel_unitConvexApproxKernel hg (closedBallHalfSubset Q)
    (halfCubeRadiusPos Q).le tendstoSmoothScale
    (Filter.Eventually.of_forall fun n => (smoothScalePos n).le)
    (Filter.Eventually.of_forall fun n => (smoothScaleLtOne n).le) hδ] with n hn x hx
  rw [cubeSmoothSeqEqOn Q g n hx]
  exact hn hx

private theorem cubeSmoothSeqFDerivUniform (Q : TriadicCube d) {g : Vec d → ℝ}
    (hg : ContDiff ℝ 1 g) (i : Fin d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ x ∈ openCubeSet Q,
      |(fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec i) -
        (fderiv ℝ g x) (basisVec i)| ≤ δ := by
  filter_upwards
    [eventually_forall_abs_fderiv_convexApproxSmoothing_apply_basisVec_sub_le_of_contDiff
      (isOpenBoundedConvexDomain_openCubeSet Q)
      isConvexApproxKernel_unitConvexApproxKernel hg (closedBallHalfSubset Q)
      (halfCubeRadiusPos Q).le tendstoSmoothScale
      (Filter.Eventually.of_forall fun n => (smoothScalePos n).le)
      (Filter.Eventually.of_forall fun n => (smoothScaleLtOne n).le) i hδ] with n hn x hx
  rw [cubeSmoothSeqFDerivEq Q g n hx]
  exact hn hx

/-! ## `L²` convergence from a uniform bound -/

private theorem tendstoELpNormOfUniform {U : Set (Vec d)} (hU : MeasurableSet U)
    {F : ℕ → Vec d → ℝ} {W : Vec d → ℝ}
    (hW : MemLp W 2 (volume.restrict U))
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict U))
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop, ∀ x ∈ U, |F n x| ≤ δ * |W x|) :
    Filter.Tendsto (fun n => eLpNorm (F n) 2 (volume.restrict U))
      Filter.atTop (nhds 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
  by_cases htop : η = ⊤
  · exact Filter.Eventually.of_forall fun n => htop ▸ le_top
  have hWtop : eLpNorm W 2 (volume.restrict U) ≠ ⊤ := hW.eLpNorm_ne_top
  set C : ℝ := (eLpNorm W 2 (volume.restrict U)).toReal with hC
  have hCnonneg : 0 ≤ C := ENNReal.toReal_nonneg
  have hCone : (0 : ℝ) < C + 1 := by linarith only [hCnonneg]
  have hetaPos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' htop
  set δ : ℝ := η.toReal / (C + 1) with hδ
  have hδpos : 0 < δ := div_pos hetaPos hCone
  filter_upwards [h δ hδpos] with n hn
  have hae : ∀ᵐ x ∂(volume.restrict U), ‖F n x‖ ≤ ‖(δ • W) x‖ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
    have := hn x hx
    simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul, norm_mul, abs_of_pos hδpos, ge_iff_le] using this
  have hmono : eLpNorm (F n) 2 (volume.restrict U)
      ≤ eLpNorm ((δ : ℝ) • W) 2 (volume.restrict U) :=
    MeasureTheory.eLpNorm_mono_ae (hF n) hae
  have hsmul : eLpNorm ((δ : ℝ) • W) 2 (volume.restrict U)
      ≤ ENNReal.ofReal δ * eLpNorm W 2 (volume.restrict U) := by
    refine le_trans MeasureTheory.eLpNorm_const_smul_le ?_
    gcongr
    simp [Real.enorm_eq_ofReal_abs, abs_of_pos hδpos]
  have hWle : eLpNorm W 2 (volume.restrict U) ≤ ENNReal.ofReal (C + 1) := by
    rw [← ENNReal.ofReal_toReal hWtop, ← hC]
    exact ENNReal.ofReal_le_ofReal (by linarith only [])
  calc eLpNorm (F n) 2 (volume.restrict U)
      ≤ ENNReal.ofReal δ * eLpNorm W 2 (volume.restrict U) := hmono.trans hsmul
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (C + 1) := by gcongr
    _ = ENNReal.ofReal (δ * (C + 1)) := (ENNReal.ofReal_mul hδpos.le).symm
    _ = η := by
        rw [hδ, div_mul_cancel₀ _ hCone.ne', ENNReal.ofReal_toReal htop]

/-! ## The weak product rule -/

/-- **The weak product rule for a `C¹` scalar factor and an `H¹` factor on a
cube.**  For `g` of class `C¹` and `v ∈ H¹(Q)`,

`∇(g v) = g ∇v + v ∇g` in the weak sense on the open cube.

The `C¹` factor is not smooth, so it cannot be fed to the upstream smooth
product rule directly; the proof approximates `g` by the globally smooth convex
smoothings `cubeSmoothSeq`, applies the smooth product rule to each, and passes
to the limit with `HasWeakPartialDerivOn.of_tendsto_eLpNorm_two`.  Both
convergences are uniform on the cube, hence `L²` because the cube is bounded. -/
theorem hasWeakGradientOn_mul_of_contDiff_one (Q : TriadicCube d)
    {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) (v : H1Function (openCubeSet Q)) :
    HasWeakGradientOn (openCubeSet Q) (fun x => g x * v.toFun x)
      (fun x i => g x * v.grad x i + v.toFun x * (fderiv ℝ g x) (basisVec i)) := by
  intro k
  have hgc : Continuous g := hg.continuous
  have hdgc : ∀ i : Fin d, Continuous (fun x : Vec d => (fderiv ℝ g x) (basisVec i)) :=
    fun i => (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  -- the smooth approximations and their top-integrability data
  have hGTop : ∀ n : ℕ, MemLp (cubeSmoothSeq Q g n) ⊤
      (volume.restrict (openCubeSet Q)) := fun n =>
    memLpOn_openCubeSet_of_continuous Q (contDiffCubeSmoothSeq Q hgc n).continuous
  have hdGTop : ∀ (n : ℕ) (i : Fin d),
      MemLp (fun x => (fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec i)) ⊤
        (volume.restrict (openCubeSet Q)) := fun n i =>
    memLpOn_openCubeSet_of_continuous Q
      (((contDiffCubeSmoothSeq Q hgc n).continuous_fderiv (by simp)).clm_apply
        continuous_const)
  have hweakn : ∀ n : ℕ, HasWeakPartialDerivOn (openCubeSet Q) k
      (fun x => cubeSmoothSeq Q g n x * v.toFun x)
      (fun x => cubeSmoothSeq Q g n x * v.grad x k +
        v.toFun x * (fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec k)) := by
    intro n
    have h := (v.mulContDiffMemLpTop (contDiffCubeSmoothSeq Q hgc n) (hGTop n)
      (hdGTop n)).hasWeakGradient k
    rwa [H1Function.mulContDiffMemLpTop_toFun,
      H1Function.mulContDiffMemLpTop_grad] at h
  have hmemn : ∀ n : ℕ, MemLp (fun x => cubeSmoothSeq Q g n x * v.toFun x) 2
      (volume.restrict (openCubeSet Q)) := fun n => (hGTop n).fun_mul v.memL2
  have hgradn : ∀ n : ℕ, MemLp (fun x => cubeSmoothSeq Q g n x * v.grad x k +
      v.toFun x * (fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec k)) 2
      (volume.restrict (openCubeSet Q)) := by
    intro n
    have h := (v.mulContDiffMemLpTop (contDiffCubeSmoothSeq Q hgc n) (hGTop n)
      (hdGTop n)).gradMemL2 k
    rwa [H1Function.mulContDiffMemLpTop_grad] at h
  -- the limits
  have hmemLim : MemLp (fun x => g x * v.toFun x) 2
      (volume.restrict (openCubeSet Q)) :=
    (memLpOn_openCubeSet_of_continuous (p := ⊤) Q hgc).fun_mul v.memL2
  have hgradLim : MemLp (fun x => g x * v.grad x k +
      v.toFun x * (fderiv ℝ g x) (basisVec k)) 2
      (volume.restrict (openCubeSet Q)) := by
    refine MeasureTheory.MemLp.add
      ((memLpOn_openCubeSet_of_continuous (p := ⊤) Q hgc).fun_mul (v.gradMemL2 k)) ?_
    have h : MemLp (fun x => (fderiv ℝ g x) (basisVec k) * v.toFun x) 2
        (volume.restrict (openCubeSet Q)) :=
      (memLpOn_openCubeSet_of_continuous (p := ⊤) Q (hdgc k)).fun_mul v.memL2
    have hrw : (fun x : Vec d => (fderiv ℝ g x) (basisVec k) * v.toFun x)
        = fun x : Vec d => v.toFun x * (fderiv ℝ g x) (basisVec k) := by
      funext x; ring
    rwa [hrw] at h
  refine HasWeakPartialDerivOn.of_tendsto_eLpNorm_two hmemLim hgradLim hmemn hgradn
    hweakn ?_ ?_
  · refine tendstoELpNormOfUniform (isOpen_openCubeSet Q).measurableSet v.memL2
      (fun n => ((hmemn n).sub hmemLim).aestronglyMeasurable) ?_
    intro δ hδ
    filter_upwards [cubeSmoothSeqUniform Q hgc hδ] with n hn x hx
    have hb := hn x hx
    have hrw : cubeSmoothSeq Q g n x * v.toFun x - g x * v.toFun x
        = (cubeSmoothSeq Q g n x - g x) * v.toFun x := by ring
    rw [hrw, abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  · have hWmem : MemLp (fun x => ‖v.grad x k‖ + ‖v.toFun x‖) 2
        (volume.restrict (openCubeSet Q)) := (v.gradMemL2 k).norm.add v.memL2.norm
    refine tendstoELpNormOfUniform (isOpen_openCubeSet Q).measurableSet hWmem
      (fun n => ((hgradn n).sub hgradLim).aestronglyMeasurable) ?_
    intro δ hδ
    filter_upwards [cubeSmoothSeqUniform Q hgc hδ,
      cubeSmoothSeqFDerivUniform Q hg k hδ] with n hn hn' x hx
    have hb := hn x hx
    have hb' := hn' x hx
    have hrw : (cubeSmoothSeq Q g n x * v.grad x k +
          v.toFun x * (fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec k)) -
        (g x * v.grad x k + v.toFun x * (fderiv ℝ g x) (basisVec k))
        = (cubeSmoothSeq Q g n x - g x) * v.grad x k +
          v.toFun x * ((fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec k) -
            (fderiv ℝ g x) (basisVec k)) := by ring
    have h1 : |(cubeSmoothSeq Q g n x - g x) * v.grad x k| ≤ δ * ‖v.grad x k‖ := by
      rw [abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    have h2 : |v.toFun x * ((fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec k) -
        (fderiv ℝ g x) (basisVec k))| ≤ δ * ‖v.toFun x‖ := by
      rw [abs_mul, Real.norm_eq_abs, mul_comm δ]
      exact mul_le_mul_of_nonneg_left hb' (abs_nonneg _)
    have habs : |‖v.grad x k‖ + ‖v.toFun x‖| = ‖v.grad x k‖ + ‖v.toFun x‖ :=
      abs_of_nonneg (by positivity)
    rw [hrw, habs]
    calc |(cubeSmoothSeq Q g n x - g x) * v.grad x k +
            v.toFun x * ((fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec k) -
              (fderiv ℝ g x) (basisVec k))|
        ≤ |(cubeSmoothSeq Q g n x - g x) * v.grad x k| +
          |v.toFun x * ((fderiv ℝ (cubeSmoothSeq Q g n) x) (basisVec k) -
            (fderiv ℝ g x) (basisVec k))| := abs_add_le _ _
      _ ≤ δ * ‖v.grad x k‖ + δ * ‖v.toFun x‖ := add_le_add h1 h2
      _ = δ * (‖v.grad x k‖ + ‖v.toFun x‖) := by ring

/-! ## Schwarz symmetry of a weak Hessian -/

/-- **Schwarz symmetry of a weak Hessian.**  Two mixed weak second derivatives
of an `H¹` function on an open set agree almost everywhere: both are read off
the same second derivative of the test function. -/
theorem hess_ae_eq_swap {U : Set (Vec d)} (hU : IsOpen U) {u : H1Function U}
    (H : HasWeakHessianOn U u) (i j : Fin d) :
    H.hess i j =ᵐ[volume.restrict U] H.hess j i := by
  have hijLoc : MeasureTheory.LocallyIntegrableOn (H.hess i j) U volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((H.hess_memL2 i j).locallyIntegrable (by norm_num))
  have hjiLoc : MeasureTheory.LocallyIntegrableOn (H.hess j i) U volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((H.hess_memL2 j i).locallyIntegrable (by norm_num))
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hU.measurableSet]
  have hzero : ∀ᵐ x ∂volume, x ∈ U → H.hess i j x - H.hess j i x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hijLoc.sub hjiLoc) ?_
    intro phi hphi hphis hphiSub
    have hij := H.weak_second i j phi hphi hphis hphiSub
    have hji := H.weak_second j i phi hphi hphis hphiSub
    have huij := u.hasWeakPartialDerivOn i (euclideanCoordDeriv j phi)
      (contDiff_euclideanCoordDeriv hphi j)
      (hasCompactSupport_euclideanCoordDeriv hphis j)
      ((tsupport_euclideanCoordDeriv_subset_tsupport j phi).trans hphiSub)
    have huji := u.hasWeakPartialDerivOn j (euclideanCoordDeriv i phi)
      (contDiff_euclideanCoordDeriv hphi i)
      (hasCompactSupport_euclideanCoordDeriv hphis i)
      ((tsupport_euclideanCoordDeriv_subset_tsupport i phi).trans hphiSub)
    have hphiL2 : MemScalarL2 U phi := by
      simpa only [MemScalarL2, volumeMeasureOn] using
        (hphi.continuous.memLp_of_hasCompactSupport hphis).restrict U
    have hijInt : MeasureTheory.Integrable (fun x => H.hess i j x * phi x)
        (volume.restrict U) := by
      exact (H.hess_memL2 i j).integrable_mul hphiL2
    have hjiInt : MeasureTheory.Integrable (fun x => H.hess j i x * phi x)
        (volume.restrict U) := by
      exact (H.hess_memL2 j i).integrable_mul hphiL2
    have hijOut : ∀ x, x ∉ U → H.hess i j x * phi x = 0 := by
      intro x hx
      have hnot : x ∉ tsupport phi := fun hx' => hx (hphiSub hx')
      simp [image_eq_zero_of_notMem_tsupport hnot]
    have hjiOut : ∀ x, x ∉ U → H.hess j i x * phi x = 0 := by
      intro x hx
      have hnot : x ∉ tsupport phi := fun hx' => hx (hphiSub hx')
      simp [image_eq_zero_of_notMem_tsupport hnot]
    have hijGlobal : MeasureTheory.Integrable (fun x => H.hess i j x * phi x) volume :=
      MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero hijInt hijOut
    have hjiGlobal : MeasureTheory.Integrable (fun x => H.hess j i x * phi x) volume :=
      MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero hjiInt hjiOut
    have hij' : ∫ x in U, u.grad x i * euclideanCoordDeriv j phi x ∂volume =
        -∫ x in U, H.hess i j x * phi x ∂volume := by
      simpa only [euclideanCoordDeriv] using hij
    have hji' : ∫ x in U, u.grad x j * euclideanCoordDeriv i phi x ∂volume =
        -∫ x in U, H.hess j i x * phi x ∂volume := by
      simpa only [euclideanCoordDeriv] using hji
    have huij' : ∫ x in U, u x * euclideanCoordSecondDeriv j i phi x ∂volume =
        -∫ x in U, u.grad x i * euclideanCoordDeriv j phi x ∂volume := by
      simpa only [euclideanCoordSecondDeriv, euclideanCoordDeriv] using huij
    have huji' : ∫ x in U, u x * euclideanCoordSecondDeriv i j phi x ∂volume =
        -∫ x in U, u.grad x j * euclideanCoordDeriv i phi x ∂volume := by
      simpa only [euclideanCoordSecondDeriv, euclideanCoordDeriv] using huji
    simp only [smul_eq_mul]
    rw [show (fun x => phi x * (H.hess i j x - H.hess j i x)) =
        (fun x => H.hess i j x * phi x - H.hess j i x * phi x) by
          funext x; ring, MeasureTheory.integral_sub hijGlobal hjiGlobal]
    refine sub_eq_zero.mpr ?_
    calc ∫ x, H.hess i j x * phi x ∂volume
        = ∫ x in U, H.hess i j x * phi x ∂volume :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hijOut).symm
      _ = -∫ x in U, u.grad x i * euclideanCoordDeriv j phi x ∂volume := by
          linarith only [hij']
      _ = ∫ x in U, u x * euclideanCoordSecondDeriv j i phi x ∂volume := by
          linarith only [huij']
      _ = ∫ x in U, u x * euclideanCoordSecondDeriv i j phi x ∂volume := by
          refine MeasureTheory.setIntegral_congr_fun hU.measurableSet fun x _ => ?_
          rw [euclideanCoordSecondDeriv_comm hphi j i x]
      _ = -∫ x in U, u.grad x j * euclideanCoordDeriv i phi x ∂volume := by
          linarith only [huji']
      _ = ∫ x in U, H.hess j i x * phi x ∂volume := by linarith only [hji']
      _ = ∫ x, H.hess j i x * phi x ∂volume :=
          MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hjiOut
  filter_upwards [hzero] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-! ## The symmetrized weak Hessian -/

/-- A weak partial derivative may be modified on a null set of the domain. -/
private theorem hasWeakPartialDerivOnCongrDeriv {U : Set (Vec d)}
    {i : Fin d} {u g g' : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u g)
    (hae : g =ᵐ[volume.restrict U] g') :
    HasWeakPartialDerivOn U i u g' := by
  intro phi hphi hs hsub
  have hcongr : ∫ x in U, g' x * phi x ∂volume = ∫ x in U, g x * phi x ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hcongr]
  exact h phi hphi hs hsub

theorem hessSymmMemL2 {U : Set (Vec d)} {u : H1Function U}
    (H : HasWeakHessianOn U u) (i j : Fin d) :
    MemScalarL2 U (fun x => (H.hess i j x + H.hess j i x) / 2) := by
  have h : MemScalarL2 U (fun x => H.hess i j x + H.hess j i x) :=
    MeasureTheory.MemLp.add (H.hess_memL2 i j) (H.hess_memL2 j i)
  have h2 : MemScalarL2 U (fun x => (2 : ℝ)⁻¹ * (H.hess i j x + H.hess j i x)) :=
    MeasureTheory.MemLp.const_mul h _
  have hrw : (fun x : Vec d => (2 : ℝ)⁻¹ * (H.hess i j x + H.hess j i x))
      = fun x : Vec d => (H.hess i j x + H.hess j i x) / 2 := by
    funext x
    ring
  rwa [hrw] at h2

theorem hessSymmWeak {U : Set (Vec d)} (hU : IsOpen U) {u : H1Function U}
    (H : HasWeakHessianOn U u) (i j : Fin d) :
    HasWeakPartialDerivOn U j (fun x => u.grad x i)
      (fun x => (H.hess i j x + H.hess j i x) / 2) := by
  refine hasWeakPartialDerivOnCongrDeriv (H.weak_second i j) ?_
  filter_upwards [hess_ae_eq_swap hU H j i] with x hx
  rw [hx]
  ring

/-- **The symmetrized weak Hessian.**  Averaging a weak Hessian witness with its
transpose changes it only on a null set, by `hess_ae_eq_swap`, and produces a
witness whose entries satisfy `hess i j x = hess j i x` at *every* point.  The
pointwise symmetry is what the divergence identity of the integration by parts needs:
the contraction of an antisymmetric matrix with the Hessian must vanish
everywhere on the cube, not merely almost everywhere. -/
noncomputable def hasWeakHessianOnSymm {U : Set (Vec d)} (hU : IsOpen U)
    {u : H1Function U} (H : HasWeakHessianOn U u) : HasWeakHessianOn U u where
  hess := fun i j x => (H.hess i j x + H.hess j i x) / 2
  hess_memL2 := hessSymmMemL2 H
  weak_second := hessSymmWeak hU H

@[simp] theorem hasWeakHessianOnSymm_hess {U : Set (Vec d)} (hU : IsOpen U)
    {u : H1Function U} (H : HasWeakHessianOn U u) (i j : Fin d) (x : Vec d) :
    (hasWeakHessianOnSymm hU H).hess i j x = (H.hess i j x + H.hess j i x) / 2 :=
  rfl

/-! ## Finite sums of weak partial derivatives -/

private theorem memL2OnTestDeriv {U : Set (Vec d)} {phi : Vec d → ℝ} (i : Fin d)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hs : HasCompactSupport phi) :
    MemL2On U (fun x => (fderiv ℝ phi x) (basisVec i)) := by
  have hcont : Continuous (fun x : Vec d => (fderiv ℝ phi x) (basisVec i)) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs : HasCompactSupport (fun x : Vec d => (fderiv ℝ phi x) (basisVec i)) := by
    simpa only using hs.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hcont.memLp_of_hasCompactSupport hcs).restrict U

private theorem hasWeakPartialDerivOnSum {U : Set (Vec d)} {i : Fin d}
    {ι : Type*} (s : Finset ι) (f g : ι → Vec d → ℝ)
    (hf : ∀ a ∈ s, MemL2On U (f a)) (hg : ∀ a ∈ s, MemL2On U (g a))
    (h : ∀ a ∈ s, HasWeakPartialDerivOn U i (f a) (g a)) :
    HasWeakPartialDerivOn U i (fun x => ∑ a ∈ s, f a x)
      (fun x => ∑ a ∈ s, g a x) := by
  intro phi hphi hs hsub
  have hphiL2 : MemL2On U phi := (hphi.continuous.memLp_of_hasCompactSupport hs).restrict U
  have hdL2 : MemL2On U (fun x => (fderiv ℝ phi x) (basisVec i)) :=
    memL2OnTestDeriv i hphi hs
  have hleft : ∫ x in U, (∑ a ∈ s, f a x) * (fderiv ℝ phi x) (basisVec i) ∂volume
      = ∑ a ∈ s, ∫ x in U, f a x * (fderiv ℝ phi x) (basisVec i) ∂volume := by
    rw [show (fun x : Vec d => (∑ a ∈ s, f a x) * (fderiv ℝ phi x) (basisVec i))
        = fun x : Vec d => ∑ a ∈ s, f a x * (fderiv ℝ phi x) (basisVec i) from
      funext fun x => Finset.sum_mul _ _ _]
    exact MeasureTheory.integral_finsetSum s
      (fun a ha => (hf a ha).integrable_mul hdL2)
  have hright : ∫ x in U, (∑ a ∈ s, g a x) * phi x ∂volume
      = ∑ a ∈ s, ∫ x in U, g a x * phi x ∂volume := by
    rw [show (fun x : Vec d => (∑ a ∈ s, g a x) * phi x)
        = fun x : Vec d => ∑ a ∈ s, g a x * phi x from
      funext fun x => Finset.sum_mul _ _ _]
    exact MeasureTheory.integral_finsetSum s
      (fun a ha => (hg a ha).integrable_mul hphiL2)
  rw [hleft, hright, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a ha => h a ha phi hphi hs hsub

/-! ## The weak Jacobian of a `C¹` matrix field applied to a weak gradient -/

/-- The `j`-th gradient coordinate of an `H¹` function with a weak Hessian,
packaged as an `H¹` function with the corresponding Hessian row as gradient. -/
private def hessRowH1 {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u) (j : Fin d) :
    H1Function (openCubeSet Q) where
  toFun := fun x => u.grad x j
  grad := fun x k => H.hess j k x
  memL2 := u.gradMemL2 j
  gradMemL2 := fun k => H.hess_memL2 j k
  hasWeakGradient := fun k => H.weak_second j k

/-- **The weak Jacobian of `x ↦ K x ∇u x`** for a `C¹` matrix field `K` and an
`H¹` function `u` carrying a weak Hessian, in the shape
`Sobolev/DirichletW2pDivergence.HasWeakJacobianOn` consumes: the `i`-th row is

`∂_k (∑_j K_{ij} ∂_j u) = ∑_j ((∂_k K_{ij}) ∂_j u + K_{ij} ∂_k∂_j u)`.

Each summand is the weak product rule `hasWeakGradientOn_mul_of_contDiff_one`
applied to the `C¹` entry `K_{ij}` and the `H¹` function `∂_j u`; the sum is
`hasWeakPartialDerivOnSum`. -/
theorem hasWeakJacobianOn_matVecMul_of_contDiff_one (Q : TriadicCube d)
    {K : Vec d → Mat d} (hK : ∀ i j : Fin d, ContDiff ℝ 1 (fun x : Vec d => K x i j))
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u) :
    Sobolev.HasWeakJacobianOn (openCubeSet Q) (fun x => matVecMul (K x) (u.grad x))
      (fun i x k => ∑ j : Fin d, (K x i j * H.hess j k x +
        u.grad x j * (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec k))) := by
  intro i k
  have hmem : ∀ j : Fin d, MemL2On (openCubeSet Q) (fun x => K x i j * u.grad x j) :=
    fun j => (memLpOn_openCubeSet_of_continuous (p := ⊤) Q (hK i j).continuous).fun_mul
      (u.gradMemL2 j)
  have hmemg : ∀ j : Fin d, MemL2On (openCubeSet Q)
      (fun x => K x i j * H.hess j k x +
        u.grad x j * (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec k)) := by
    intro j
    refine MeasureTheory.MemLp.add ((memLpOn_openCubeSet_of_continuous (p := ⊤) Q (hK i j).continuous).fun_mul
      (H.hess_memL2 j k)) ?_
    have hc : Continuous
        (fun x : Vec d => (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec k)) :=
      ((hK i j).continuous_fderiv (by simp)).clm_apply continuous_const
    have h : MemL2On (openCubeSet Q)
        (fun x => (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec k) * u.grad x j) :=
      (memLpOn_openCubeSet_of_continuous (p := ⊤) Q hc).fun_mul (u.gradMemL2 j)
    have hrw : (fun x : Vec d =>
          (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec k) * u.grad x j)
        = fun x : Vec d => u.grad x j *
          (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec k) := by
      funext x; ring
    rwa [hrw] at h
  have hrow : ∀ j : Fin d, HasWeakPartialDerivOn (openCubeSet Q) k
      (fun x => K x i j * u.grad x j)
      (fun x => K x i j * H.hess j k x +
        u.grad x j * (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec k)) :=
    fun j => hasWeakGradientOn_mul_of_contDiff_one Q (hK i j) (hessRowH1 H j) k
  exact hasWeakPartialDerivOnSum Finset.univ _ _ (fun j _ => hmem j)
    (fun j _ => hmemg j) (fun j _ => hrow j)

end

end SuperdiffusionCLT.Section3.Terms
