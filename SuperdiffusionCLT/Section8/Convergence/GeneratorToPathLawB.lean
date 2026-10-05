/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.InvariancePrinciple
public import SuperdiffusionCLT.Section8.Brownian.HeatCore
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApi
public import SuperdiffusionCLT.Section8.Brownian.HeatCoreC

/-!
# Smooth compactly supported functions are a core for the heat generator

The generator approximation of the manuscript is formulated for `u ∈ C_c^∞(ℝ^d)`, while the heat
core of `Brownian.dense_smul_sub_half_laplacian_heatCore` is the larger class of `C²` functions of
`C₀` with second derivative vanishing at infinity.  This file bridges the two: the functions
`f - ½ Δ f`, for `f` smooth with compact support, are dense in `C₀(ℝ^d)`
(`genPath_dense_smooth_range`).

The proof approximates a function `f` of the heat core in the graph norm
`‖f‖_∞ + ‖Δ f‖_∞` by smooth compactly supported functions in two steps:

* a cutoff `f ↦ χ(·/R) f` (`genPath_exists_compact_close`), whose Laplacian error is controlled by
  the product rule `genPath_vecLaplacian_mul` and by a bound on the first derivative
  (`genPath_norm_fderiv_apply_le`);
* a mollification `g = φ ⋆ h` (`genPath_exists_smooth_close`), whose Laplacian is the
  mollification of the Laplacian (`genPath_fderiv_convolution_apply`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence

open Filter Homogenization MeasureTheory Topology Convolution
open scoped ContDiff ZeroAtInfty

noncomputable section

variable {d : ℕ}

theorem genPath_fderiv_convolution_apply (φ : Vec d → ℝ)
    (hφ : LocallyIntegrable φ (volume : Measure (Vec d))) {k : Vec d → ℝ}
    (hk : ContDiff ℝ 1 k) (hcs : HasCompactSupport k) (x v : Vec d) :
    fderiv ℝ (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x v =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => fderiv ℝ k y v)) x := by
  rw [(hcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hφ hk x).fderiv]
  have hex := (hcs.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Vec d)) hφ (hk.continuous_fderiv one_ne_zero) x
  unfold convolution
  rw [ContinuousLinearMap.integral_apply hex v]
  rfl

theorem genPath_fderiv_fderiv_apply {w : Vec d → ℝ} (hw : ContDiff ℝ 2 w) (x e e' : Vec d) :
    fderiv ℝ (fun y => fderiv ℝ w y e') x e = fderiv ℝ (fderiv ℝ w) x e e' := by
  have h1 : Differentiable ℝ (fderiv ℝ w) :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [fderiv_clm_apply (h1 x) (differentiableAt_const e')]
  simp

theorem genPath_contDiff_fderiv_apply {w : Vec d → ℝ} (hw : ContDiff ℝ 2 w) (e : Vec d) :
    ContDiff ℝ 1 (fun y => fderiv ℝ w y e) :=
  ((hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)

theorem genPath_hasCompactSupport_fderiv_apply {w : Vec d → ℝ} (hcs : HasCompactSupport w)
    (e : Vec d) : HasCompactSupport (fun y => fderiv ℝ w y e) :=
  (hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L e) (by simp)

theorem genPath_vecLaplacian_eq_sum_m {w : Vec d → ℝ} (hw : ContDiff ℝ 2 w) (x : Vec d) :
    Brownian.vecLaplacian w x = ∑ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ w y (Pi.single i 1)) x (Pi.single i 1) := by
  rw [Brownian.vecLaplacian_eq_sum_fderiv]
  exact Finset.sum_congr rfl fun i _ => (genPath_fderiv_fderiv_apply hw x _ _).symm

theorem genPath_exists_smooth_close {h : Vec d → ℝ} (h2 : ContDiff ℝ 2 h)
    (hcs : HasCompactSupport h) {e : ℝ} (he : 0 < e) :
    ∃ g : Vec d → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x,
      |g x - h x| ≤ e ∧
        |Brownian.vecLaplacian g x - Brownian.vecLaplacian h x| ≤ e := by
  set η : ℝ := e / (d + 1) with hηdef
  have hη : 0 < η := by positivity
  set k : Fin d → Vec d → ℝ := fun i y => fderiv ℝ h y (Pi.single i 1) with hk
  set m : Fin d → Vec d → ℝ := fun i y => fderiv ℝ (k i) y (Pi.single i 1) with hm
  have hk1 : ∀ i, ContDiff ℝ 1 (k i) := fun i => genPath_contDiff_fderiv_apply h2 _
  have hkcs : ∀ i, HasCompactSupport (k i) := fun i => genPath_hasCompactSupport_fderiv_apply hcs _
  have hmc : ∀ i, Continuous (m i) := fun i =>
    ((hk1 i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hmcs : ∀ i, HasCompactSupport (m i) := fun i =>
    (hkcs i).fderiv (𝕜 := ℝ) |>.comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (Pi.single i 1))
      (by simp)
  have hucm : ∀ i, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y z : Vec d, dist y z < r → |m i y - m i z| ≤ η := by
    intro i
    obtain ⟨r0, hr0, hr⟩ := Metric.uniformContinuous_iff.mp
      ((hmcs i).uniformContinuous_of_continuous (hmc i)) η hη
    filter_upwards [Ioo_mem_nhdsGT hr0] with r hr' y z hyz
    have := hr (hyz.trans hr'.2)
    rw [Real.dist_eq] at this
    exact this.le
  have huch : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ y z : Vec d, dist y z < r → |h y - h z| ≤ η := by
    obtain ⟨r0, hr0, hr⟩ := Metric.uniformContinuous_iff.mp
      (hcs.uniformContinuous_of_continuous h2.continuous) η hη
    filter_upwards [Ioo_mem_nhdsGT hr0] with r hr' y z hyz
    have := hr (hyz.trans hr'.2)
    rw [Real.dist_eq] at this
    exact this.le
  obtain ⟨r, hr1, hr2, hr3⟩ := ((Filter.eventually_all.2 hucm).and
    (huch.and self_mem_nhdsWithin)).exists
  have hrpos : 0 < r := hr3
  let φ : ContDiffBump (0 : Vec d) := ⟨r / 2, r, half_pos hrpos, half_lt_self hrpos⟩
  set φn : Vec d → ℝ := φ.normed (volume : Measure (Vec d)) with hφn
  have hφloc : LocallyIntegrable φn (volume : Measure (Vec d)) :=
    (φ.contDiff_normed (n := 0)).continuous.locallyIntegrable
  set g : Vec d → ℝ := φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h with hg
  have hgsm : ContDiff ℝ ∞ g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      φ.contDiff_normed h2.continuous.locallyIntegrable
  have hg2 : ContDiff ℝ 2 g := hgsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgcs : HasCompactSupport g :=
    φ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcs
  refine ⟨g, hgsm, hgcs, fun x => ⟨?_, ?_⟩⟩
  · have := φ.dist_normed_convolution_le (μ := volume) (g := h) (x₀ := x) (ε := η)
      h2.continuous.aestronglyMeasurable (fun y hy => by
        rw [Real.dist_eq]
        exact hr2 y x (by simpa only [Metric.mem_ball] using hy))
    rw [Real.dist_eq] at this
    refine this.trans ?_
    rw [hηdef, div_le_iff₀ (by positivity)]
    nlinarith only [he, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  · have hD1 : ∀ y i, fderiv ℝ g y (Pi.single i 1) = (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k i) y :=
      fun y i => genPath_fderiv_convolution_apply φn hφloc (h2.of_le (by norm_num)) hcs y _
    have hD2 : ∀ i, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1) =
        (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] m i) x := by
      intro i
      have : (fun y => fderiv ℝ g y (Pi.single i 1)) =
          φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k i := funext fun y => hD1 y i
      rw [this]
      exact genPath_fderiv_convolution_apply φn hφloc (hk1 i) (hkcs i) x _
    have hlg : Brownian.vecLaplacian g x = ∑ i : Fin d, (φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] m i) x := by
      rw [genPath_vecLaplacian_eq_sum_m hg2]
      exact Finset.sum_congr rfl fun i _ => hD2 i
    have hlh : Brownian.vecLaplacian h x = ∑ i : Fin d, m i x := genPath_vecLaplacian_eq_sum_m h2 x
    rw [hlg, hlh, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i : Fin d, |(φn ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] m i) x - m i x| ≤ η := by
      intro i
      have := φ.dist_normed_convolution_le (μ := volume) (g := m i) (x₀ := x) (ε := η)
        (hmc i).aestronglyMeasurable (fun y hy => by
          rw [Real.dist_eq]
          exact hr1 i y x (by simpa only [Metric.mem_ball] using hy))
      rwa [Real.dist_eq] at this
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hηdef,
      mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith only [he, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

/-- A bound on the first derivative from bounds on the function and on the second derivative. -/
theorem genPath_norm_fderiv_apply_le {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) {B K2 : ℝ}
    (hB : ∀ x, |f x| ≤ B) (hK2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K2) (x v : Vec d)
    (hv : ‖v‖ ≤ 1) : |fderiv ℝ f x v| ≤ 2 * B + K2 := by
  have hK2nn : 0 ≤ K2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) x)) (hK2 x)
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hdiff : Differentiable ℝ (fderiv ℝ f) := h1.differentiable one_ne_zero
  have hlip : ∀ y, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ K2 * ‖y - x‖ := fun y =>
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) (fun z _ => hK2 z) convex_univ
      (Set.mem_univ x) (Set.mem_univ y)
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hψ : ∀ y ∈ Metric.closedBall x 1,
      HasFDerivWithinAt (fun y => f y - fderiv ℝ f x y) (fderiv ℝ f y - fderiv ℝ f x)
        (Metric.closedBall x 1) y := fun y _ =>
    ((hdf y).hasFDerivAt.sub (fderiv ℝ f x).hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ y ∈ Metric.closedBall x 1, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ K2 := by
    intro y hy
    refine (hlip y).trans ?_
    have : ‖y - x‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp hy
    nlinarith only [this, hK2nn, norm_nonneg (y - x)]
  have hxs : x ∈ Metric.closedBall x 1 := Metric.mem_closedBall_self zero_le_one
  have hys : x + v ∈ Metric.closedBall x 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [add_sub_cancel_left] using hv
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hψ hbd (convex_closedBall x 1)
    hxs hys
  have hmv' : |f (x + v) - fderiv ℝ f x (x + v) - (f x - fderiv ℝ f x x)| ≤ K2 := by
    have := hmv
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    simp only [add_sub_cancel_left]
    nlinarith only [hv, hK2nn]
  have e1 : f (x + v) - fderiv ℝ f x (x + v) - (f x - fderiv ℝ f x x) =
      f (x + v) - f x - fderiv ℝ f x v := by
    rw [map_add]
    ring
  rw [e1] at hmv'
  have h2 : |f (x + v) - f x| ≤ 2 * B := by
    have := abs_sub (f (x + v)) (f x)
    linarith only [this, hB (x + v), hB x]
  have h3 : |fderiv ℝ f x v| ≤ |f (x + v) - f x| + |f (x + v) - f x - fderiv ℝ f x v| := by
    have := abs_sub (f (x + v) - f x) (f (x + v) - f x - fderiv ℝ f x v)
    rwa [sub_sub_cancel] at this
  linarith only [h2, h3, hmv']

theorem genPath_vecLaplacian_mul {u v : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (x : Vec d) :
    Brownian.vecLaplacian (fun y => u y * v y) x =
      u x * Brownian.vecLaplacian v x +
        2 * ∑ i : Fin d, fderiv ℝ u x (Pi.single i 1) * fderiv ℝ v x (Pi.single i 1) +
          v x * Brownian.vecLaplacian u x := by
  have huv : ContDiff ℝ 2 (fun y => u y * v y) := hu.mul hv
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have key : ∀ e : Vec d,
      fderiv ℝ (fun y => fderiv ℝ (fun z => u z * v z) y e) x e =
        u x * fderiv ℝ (fun y => fderiv ℝ v y e) x e +
          2 * (fderiv ℝ u x e * fderiv ℝ v x e) +
            v x * fderiv ℝ (fun y => fderiv ℝ u y e) x e := by
    intro e
    have e1 : (fun y => fderiv ℝ (fun z => u z * v z) y e) =
        fun y => u y * fderiv ℝ v y e + v y * fderiv ℝ u y e := by
      funext y
      rw [(( hud y).hasFDerivAt.fun_mul (hvd y).hasFDerivAt).fderiv]
      simp
    have ha := (genPath_contDiff_fderiv_apply hv e).differentiable one_ne_zero
    have hc := (genPath_contDiff_fderiv_apply hu e).differentiable one_ne_zero
    have h1 := (((hud x).hasFDerivAt.fun_mul (ha x).hasFDerivAt).fun_add
      ((hvd x).hasFDerivAt.fun_mul (hc x).hasFDerivAt))
    rw [e1, h1.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [genPath_vecLaplacian_eq_sum_m huv, genPath_vecLaplacian_eq_sum_m hv,
    genPath_vecLaplacian_eq_sum_m hu, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => key _

/-- A continuous function vanishing at infinity is bounded. -/
theorem genPath_exists_bound {g : Vec d → ℝ} (hc : Continuous g)
    (ht : Tendsto g (cocompact (Vec d)) (𝓝 0)) : ∃ B : ℝ, ∀ x, |g x| ≤ B :=
  ⟨‖(⟨⟨g, hc⟩, ht⟩ : C₀(Vec d, ℝ))‖, fun x => by
    simpa only [ZeroAtInftyContinuousMap.coe_mk, Real.norm_eq_abs] using Brownian.norm_apply_le_norm_c0 (⟨⟨g, hc⟩, ht⟩ : C₀(Vec d, ℝ)) x⟩

/-- A continuous function vanishing at infinity is small outside a ball. -/
theorem genPath_exists_radius_of_tendsto {g : Vec d → ℝ}
    (ht : Tendsto g (cocompact (Vec d)) (𝓝 0)) {e : ℝ} (he : 0 < e) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : Vec d, R ≤ ‖y‖ → |g y| < e := by
  have hev : ∀ᶠ y in cocompact (Vec d), |g y| < e :=
    (ht.eventually (Metric.ball_mem_nhds 0 he)).mono fun x hx => by simpa only [dist_zero_right, Real.norm_eq_abs] using hx
  obtain ⟨t, ht', htc⟩ := Filter.mem_cocompact.mp hev
  obtain ⟨R, hR⟩ := ht'.isBounded.subset_closedBall (0 : Vec d)
  refine ⟨|R| + 1, by positivity, fun y hy => htc ?_⟩
  intro hyt
  have := Metric.mem_closedBall.mp (hR hyt)
  rw [dist_zero_right] at this
  linarith only [this, hy, le_abs_self R]

/-- The cutoff bump of radii `1` and `2`. -/
def genPath_bump (d : ℕ) : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff at radius `R`. -/
def genPath_cut (d : ℕ) (R : ℝ) (x : Vec d) : ℝ := genPath_bump d (R⁻¹ • x)

theorem genPath_cut_contDiff (R : ℝ) : ContDiff ℝ ∞ (genPath_cut d R) :=
  (genPath_bump d).contDiff.comp (contDiff_const_smul _)

theorem genPath_cut_nonneg (R : ℝ) (x : Vec d) : 0 ≤ genPath_cut d R x :=
  (genPath_bump d).nonneg

theorem genPath_cut_le_one (R : ℝ) (x : Vec d) : genPath_cut d R x ≤ 1 :=
  (genPath_bump d).le_one

theorem genPath_cut_eq_one {R : ℝ} (hR : 0 < R) {x : Vec d} (hx : ‖x‖ ≤ R) :
    genPath_cut d R x = 1 := by
  refine (genPath_bump d).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hR]
  show R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]
  linarith only [hx]

theorem genPath_cut_eq_zero {R : ℝ} (hR : 0 < R) {x : Vec d} (hx : 2 * R ≤ ‖x‖) :
    genPath_cut d R x = 0 := by
  refine (genPath_bump d).zero_of_le_dist ?_
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
  show 2 ≤ R⁻¹ * ‖x‖
  rw [le_inv_mul_iff₀ hR]
  linarith only [hx]

theorem genPath_fderiv_cut {R : ℝ} (y v : Vec d) :
    fderiv ℝ (genPath_cut d R) y v = R⁻¹ * fderiv ℝ (genPath_bump d) (R⁻¹ • y) v := by
  have hb : DifferentiableAt ℝ (genPath_bump d) (R⁻¹ • y) :=
    (((genPath_bump d).contDiff (n := 1)).differentiable one_ne_zero).differentiableAt
  have h := hb.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul R⁻¹)
  have h2 : fderiv ℝ (genPath_cut d R) y = _ := h.fderiv
  rw [h2]
  simp

theorem genPath_vecLaplacian_cut {R : ℝ} (hR : R ≠ 0) (y : Vec d) :
    Brownian.vecLaplacian (genPath_cut d R) y =
      (R⁻¹) ^ 2 * Brownian.vecLaplacian (genPath_bump d) (R⁻¹ • y) := by
  have hb : ContDiff ℝ 2 (genPath_bump d) :=
    (genPath_bump d).contDiff.of_le (WithTop.coe_le_coe.mpr le_top)
  have hc : ContDiff ℝ 2 (genPath_cut d R) :=
    (genPath_cut_contDiff R).of_le (WithTop.coe_le_coe.mpr le_top)
  have h := divForm_comp_smul (d := d) 1 (fun _ => (1 : ℝ) • (1 : Mat d)) (⇑(genPath_bump d))
    (inv_ne_zero hR) y
  have h1 := divForm_const_smul_one (d := d) 1 (genPath_cut d R) hc y
  have h2 := divForm_const_smul_one (d := d) 1 (⇑(genPath_bump d)) hb (R⁻¹ • y)
  change divForm 1 _ (genPath_cut d R) y = _ at h
  rw [h1, h2] at h
  simpa only [inv_pow, one_mul] using h

theorem genPath_bump_bounds (d : ℕ) :
    ∃ M1 M3 : ℝ, (∀ (y e : Vec d), ‖e‖ ≤ 1 → |fderiv ℝ (genPath_bump d) y e| ≤ M1) ∧
      ∀ y : Vec d, |Brownian.vecLaplacian (genPath_bump d) y| ≤ M3 := by
  obtain ⟨K, hK⟩ := Brownian.heatCore_bound_fderiv ((genPath_bump d).contDiff (n := ⊤))
    (genPath_bump d).hasCompactSupport
  obtain ⟨K2, hK2⟩ := Brownian.heatCore_bound_fderiv_fderiv
    ((genPath_bump d).contDiff (n := ⊤)) (genPath_bump d).hasCompactSupport
  refine ⟨K, d * K2, fun y e he => ?_, fun y => ?_⟩
  · have := (fderiv ℝ (genPath_bump d) y).le_opNorm e
    rw [Real.norm_eq_abs] at this
    have h2 := hK y
    nlinarith only [this, h2, he, norm_nonneg e, norm_nonneg (fderiv ℝ (genPath_bump d) y)]
  · refine (abs_vecLaplacian_le _ y).trans ?_
    rw [Brownian.heatCore_norm_iteratedFDeriv_two]
    exact mul_le_mul_of_nonneg_left (hK2 y) (Nat.cast_nonneg d)

theorem genPath_exists_compact_close {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (hf0 : Tendsto f (cocompact (Vec d)) (𝓝 0))
    (hf2 : Tendsto (iteratedFDeriv ℝ 2 f) (cocompact (Vec d)) (𝓝 0)) {e : ℝ} (he : 0 < e) :
    ∃ h : Vec d → ℝ, ContDiff ℝ 2 h ∧ HasCompactSupport h ∧ ∀ x,
      |h x - f x| ≤ e ∧
        |Brownian.vecLaplacian h x - Brownian.vecLaplacian f x| ≤ e := by
  obtain ⟨B, hB⟩ := genPath_exists_bound hf.continuous hf0
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hnorm2 : Tendsto (fun x => ‖iteratedFDeriv ℝ 2 f x‖) (cocompact (Vec d)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hf2
  obtain ⟨K2, hK2'⟩ := genPath_exists_bound
    (hf.continuous_iteratedFDeriv (by norm_num)).norm hnorm2
  have hK2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ K2 := fun x => by
    rw [← Brownian.heatCore_norm_iteratedFDeriv_two]
    exact (le_abs_self _).trans (hK2' x)
  have hK20 : 0 ≤ K2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)) (hK2 0)
  have hK1 : ∀ (x : Vec d) (i : Fin d), |fderiv ℝ f x (Pi.single i 1)| ≤ 2 * B + K2 :=
    fun x i => genPath_norm_fderiv_apply_le hf hB hK2 x _ (by rw [Pi.norm_single, norm_one])
  obtain ⟨Rl, hRl, hRl'⟩ := genPath_exists_radius_of_tendsto
    (tendsto_vecLaplacian_cocompact hf2) (by positivity : 0 < e / 4)
  obtain ⟨Rf, hRf, hRf'⟩ := genPath_exists_radius_of_tendsto hf0 he
  obtain ⟨M1, M3, hM1, hM3⟩ := genPath_bump_bounds d
  have hM10 : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0 0 (by simp))
  have hM30 : 0 ≤ M3 := (abs_nonneg _).trans (hM3 0)
  set C : ℝ := 2 * d * M1 * (2 * B + K2) + B * M3 with hC
  have hC0 : 0 ≤ C := by positivity
  set R : ℝ := max (max 1 (max Rl Rf)) (2 * C / e) with hRdef
  have hR1 : 1 ≤ R := le_max_of_le_left (le_max_left _ _)
  have hRlR : Rl ≤ R := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have hRfR : Rf ≤ R := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  have hReC : 2 * C / e ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have hRinv : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hRinv0 : 0 < R⁻¹ := inv_pos.mpr hRpos
  have hCR : C * R⁻¹ ≤ e / 2 := by
    rw [mul_inv_le_iff₀ hRpos]
    have := (div_le_iff₀ he).mp hReC
    linarith only [this]
  have hcut2 : ContDiff ℝ 2 (genPath_cut d R) :=
    (genPath_cut_contDiff R).of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun y => genPath_cut d R y * f y, hcut2.mul hf, ?_, fun x => ⟨?_, ?_⟩⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) (2 * R)) fun x hx => ?_
    have hx2 : 2 * R ≤ ‖x‖ := by
      by_contra hcon
      exact hx (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith only [hcon]))
    simp [genPath_cut_eq_zero hRpos hx2]
  · by_cases hxR : ‖x‖ ≤ R
    · simp only [genPath_cut_eq_one hRpos hxR, one_mul, sub_self, abs_zero]
      exact he.le
    · have hxR' : R < ‖x‖ := not_le.mp hxR
      have hfx := hRf' x (hRfR.trans hxR'.le)
      have h1 := genPath_cut_nonneg R x
      have h2 := genPath_cut_le_one R x
      have : genPath_cut d R x * f x - f x = (genPath_cut d R x - 1) * f x := by ring
      rw [this, abs_mul]
      have h3 : |genPath_cut d R x - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith only [h1, h2]
      nlinarith only [h3, hfx, abs_nonneg (f x), abs_nonneg (genPath_cut d R x - 1)]
  · rw [genPath_vecLaplacian_mul hcut2 hf x]
    set K1 : ℝ := 2 * B + K2 with hK1def
    have hK10 : 0 ≤ K1 := by positivity
    have hχ0 := genPath_cut_nonneg R x
    have hχ1 := genPath_cut_le_one R x
    have hdiff : genPath_cut d R x * Brownian.vecLaplacian f x +
        2 * ∑ i : Fin d, fderiv ℝ (genPath_cut d R) x (Pi.single i 1) *
          fderiv ℝ f x (Pi.single i 1) + f x * Brownian.vecLaplacian (genPath_cut d R) x -
        Brownian.vecLaplacian f x =
        (genPath_cut d R x - 1) * Brownian.vecLaplacian f x +
          2 * ∑ i : Fin d, fderiv ℝ (genPath_cut d R) x (Pi.single i 1) *
            fderiv ℝ f x (Pi.single i 1) + f x * Brownian.vecLaplacian (genPath_cut d R) x := by
      ring
    rw [hdiff]
    have t1 : |(genPath_cut d R x - 1) * Brownian.vecLaplacian f x| ≤ e / 4 := by
      by_cases hxR : ‖x‖ ≤ R
      · rw [genPath_cut_eq_one hRpos hxR, sub_self, zero_mul, abs_zero]
        positivity
      · have hxR' : R < ‖x‖ := not_le.mp hxR
        have hl := hRl' x (hRlR.trans hxR'.le)
        have h3 : |genPath_cut d R x - 1| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith only [hχ0, hχ1]
        rw [abs_mul]
        nlinarith only [h3, hl, abs_nonneg (Brownian.vecLaplacian f x),
          abs_nonneg (genPath_cut d R x - 1)]
    have t2 : |2 * ∑ i : Fin d, fderiv ℝ (genPath_cut d R) x (Pi.single i 1) *
        fderiv ℝ f x (Pi.single i 1)| ≤ 2 * d * M1 * K1 * R⁻¹ := by
      have hterm : ∀ i : Fin d, |fderiv ℝ (genPath_cut d R) x (Pi.single i 1) *
          fderiv ℝ f x (Pi.single i 1)| ≤ M1 * K1 * R⁻¹ := by
        intro i
        rw [genPath_fderiv_cut, abs_mul, abs_mul, abs_of_pos hRinv0]
        have ha := hM1 (R⁻¹ • x) (Pi.single i 1) (by rw [Pi.norm_single, norm_one])
        have hb := hK1 x i
        have := mul_le_mul ha hb (abs_nonneg _) hM10
        nlinarith only [this, hRinv0]
      rw [abs_mul, abs_two]
      have hs := (Finset.abs_sum_le_sum_abs (fun i : Fin d => fderiv ℝ (genPath_cut d R) x (Pi.single i 1) *
        fderiv ℝ f x (Pi.single i 1)) Finset.univ).trans (Finset.sum_le_sum fun i _ => hterm i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      nlinarith only [hs]
    have t3 : |f x * Brownian.vecLaplacian (genPath_cut d R) x| ≤ B * M3 * R⁻¹ := by
      rw [abs_mul, genPath_vecLaplacian_cut hRpos.ne', abs_mul, abs_pow, abs_of_pos hRinv0]
      have h3 := hM3 (R⁻¹ • x)
      have h4 : R⁻¹ ^ 2 ≤ R⁻¹ := by nlinarith only [hRinv, hRinv0]
      have h5 : R⁻¹ ^ 2 * |Brownian.vecLaplacian (genPath_bump d) (R⁻¹ • x)| ≤ R⁻¹ * M3 :=
        mul_le_mul h4 h3 (abs_nonneg _) hRinv0.le
      have h6 := mul_le_mul (hB x) h5 (by positivity) hB0
      nlinarith only [h6]
    have hsum : 2 * d * M1 * K1 * R⁻¹ + B * M3 * R⁻¹ ≤ e / 2 := by
      have : (2 * d * M1 * K1 + B * M3) * R⁻¹ ≤ e / 2 := hCR
      nlinarith only [this]
    have habs := abs_add_three ((genPath_cut d R x - 1) * Brownian.vecLaplacian f x)
      (2 * ∑ i : Fin d, fderiv ℝ (genPath_cut d R) x (Pi.single i 1) *
        fderiv ℝ f x (Pi.single i 1)) (f x * Brownian.vecLaplacian (genPath_cut d R) x)
    linarith only [habs, t1, t2, t3, hsum, he]

theorem genPath_norm_le_of_forall (a : C₀(Vec d, ℝ)) {e : ℝ} (he : 0 ≤ e)
    (h : ∀ x, |a x| ≤ e) : ‖a‖ ≤ e := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le he).mpr fun x => by simpa only [ZeroAtInftyContinuousMap.toBCF_apply, Real.norm_eq_abs] using h x

/-- A smooth compactly supported function, as an element of the differentiable class of the heat
generator. -/
def genPath_toC0 (g : Vec d → ℝ) (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    C₀(Vec d, ℝ) := ⟨⟨g, hg.continuous⟩, hcs.is_zero_at_infty⟩

theorem genPath_toC0_mem (g : Vec d → ℝ) (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    genPath_toC0 g hg hcs ∈ heatCore d :=
  ⟨hg.of_le (WithTop.coe_le_coe.mpr le_top), (hcs.iteratedFDeriv (𝕜 := ℝ) 2).is_zero_at_infty⟩

/-- **Smooth compactly supported functions approximate the differentiable class in the graph
norm of the Laplacian.** -/
theorem genPath_exists_cInfty_close (f : heatCore d) {e : ℝ} (he : 0 < e) :
    ∃ g : Vec d → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x,
      |g x - (f : C₀(Vec d, ℝ)) x| ≤ e ∧
        |Brownian.vecLaplacian g x - Brownian.vecLaplacian (f : Vec d → ℝ) x| ≤ e := by
  obtain ⟨h, h2, hcs, hh⟩ := genPath_exists_compact_close f.2.1
    (f : C₀(Vec d, ℝ)).zero_at_infty' f.2.2 (half_pos he)
  obtain ⟨g, hg, hgcs, hgg⟩ := genPath_exists_smooth_close h2 hcs (half_pos he)
  refine ⟨g, hg, hgcs, fun x => ⟨?_, ?_⟩⟩
  · have h1 := (hgg x).1
    have h2 := (hh x).1
    have := abs_add_le (g x - h x) (h x - (f : C₀(Vec d, ℝ)) x)
    rw [sub_add_sub_cancel] at this
    linarith only [this, h1, h2]
  · have h1 := (hgg x).2
    have h2 := (hh x).2
    have := abs_add_le (Brownian.vecLaplacian g x - Brownian.vecLaplacian h x)
      (Brownian.vecLaplacian h x - Brownian.vecLaplacian (f : Vec d → ℝ) x)
    rw [sub_add_sub_cancel] at this
    linarith only [this, h1, h2]

theorem genPath_graph_dist (f f' : heatCore d) {e : ℝ} (he : 0 ≤ e)
    (h1 : ∀ x, |(f' : C₀(Vec d, ℝ)) x - (f : C₀(Vec d, ℝ)) x| ≤ e)
    (h2 : ∀ x, |Brownian.vecLaplacian (f' : Vec d → ℝ) x -
      Brownian.vecLaplacian (f : Vec d → ℝ) x| ≤ e) :
    ‖((1 : ℝ) • (f : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f) -
      ((1 : ℝ) • (f' : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f')‖ ≤ 2 * e := by
  have ha : ‖(f : C₀(Vec d, ℝ)) - f'‖ ≤ e := genPath_norm_le_of_forall _ he fun x => by
    rw [ZeroAtInftyContinuousMap.sub_apply, abs_sub_comm]
    exact h1 x
  have hb : ‖heatCoreLaplacian f - heatCoreLaplacian f'‖ ≤ e :=
    genPath_norm_le_of_forall _ he fun x => by
      rw [ZeroAtInftyContinuousMap.sub_apply, heatCoreLaplacian_apply, heatCoreLaplacian_apply,
        abs_sub_comm]
      exact h2 x
  have heq : ((1 : ℝ) • (f : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f) -
      ((1 : ℝ) • (f' : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f') =
      ((f : C₀(Vec d, ℝ)) - f') - (2 : ℝ)⁻¹ • (heatCoreLaplacian f - heatCoreLaplacian f') := by
    ext x
    simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
      smul_eq_mul]
    ring
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul]
  have : ‖(2 : ℝ)⁻¹‖ = 2⁻¹ := by norm_num
  rw [this]
  nlinarith only [ha, hb, he]

/-- **The smooth compactly supported functions form a core** at the shift `1`: the functions
`f - ½ Δ f`, for `f` smooth with compact support, are dense in `C₀`. -/
theorem genPath_dense_smooth_range (d : ℕ) :
    Dense {g : C₀(Vec d, ℝ) | ∃ f : heatCore d, ContDiff ℝ ∞ (f : Vec d → ℝ) ∧
      HasCompactSupport (f : Vec d → ℝ) ∧
      (1 : ℝ) • (f : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f = g} := by
  intro g
  have hd := Brownian.dense_smul_sub_half_laplacian_heatCore d ⟨1, Set.mem_Ioi.mpr one_pos⟩ g
  refine closure_minimal ?_ isClosed_closure hd
  rintro _ ⟨f, rfl⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g', hg', hcs, hgg⟩ := genPath_exists_cInfty_close f (by positivity : 0 < ε / 4)
  let f' : heatCore d := ⟨genPath_toC0 g' hg' hcs, genPath_toC0_mem g' hg' hcs⟩
  have hf'1 : ContDiff ℝ ∞ ((f' : C₀(Vec d, ℝ)) : Vec d → ℝ) := hg'
  have hf'2 : HasCompactSupport ((f' : C₀(Vec d, ℝ)) : Vec d → ℝ) := hcs
  refine ⟨(1 : ℝ) • (f' : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f',
    ⟨f', hf'1, hf'2, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have := genPath_graph_dist f f' (by positivity : 0 ≤ ε / 4) (fun x => (hgg x).1)
    (fun x => (hgg x).2)
  show ‖((1 : ℝ) • (f : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f) -
    ((1 : ℝ) • (f' : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • heatCoreLaplacian f')‖ < ε
  linarith only [this, hε]

end

end SuperdiffusionCLT.Section8.Convergence
