/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.H1.Definitions
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

/-!
# Integration by parts against `C¹` test functions

A weak partial derivative defined by smooth compactly supported tests also integrates by parts
against `C¹` compactly supported tests supported in the open set: mollify the test function.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped Convolution Pointwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- The mollification radius sequence. -/
noncomputable def intW2p_bump (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : Vec d) :=
  ⟨δ / (n + 2) / 2, δ / (n + 2), by positivity, half_lt_self (by positivity)⟩

theorem intW2p_bump_rOut (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    (intW2p_bump (d := d) δ hδ n).rOut = δ / (n + 2) := rfl

theorem intW2p_tendsto_rOut (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ (intW2p_bump (d := d) δ hδ n).rOut) atTop (𝓝 0) := by
  simp only [intW2p_bump_rOut]
  have h : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact (tendsto_const_nhds.div_atTop h)

theorem intW2p_normed_locInt (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    LocallyIntegrable (((intW2p_bump (d := d) δ hδ n).normed volume)) volume :=
  ((intW2p_bump (d := d) δ hδ n).continuous_normed (μ := volume)).locallyIntegrable

/-- The mollification of a function by the `n`-th bump. -/
noncomputable def intW2p_moll (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (ψ : Vec d → ℝ) : Vec d → ℝ :=
  ((intW2p_bump δ hδ n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ

theorem intW2p_moll_contDiff (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {ψ : Vec d → ℝ} (hψ : Continuous ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (intW2p_moll δ hδ n ψ) :=
  (intW2p_bump δ hδ n).hasCompactSupport_normed.contDiff_convolution_left _
    (intW2p_bump δ hδ n).contDiff_normed hψ.locallyIntegrable

theorem intW2p_moll_compact (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {ψ : Vec d → ℝ}
    (hc : HasCompactSupport ψ) : HasCompactSupport (intW2p_moll δ hδ n ψ) :=
  HasCompactSupport.convolution _ (intW2p_bump δ hδ n).hasCompactSupport_normed hc

theorem intW2p_moll_support (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {ψ : Vec d → ℝ} :
    Function.support (intW2p_moll δ hδ n ψ) ⊆
      Metric.ball (0 : Vec d) (δ / (n + 2)) + Function.support ψ := by
  refine (MeasureTheory.support_convolution_subset (μ := volume)
    (L := ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
  rw [(intW2p_bump δ hδ n).support_normed_eq]
  exact Set.Subset.rfl

theorem intW2p_moll_fderiv (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (x : Vec d) (i : Fin d) :
    fderiv ℝ (intW2p_moll δ hδ n ψ) x (basisVec i) =
      intW2p_moll δ hδ n (fun y ↦ fderiv ℝ ψ y (basisVec i)) x := by
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (intW2p_normed_locInt δ hδ n) hψ x
  have h' : HasFDerivAt (intW2p_moll δ hδ n ψ) _ x := h
  rw [h'.fderiv]
  exact convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (intW2p_normed_locInt δ hδ n) (hc.fderiv (𝕜 := ℝ)) (hψ.continuous_fderiv one_ne_zero) x
    (basisVec i)

theorem intW2p_moll_tendsto (δ : ℝ) (hδ : 0 < δ) {ψ : Vec d → ℝ} (hψ : Continuous ψ) (x : Vec d) :
    Tendsto (fun n ↦ intW2p_moll δ hδ n ψ x) atTop (𝓝 (ψ x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous (intW2p_tendsto_rOut δ hδ) hψ x

theorem intW2p_moll_bound (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {ψ : Vec d → ℝ} (hψ : Continuous ψ)
    {C : ℝ} (hC : ∀ x, |ψ x| ≤ C) (x : Vec d) : |intW2p_moll δ hδ n ψ x| ≤ 3 * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h := (intW2p_bump δ hδ n).dist_normed_convolution_le (μ := volume) (x₀ := x)
    (g := ψ) (ε := 2 * C) hψ.aestronglyMeasurable (fun y _ ↦ by
      rw [Real.dist_eq]
      calc |ψ y - ψ x| ≤ |ψ y| + |ψ x| := abs_sub _ _
        _ ≤ 2 * C := by linarith only [hC y, hC x])
  have h2 : |intW2p_moll δ hδ n ψ x| ≤ |intW2p_moll δ hδ n ψ x - ψ x| + |ψ x| := by
    have := abs_add_le (intW2p_moll δ hδ n ψ x - ψ x) (ψ x)
    simpa only [sub_add_cancel] using this
  rw [Real.dist_eq] at h
  have h3 : intW2p_moll δ hδ n ψ x = ((intW2p_bump δ hδ n).normed volume ⋆[
      ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) x := rfl
  rw [h3] at h2 ⊢
  rw [h3] at *
  linarith only [h, h2, hC x]


theorem intW2p_moll_zero_off (δ : ℝ) (hδ : 0 < δ) (n : ℕ) {θ : Vec d → ℝ} {S : Set (Vec d)}
    (hS : Function.support θ ⊆ S) {x : Vec d} (hx : x ∉ Metric.cthickening (δ / 2) S) :
    intW2p_moll δ hδ n θ x = 0 := by
  by_contra h
  have hmem := intW2p_moll_support δ hδ n (Function.mem_support.mpr h)
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hmem
  apply hx
  refine Metric.mem_cthickening_of_dist_le (y + z) z (δ / 2) S (hS hz) ?_
  rw [dist_eq_norm, add_sub_cancel_right]
  have h1 : ‖y‖ < δ / (n + 2) := by simpa only [mem_ball_zero_iff] using hy
  have h2 : δ / ((n : ℝ) + 2) ≤ δ / 2 := by
    refine div_le_div_of_nonneg_left hδ.le (by norm_num) ?_
    linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith only [h1, h2]

/-- Dominated convergence for the mollified test functions. -/
theorem intW2p_tendsto_integral {U : Set (Vec d)} {w : Vec d → ℝ}
    (hw : LocallyIntegrableOn w U) {θ : Vec d → ℝ} (hθ : Continuous θ) {S : Set (Vec d)}
    (hSc : IsCompact S) {δ : ℝ} (hδ : 0 < δ) (hSU : Metric.cthickening (δ / 2) S ⊆ U)
    (hθS : Function.support θ ⊆ S) :
    Tendsto (fun n ↦ ∫ x in U, w x * intW2p_moll δ hδ n θ x) atTop
      (𝓝 (∫ x in U, w x * θ x)) := by
  have hK : IsCompact (Metric.cthickening (δ / 2) S) := hSc.cthickening
  have hθc : HasCompactSupport θ :=
    HasCompactSupport.of_support_subset_isCompact hSc hθS
  obtain ⟨C, hC'⟩ := hθc.exists_bound_of_continuous hθ
  have hC : ∀ x, |θ x| ≤ C := fun x ↦ by simpa only [Real.norm_eq_abs] using hC' x
  have hwi : IntegrableOn w (Metric.cthickening (δ / 2) S) volume :=
    hw.integrableOn_compact_subset hSU hK
  have hwi' : Integrable w (volume.restrict (Metric.cthickening (δ / 2) S)) := hwi
  refine tendsto_integral_of_dominated_convergence
    ((Metric.cthickening (δ / 2) S).indicator (fun x ↦ 3 * C * ‖w x‖)) ?_ ?_ ?_ ?_
  · intro n
    exact hw.aestronglyMeasurable.mul
      (intW2p_moll_contDiff δ hδ n hθ).continuous.aestronglyMeasurable
  · rw [integrable_indicator_iff hK.isClosed.measurableSet]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hK.isClosed.measurableSet, Set.inter_eq_left.mpr hSU]
    exact (hwi'.norm.const_mul _)
  · intro n
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ Metric.cthickening (δ / 2) S
    · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm (3 * C)]
      exact mul_le_mul_of_nonneg_left (intW2p_moll_bound δ hδ n hθ hC x) (abs_nonneg _)
    · rw [intW2p_moll_zero_off δ hδ n hθS hx, Set.indicator_of_notMem hx]
      simp
  · refine Eventually.of_forall fun x ↦ ?_
    exact (intW2p_moll_tendsto δ hδ hθ x).const_mul (w x)


/-- **Integration by parts against `C¹` compactly supported tests.** -/
theorem intW2p_ibp_c1 {U : Set (Vec d)} (hU : IsOpen U) {w g' : Vec d → ℝ} {i : Fin d}
    (hw : LocallyIntegrableOn w U) (hg : LocallyIntegrableOn g' U)
    (hweak : HasWeakPartialDerivOn U i w g') {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U) :
    ∫ x in U, w x * fderiv ℝ ψ x (basisVec i) = -∫ x in U, g' x * ψ x := by
  obtain ⟨δ, hδ, hth⟩ := hc.isCompact.exists_thickening_subset_open hU hs
  have hSU : Metric.cthickening (δ / 2) (tsupport ψ) ⊆ U :=
    (Metric.cthickening_subset_thickening' hδ (half_lt_self hδ) _).trans hth
  have hψc : Continuous ψ := hψ.continuous
  have hdc : Continuous fun y ↦ fderiv ℝ ψ y (basisVec i) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsd : Function.support (fun y ↦ fderiv ℝ ψ y (basisVec i)) ⊆ tsupport ψ := by
    intro y hy
    by_contra hyn
    apply hy
    simp only [fderiv_of_notMem_tsupport ℝ hyn, zero_apply]
  have h1 := intW2p_tendsto_integral hw hdc hc.isCompact hδ hSU hsd
  have h2 := intW2p_tendsto_integral hg hψc hc.isCompact hδ hSU subset_closure
  have h3 : ∀ n, ∫ x in U, w x * intW2p_moll δ hδ n (fun y ↦ fderiv ℝ ψ y (basisVec i)) x =
      -∫ x in U, g' x * intW2p_moll δ hδ n ψ x := fun n ↦ by
    have hsub : tsupport (intW2p_moll δ hδ n ψ) ⊆ U := by
      refine (closure_minimal ?_ Metric.isClosed_cthickening).trans hSU
      intro x hx
      by_contra hxn
      exact hx (intW2p_moll_zero_off δ hδ n (subset_closure) hxn)
    have := hweak _ (intW2p_moll_contDiff δ hδ n hψc) (intW2p_moll_compact δ hδ n hc) hsub
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [intW2p_moll_fderiv δ hδ n hψ hc x i]
  exact tendsto_nhds_unique h1 ((h2.neg).congr fun n ↦ (h3 n).symm)

end SuperdiffusionCLT.Section8
