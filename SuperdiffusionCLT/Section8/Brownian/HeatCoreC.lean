/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import SuperdiffusionCLT.Section8.Brownian.HeatCoreB

/-!
# Density of smooth compactly supported functions in `C₀`, and the heat core

The smooth compactly supported functions are dense in `C₀(Vec d, ℝ)` in the supremum norm
(`heatCore_dense_smooth`): a `C₀` function is within `e` of its soft threshold at level `e`, which
is continuous with compact support, and a continuous compactly supported function is uniformly
approximated by a smooth one with no larger support.

Combined with `heatCore_resolvent_mem` this gives the core statement consumed by the invariance
principle: for every positive shift `mu`, the functions `mu f - ½ Δ f`, for `f` in the
differentiable class of the heat generator, are dense in `C₀(Vec d, ℝ)`
(`dense_smul_sub_half_laplacian_heatCore`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization MeasureTheory Topology
open MarkovProcess.Semigroup
open scoped ContDiff NNReal ZeroAtInfty

noncomputable section

section Density

variable {d : ℕ}

/-- The soft threshold of a real function at level `e`: it differs from the function by at most
`e` and vanishes where the function is at most `e` in absolute value. -/
def heatCore_threshold (e : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  f x - max (-e) (min e (f x))

theorem heatCore_continuous_threshold {e : ℝ} {f : Vec d → ℝ} (hf : Continuous f) :
    Continuous (heatCore_threshold e f) := by
  unfold heatCore_threshold
  fun_prop

theorem heatCore_abs_threshold_sub_le {e : ℝ} (he : 0 ≤ e) (f : Vec d → ℝ) (x : Vec d) :
    |heatCore_threshold e f x - f x| ≤ e := by
  unfold heatCore_threshold
  rw [abs_le]
  constructor
  · rcases le_total (f x) e with h | h
    · rcases le_total (-e) (f x) with h' | h'
      · rw [min_eq_right h, max_eq_right h']
        linarith only [he, h, h']
      · rw [min_eq_right (by linarith only [h', he]), max_eq_left h']
        linarith only [h', he]
    · rw [min_eq_left h, max_eq_right (by linarith only [he])]
      linarith only [he]
  · rcases le_total (f x) e with h | h
    · rcases le_total (-e) (f x) with h' | h'
      · rw [min_eq_right h, max_eq_right h']
        linarith only [he, h, h']
      · rw [min_eq_right (by linarith only [h', he]), max_eq_left h']
        linarith only [h', he]
    · rw [min_eq_left h, max_eq_right (by linarith only [he])]
      linarith only [h, he]

theorem heatCore_threshold_eq_zero {e : ℝ} {f : Vec d → ℝ} {x : Vec d} (h : |f x| ≤ e) :
    heatCore_threshold e f x = 0 := by
  unfold heatCore_threshold
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]
  exact sub_self _

theorem heatCore_hasCompactSupport_threshold (f : C₀(Vec d, ℝ)) {e : ℝ} (he : 0 < e) :
    HasCompactSupport (heatCore_threshold e (f : Vec d → ℝ)) := by
  have hev : ∀ᶠ x in cocompact (Vec d), |f x| < e := by
    have := f.zero_at_infty'
    exact (this.eventually (Metric.ball_mem_nhds 0 he)).mono fun x hx ↦ by
      simpa only [ContinuousMap.toFun_eq_coe, ZeroAtInftyContinuousMap.coe_toContinuousMap, dist_zero_right, Real.norm_eq_abs] using hx
  obtain ⟨t, ht, htc⟩ := Filter.mem_cocompact.mp hev
  refine HasCompactSupport.intro (K := {x | e ≤ |f x|}) ?_ fun x hx ↦ ?_
  · refine ht.of_isClosed_subset (isClosed_le continuous_const (f.continuous.abs)) fun x hx ↦ ?_
    by_contra hxt
    have h1 : |f x| < e := htc hxt
    exact absurd h1 (not_lt.mpr hx)
  · exact heatCore_threshold_eq_zero (not_le.mp hx).le

/-- A smooth compactly supported function within `e` of the soft threshold of `f`, hence within
`2 e` of `f`, as a `C₀` function. -/
theorem heatCore_exists_smooth_close (f : C₀(Vec d, ℝ)) {e : ℝ} (he : 0 < e) :
    ∃ g : C₀(Vec d, ℝ), ContDiff ℝ ∞ (g : Vec d → ℝ) ∧ HasCompactSupport (g : Vec d → ℝ) ∧
      ‖g - f‖ ≤ 2 * e := by
  have hcont : Continuous (heatCore_threshold e (f : Vec d → ℝ)) :=
    heatCore_continuous_threshold f.continuous
  obtain ⟨g, hg, hdist, hsupp⟩ := hcont.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ ↦ e) continuous_const (fun _ ↦ he)
  have hcs : HasCompactSupport g :=
    (heatCore_hasCompactSupport_threshold f he).mono' (hsupp.trans (subset_tsupport _))
  let G : C₀(Vec d, ℝ) := ⟨⟨g, hg.continuous⟩, hcs.is_zero_at_infty⟩
  refine ⟨G, hg, hcs, ?_⟩
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x ↦ ?_
  have h1 := hdist x
  have h2 := heatCore_abs_threshold_sub_le he.le (f : Vec d → ℝ) x
  rw [Real.dist_eq] at h1
  change |g x - f x| ≤ 2 * e
  calc |g x - f x| = |(g x - heatCore_threshold e (f : Vec d → ℝ) x)
        + (heatCore_threshold e (f : Vec d → ℝ) x - f x)| := by ring_nf
    _ ≤ |g x - heatCore_threshold e (f : Vec d → ℝ) x|
        + |heatCore_threshold e (f : Vec d → ℝ) x - f x| := abs_add_le _ _
    _ ≤ 2 * e := by linarith only [h1, h2]

/-- **Smooth compactly supported functions are dense in `C₀(Vec d, ℝ)`.** -/
theorem heatCore_dense_smooth (d : ℕ) :
    Dense {g : C₀(Vec d, ℝ) | ContDiff ℝ ∞ (g : Vec d → ℝ) ∧
      HasCompactSupport (g : Vec d → ℝ)} := by
  rw [Metric.dense_iff]
  intro f r hr
  obtain ⟨g, hg, hc, hn⟩ := heatCore_exists_smooth_close f (e := r / 4) (by positivity)
  refine ⟨g, ?_, hg, hc⟩
  rw [Metric.mem_ball, dist_eq_norm]
  linarith only [hn, hr]

/-- **The heat core.**  For every positive shift `mu`, the functions `mu f - ½ Δ f`, for `f` in
the differentiable class of the heat generator (`C²`, in `C₀`, with second derivative vanishing
at infinity), are dense in `C₀(Vec d, ℝ)` in the supremum norm.  This is the core hypothesis for
the differentiable class `Convergence.heatCore`. -/
theorem dense_smul_sub_half_laplacian_heatCore (d : ℕ) (mu : PositiveShift) :
    Dense {g : C₀(Vec d, ℝ) | ∃ f : Convergence.heatCore d,
      (mu : ℝ) • (f : C₀(Vec d, ℝ)) - (2 : ℝ)⁻¹ • Convergence.heatCoreLaplacian f = g} :=
  Convergence.dense_smul_sub_heatCoreLaplacian_of_resolvent_mem mu (heatCore_dense_smooth d)
    fun g hg ↦ heatCore_resolvent_mem mu g hg.1 hg.2

/-- Witness: the statement is instantiated in dimension two at the shift one. -/
example : Dense {g : C₀(Vec 2, ℝ) | ∃ f : Convergence.heatCore 2,
    ((1 : ℝ)) • (f : C₀(Vec 2, ℝ)) - (2 : ℝ)⁻¹ • Convergence.heatCoreLaplacian f = g} :=
  dense_smul_sub_half_laplacian_heatCore 2 ⟨1, Set.mem_Ioi.mpr one_pos⟩

end Density

end

end SuperdiffusionCLT.Section8.Brownian
