/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import SuperdiffusionCLT.Section8.Brownian.HeatGenerator

/-!
# The maximum principle for functions vanishing at infinity

A twice continuously differentiable function vanishing at infinity with
`c w - ½ Δ w ≤ e` pointwise satisfies `w ≤ e / c`: the maximum is attained, and the Laplacian
is nonpositive at a maximum.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization Topology
open scoped ZeroAtInfty

variable {d : ℕ}

/-- At a global maximum, the second derivative along any direction is nonpositive. -/
theorem heatWitness_second_deriv_nonpos {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) {x : Vec d}
    (hmax : ∀ y, f y ≤ f x) (e : Vec d) : fderiv ℝ (fderiv ℝ f) x e e ≤ 0 := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf' : Differentiable ℝ (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (by norm_num) |>.differentiable (by norm_num)
  set φ : ℝ → ℝ := fun t ↦ f (x + t • e) with hφ
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ x + s • e) e t := fun t ↦ by
    simpa only [hasDerivAt_const_add_iff, id_eq, one_smul] using ((hasDerivAt_id t).smul_const e).const_add x
  have h1 : ∀ t, HasDerivAt φ (fderiv ℝ f (x + t • e) e) t := fun t ↦
    (hdf (x + t • e)).hasFDerivAt.comp_hasDerivAt t (hline t)
  have h1' : deriv φ = fun t ↦ fderiv ℝ f (x + t • e) e := funext fun t ↦ (h1 t).deriv
  have h2 : HasDerivAt (deriv φ) (fderiv ℝ (fderiv ℝ f) x e e) 0 := by
    rw [h1']
    have := ((hdf' (x + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0))
    have h3 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt (0 : ℝ) this
    rw [zero_smul, add_zero] at h3
    exact h3
  by_contra hneg
  push Not at hneg
  set a := fderiv ℝ (fderiv ℝ f) x e e with ha
  set ψ : ℝ → ℝ := fun t ↦ φ t - (a / 4) * t ^ 2 with hψ
  have hd0 : deriv φ 0 = 0 := by
    have hloc : IsLocalMax φ 0 := Filter.Eventually.of_forall fun t ↦ by
      simpa only [hφ, zero_smul, add_zero] using hmax (x + t • e)
    exact hloc.deriv_eq_zero
  have hψ1 : ∀ t, HasDerivAt ψ (deriv φ t - (a / 4) * (2 * t)) t := fun t ↦ by
    have := (h1 t).sub (((hasDerivAt_pow 2 t).const_mul (a / 4)))
    rw [← (h1 t).deriv] at this
    have e2 : deriv φ t - a / 4 * (((2 : ℕ) : ℝ) * t ^ (2 - 1)) = deriv φ t - a / 4 * (2 * t) := by
      norm_num
    rw [e2] at this
    exact this
  have hψ1' : deriv ψ = fun t ↦ deriv φ t - (a / 4) * (2 * t) := funext fun t ↦ (hψ1 t).deriv
  have hψ2 : HasDerivAt (deriv ψ) (a - (a / 4) * 2) 0 := by
    rw [hψ1']
    have := h2.sub (((hasDerivAt_id (0 : ℝ)).const_mul 2).const_mul (a / 4))
    have e2 : a - a / 4 * (2 * 1) = a - a / 4 * 2 := by norm_num
    rw [e2] at this
    exact this
  have hmin : IsLocalMin ψ 0 := by
    refine isLocalMin_of_deriv_deriv_pos ?_ ?_ (hψ1 0).continuousAt
    · rw [hψ2.deriv]; linarith only [hneg]
    · rw [(hψ1 0).deriv, hd0]; simp
  have hψ0 : ψ 0 = φ 0 := by simp [hψ]
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hmin
  have hr2 := hball (y := r / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith only [hr])]; linarith only [hr])
  have hφle : φ (r / 2) ≤ φ 0 := by simpa only [hφ, zero_smul, add_zero] using hmax (x + (r / 2) • e)
  simp only [hψ] at hr2 hψ0
  have : 0 < (a / 4) * (r / 2) ^ 2 := by positivity
  simp only [hφ] at hφle hr2 ⊢
  linarith only [hr2, hφle, this]

/-- At a global maximum the Laplacian is nonpositive. -/
theorem heatWitness_vecLaplacian_nonpos {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) {x : Vec d}
    (hmax : ∀ y, f y ≤ f x) : vecLaplacian f x ≤ 0 := by
  rw [vecLaplacian_eq_sum_fderiv]
  exact Finset.sum_nonpos fun i _ ↦ heatWitness_second_deriv_nonpos hf hmax _

/-- The Laplacian of a difference of two `C²` functions. -/
theorem heatWitness_vecLaplacian_sub {f g : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : Vec d) :
    vecLaplacian (fun y ↦ f y - g y) x = vecLaplacian f x - vecLaplacian g x := by
  unfold vecLaplacian
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (fun y ↦ f y - g y) = f - g from rfl,
    iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt]
  rfl

/-- The Laplacian of a negative. -/
theorem heatWitness_vecLaplacian_neg (f : Vec d → ℝ) (x : Vec d) :
    vecLaplacian (fun y ↦ -f y) x = - vecLaplacian f x := by
  unfold vecLaplacian
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show (fun y ↦ -f y) = -f from rfl, iteratedFDeriv_neg_apply]
  rfl

/-- **The maximum principle for `C²` functions vanishing at infinity.**  If `c w - ½ Δ w ≤ e`
pointwise, with `c > 0` and `e ≥ 0`, then `w ≤ e / c`. -/
theorem heatWitness_le_of_maxPrinciple {w : Vec d → ℝ} (hw : ContDiff ℝ 2 w)
    (h0 : Tendsto w (cocompact (Vec d)) (𝓝 0)) {c e : ℝ} (hc : 0 < c) (he : 0 ≤ e)
    (hineq : ∀ x, c * w x - 2⁻¹ * vecLaplacian w x ≤ e) : ∀ x, w x ≤ e / c := by
  intro x₁
  by_contra hlt
  push Not at hlt
  have hapos : 0 < w x₁ := lt_of_le_of_lt (div_nonneg he hc.le) hlt
  have hcont : Continuous w := hw.continuous
  set K : Set (Vec d) := {x | w x₁ ≤ w x} with hK
  have hKclosed : IsClosed K := isClosed_le continuous_const hcont
  have hev : ∀ᶠ x in cocompact (Vec d), w x < w x₁ := h0.eventually (gt_mem_nhds hapos)
  obtain ⟨t, ht, htc⟩ := Filter.mem_cocompact.mp hev
  have hKcompact : IsCompact K := by
    refine ht.of_isClosed_subset hKclosed fun x hx ↦ ?_
    by_contra hxt
    have h : w x < w x₁ := htc hxt
    have hx' : w x₁ ≤ w x := hx
    exact absurd hx' (not_le.mpr h)
  obtain ⟨x₀, hx₀K, hx₀⟩ := hKcompact.exists_isMaxOn ⟨x₁, (le_refl (w x₁) : w x₁ ≤ w x₁)⟩ hcont.continuousOn
  have hglob : ∀ y, w y ≤ w x₀ := fun y ↦ by
    by_cases hy : y ∈ K
    · exact hx₀ hy
    · exact le_trans (le_of_lt (not_le.mp hy)) hx₀K
  have hlap := heatWitness_vecLaplacian_nonpos hw hglob
  have h1 := hineq x₀
  have h2 : c * w x₀ ≤ e := by linarith only [h1, hlap]
  have h3 : w x₀ ≤ e / c := by rw [le_div_iff₀ hc]; linarith only [h2]
  have h4 : w x₁ ≤ w x₀ := hx₀K
  linarith only [h3, hlt, h4]

/-- **Comparison for `C₀` functions.**  If two `C²` functions in `C₀` satisfy
`|c (u - v) - ½ Δ (u - v)| ≤ e` pointwise, with `c > 0` and `e ≥ 0`, then
`‖u - v‖ ≤ e / c`. -/
theorem heatWitness_norm_sub_le (u v : C₀(Vec d, ℝ)) (hu : ContDiff ℝ 2 (⇑u))
    (hv : ContDiff ℝ 2 (⇑v)) {c e : ℝ} (hc : 0 < c) (he : 0 ≤ e)
    (hineq : ∀ x, |c * (u x - v x) - 2⁻¹ * (vecLaplacian (⇑u) x - vecLaplacian (⇑v) x)| ≤ e) :
    ‖u - v‖ ≤ e / c := by
  have hw : ContDiff ℝ 2 (fun y ↦ u y - v y) := hu.sub hv
  have hw0 : Tendsto (fun y ↦ u y - v y) (cocompact (Vec d)) (𝓝 0) := by
    simpa only [ContinuousMap.toFun_eq_coe, ZeroAtInftyContinuousMap.coe_toContinuousMap, sub_self] using u.zero_at_infty'.sub v.zero_at_infty'
  have hup := heatWitness_le_of_maxPrinciple hw hw0 hc he fun x ↦ by
    rw [heatWitness_vecLaplacian_sub hu hv]
    exact (le_abs_self _).trans (hineq x)
  have hnw : ContDiff ℝ 2 (fun y ↦ -(u y - v y)) := hw.neg
  have hn0 : Tendsto (fun y ↦ -(u y - v y)) (cocompact (Vec d)) (𝓝 0) := by
    simpa only [neg_sub, neg_zero] using hw0.neg
  have hdn := heatWitness_le_of_maxPrinciple hnw hn0 hc he fun x ↦ by
    rw [heatWitness_vecLaplacian_neg, heatWitness_vecLaplacian_sub hu hv]
    have := (neg_le_abs _).trans (hineq x)
    linarith only [this]
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le (div_nonneg he hc.le)]
  intro x
  have h1 := hup x
  have h2 := hdn x
  rw [Real.norm_eq_abs, abs_le]
  have : (u - v).toBCF x = u x - v x := rfl
  rw [this]
  constructor <;> linarith only [h1, h2]

end SuperdiffusionCLT.Section8.Brownian
