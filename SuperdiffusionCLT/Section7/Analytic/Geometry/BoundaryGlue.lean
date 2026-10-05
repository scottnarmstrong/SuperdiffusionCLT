/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.FlattenB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedJ

/-!
# Orthogonal preimages of uniformly `C^{1,1}` domains

For a matrix `A` with `A Aᵀ = 1`, the preimage `{y | A y ∈ H}` of a uniformly `C^{1,1}` domain
`H` is uniformly `C^{1,1}`, with data `(r / (d + 1), d M₁, d² M₂, d D)`. The constants depend on
`d` only, not on `A`. This is the rotation lemma used to make the data of the model domain
independent of its axis direction.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization Matrix

variable {d : ℕ}

theorem g1c_mul_eq_one {A : Mat d} (hA : A * Aᵀ = 1) : Aᵀ * A = 1 :=
  mul_eq_one_comm.1 hA

theorem g1c_dot_transpose (A : Mat d) (x w : Vec d) : (Aᵀ *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (A *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem g1c_vecDot_eq (x y : Vec d) : vecDot x y = x ⬝ᵥ y := rfl

theorem g1c_vecDot_transpose (A : Mat d) (x w : Vec d) :
    vecDot (Aᵀ *ᵥ x) w = vecDot x (A *ᵥ w) := by
  rw [g1c_vecDot_eq, g1c_vecDot_eq, g1c_dot_transpose]

/-- The continuous linear map of a matrix. -/
noncomputable def g1c_clm (A : Mat d) : Vec d →L[ℝ] Vec d :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

theorem g1c_clm_apply (A : Mat d) (y : Vec d) : g1c_clm A y = A *ᵥ y := rfl

theorem g1c_norm_clm_le {A : Mat d} (hA : A * Aᵀ = 1) : ‖g1c_clm A‖ ≤ d :=
  ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg d) fun v => by
    rw [g1c_clm_apply]
    exact flatten_norm_mulVec_le (flatten_abs_entry_le_one hA) v

theorem g1c_norm_mulVec_le {A : Mat d} (hA : A * Aᵀ = 1) (v : Vec d) : ‖A *ᵥ v‖ ≤ d * ‖v‖ :=
  flatten_norm_mulVec_le (flatten_abs_entry_le_one hA) v

theorem g1c_norm_mulVec_transpose_le {A : Mat d} (hA : A * Aᵀ = 1) (v : Vec d) :
    ‖Aᵀ *ᵥ v‖ ≤ d * ‖v‖ := by
  have h : Aᵀ * Aᵀᵀ = 1 := by rw [Matrix.transpose_transpose]; exact g1c_mul_eq_one hA
  exact flatten_norm_mulVec_le (flatten_abs_entry_le_one h) v

/-- The homeomorphism `y ↦ A y`. -/
noncomputable def g1c_homeo {A : Mat d} (hA : A * Aᵀ = 1) : Vec d ≃ₜ Vec d where
  toFun y := A *ᵥ y
  invFun y := Aᵀ *ᵥ y
  left_inv y := by
    show Aᵀ *ᵥ (A *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, g1c_mul_eq_one hA, Matrix.one_mulVec]
  right_inv y := by
    show A *ᵥ (Aᵀ *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  continuous_toFun := (g1c_clm A).continuous
  continuous_invFun := (g1c_clm Aᵀ).continuous

theorem g1c_vecNormSq_transpose {A : Mat d} (hA : A * Aᵀ = 1) {e : Vec d} (he : vecNormSq e = 1) :
    vecNormSq (Aᵀ *ᵥ e) = 1 := by
  unfold vecNormSq
  rw [g1c_vecDot_transpose, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  exact he

theorem g1c_proj_mulVec {A : Mat d} (hA : A * Aᵀ = 1) (e y : Vec d) :
    A *ᵥ (y - vecDot (Aᵀ *ᵥ e) y • (Aᵀ *ᵥ e)) = A *ᵥ y - vecDot e (A *ᵥ y) • e := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec,
    g1c_vecDot_transpose]

theorem g1c_chart_orth {A : Mat d} (hA : A * Aᵀ = 1) {H : Set (Vec d)} {p : Vec d}
    {r M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (h : HasC11ChartAt H (A *ᵥ p) r M₁ M₂) :
    HasC11ChartAt {y | A *ᵥ y ∈ H} p (r / (d + 1)) (d * M₁) (d ^ 2 * M₂) := by
  obtain ⟨e, ψ, he, hψ, hb1, hb2, hH⟩ := h
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (fun z => ψ (A *ᵥ z)) y = (fderiv ℝ ψ (A *ᵥ y)).comp (g1c_clm A) :=
    fun y => by
      have h1 : HasFDerivAt (fun z : Vec d => A *ᵥ z) (g1c_clm A) y :=
        (g1c_clm A).hasFDerivAt
      exact ((hdiff (A *ᵥ y)).hasFDerivAt.comp y h1).fderiv
  have hAcl := g1c_norm_clm_le hA
  refine ⟨Aᵀ *ᵥ e, fun z => ψ (A *ᵥ z), g1c_vecNormSq_transpose hA he, ?_, fun y => ?_,
    fun y z => ?_, fun y hy => ?_⟩
  · exact hψ.comp (g1c_clm A).contDiff
  · rw [hfd]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hb1 _) hAcl (norm_nonneg _) hM₁) |>.trans (le_of_eq (mul_comm _ _))
  · rw [hfd, hfd, ← ContinuousLinearMap.sub_comp]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hb2 (A *ᵥ y) (A *ᵥ z)
    rw [← Matrix.mulVec_sub] at h1
    have h2 := g1c_norm_mulVec_le hA (y - z)
    calc ‖fderiv ℝ ψ (A *ᵥ y) - fderiv ℝ ψ (A *ᵥ z)‖ * ‖g1c_clm A‖
        ≤ (M₂ * (d * ‖y - z‖)) * d :=
          mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hM₂)) hAcl (norm_nonneg _)
            (by positivity)
      _ = d ^ 2 * M₂ * ‖y - z‖ := by ring
  · have hball : A *ᵥ y ∈ Metric.ball (A *ᵥ p) r := by
      rw [Metric.mem_ball, dist_eq_norm, ← Matrix.mulVec_sub]
      have h2 := g1c_norm_mulVec_le hA (y - p)
      have h3 : ‖y - p‖ < r / (d + 1) := by rwa [Metric.mem_ball, dist_eq_norm] at hy
      have h4 : ‖y - p‖ * (d + 1) < r := (lt_div_iff₀ (by positivity)).1 h3
      have h5 : (d : ℝ) * ‖y - p‖ ≤ (d + 1) * ‖y - p‖ :=
        mul_le_mul_of_nonneg_right (by linarith only) (norm_nonneg _)
      linarith only [h2, h4, h5]
    show A *ᵥ y ∈ H ↔ vecDot (Aᵀ *ᵥ e) y < ψ (A *ᵥ (y - vecDot (Aᵀ *ᵥ e) y • (Aᵀ *ᵥ e)))
    rw [hH _ hball, g1c_proj_mulVec hA, g1c_vecDot_transpose]

/-- The orthogonal preimage of a uniformly `C^{1,1}` domain. -/
theorem g1c_isUniformC11Domain_orth {A : Mat d} (hA : A * Aᵀ = 1) {H : Set (Vec d)}
    {r M₁ M₂ D : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (h : IsUniformC11Domain H r M₁ M₂ D) :
    IsUniformC11Domain {y | A *ᵥ y ∈ H} (r / (d + 1)) (d * M₁) (d ^ 2 * M₂) (d * D) := by
  obtain ⟨hopen, hr, hD, hch⟩ := h
  refine ⟨hopen.preimage (g1c_clm A).continuous, div_pos hr (by positivity), fun y hy y' hy' => ?_,
    fun p hp => ?_⟩
  · have h1 := hD _ hy _ hy'
    have h2 : y - y' = Aᵀ *ᵥ (A *ᵥ y - A *ᵥ y') := by
      rw [← Matrix.mulVec_sub, Matrix.mulVec_mulVec, g1c_mul_eq_one hA, Matrix.one_mulVec]
    rw [h2]
    exact (g1c_norm_mulVec_transpose_le hA _).trans
      (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d))
  · have hq : A *ᵥ p ∈ frontier H := by
      have := (g1c_homeo hA).preimage_frontier H
      have h' : p ∈ frontier ((g1c_homeo hA) ⁻¹' H) := hp
      rw [← this] at h'
      exact h'
    exact g1c_chart_orth hA hM₁ hM₂ (hch _ hq)

end SuperdiffusionCLT.Section7
