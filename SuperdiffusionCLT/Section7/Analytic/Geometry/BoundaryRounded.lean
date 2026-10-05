/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# Pulling a uniformly `C^{1,1}` domain back through a graph shear

Let `e` be a unit vector, `P y = y - ⟨e,y⟩ e`, and `Ψ` a smooth function on the whole space with
bounded gradient and Lipschitz gradient. The shear `T y = y - Ψ(P y) e` is a bi-Lipschitz
homeomorphism preserving `P`. For a domain `H` whose frontier charts are of two kinds,

* near the cylinder `‖P y‖ < ρ + δ`: graph charts in the direction `±e` (these transform
  explicitly: the graph function `g` becomes `g ± Ψ`);
* away from it, where `Ψ` is the constant `c` and `T` is a translation: arbitrary charts
  (these are translated),

the preimage `T⁻¹ H` is a uniformly `C^{1,1}` domain.

* `Section7.g1b_ChartDir`: a chart with a prescribed direction.
* `Section7.g1b_chartDir_shear`: transport of a chart with direction `ε e` (`ε = ±1`).
* `Section7.g1b_isUniformC11Domain_shear_preimage`: the assembly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- A quantitative `C^{1,1}` chart whose direction is the prescribed unit vector `e`. -/
def g1b_ChartDir (U : Set (Vec d)) (x : Vec d) (r M₁ M₂ : ℝ) (e : Vec d) : Prop :=
  vecNormSq e = 1 ∧ ∃ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) ∧
    (∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) ∧
    ∀ y ∈ Metric.ball x r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))

theorem g1b_ChartDir.hasC11ChartAt {U : Set (Vec d)} {x : Vec d} {r M₁ M₂ : ℝ} {e : Vec d}
    (h : g1b_ChartDir U x r M₁ M₂ e) : HasC11ChartAt U x r M₁ M₂ := by
  obtain ⟨he, ψ, hψ, hb1, hb2, hU⟩ := h
  exact ⟨e, ψ, he, hψ, hb1, hb2, hU⟩

theorem g1b_vecDot_smul (ε : ℝ) (e y : Vec d) : vecDot (ε • e) y = ε * vecDot e y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g1b_proj_smul {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (e y : Vec d) :
    y - vecDot (ε • e) y • (ε • e) = y - vecDot e y • e := by
  rw [g1b_vecDot_smul]
  rcases hε with rfl | rfl <;> simp

theorem g1b_vecNormSq_smul {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {e : Vec d} (he : vecNormSq e = 1) :
    vecNormSq (ε • e) = 1 := by
  have : vecDot (ε • e) (ε • e) = ε * (ε * vecDot e e) := by
    rw [g1b_vecDot_smul]
    simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : vecNormSq (ε • e) = vecDot (ε • e) (ε • e) := rfl
  have h3 : vecNormSq e = vecDot e e := rfl
  rw [h2, this, ← h3, he]
  rcases hε with rfl | rfl <;> norm_num

theorem g1b_shear_continuous {e : Vec d} {Ψ : Vec d → ℝ} (hΨ : Continuous Ψ) :
    Continuous (shear e Ψ) := by
  unfold shear
  have h1 : Continuous fun y : Vec d => vecDot e y := by unfold vecDot; fun_prop
  exact continuous_id.sub ((hΨ.comp (continuous_id.sub (h1.smul continuous_const))).smul
    continuous_const)

/-- The shear as a homeomorphism. -/
noncomputable def g1b_shearHomeo {e : Vec d} (he : vecNormSq e = 1) {Ψ : Vec d → ℝ}
    (hΨ : Continuous Ψ) : Vec d ≃ₜ Vec d where
  toFun := shear e Ψ
  invFun := shear e (-Ψ)
  left_inv := fun y => congrFun (shear_neg_left_inverse he Ψ) y
  right_inv := fun y => congrFun (shear_neg_right_inverse he Ψ) y
  continuous_toFun := g1b_shear_continuous hΨ
  continuous_invFun := g1b_shear_continuous hΨ.neg

/-- Lipschitz constant of the shear. -/
noncomputable def g1b_Lam (d : ℕ) (K : ℝ) : ℝ := 1 + (1 + d) * K

theorem g1b_Lam_pos {K : ℝ} (hK : 0 ≤ K) : 0 < g1b_Lam d K := by
  unfold g1b_Lam
  positivity

/-- Transport of a chart in the direction `ε e` through the shear. -/
theorem g1b_chartDir_shear {e : Vec d} (he : vecNormSq e = 1) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {Ψ : Vec d → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {K₁ K₂ : ℝ}
    (hK₁ : ∀ y, ‖fderiv ℝ Ψ y‖ ≤ K₁) (hK₂ : ∀ y z, ‖fderiv ℝ Ψ y - fderiv ℝ Ψ z‖ ≤ K₂ * ‖y - z‖)
    {H : Set (Vec d)} {p : Vec d} {r M₁ M₂ : ℝ}
    (h : g1b_ChartDir H (shear e Ψ p) r M₁ M₂ (ε • e)) :
    g1b_ChartDir {y | shear e Ψ y ∈ H} p (r / g1b_Lam d K₁) (M₁ + K₁) (M₂ + K₂) (ε • e) := by
  obtain ⟨-, g, hg, hb1, hb2, hH⟩ := h
  have hK0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ 0)
  have hε1 : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  have hdg : Differentiable ℝ g := hg.differentiable (by simp)
  have hdΨ : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (fun z => g z + ε * Ψ z) y = fderiv ℝ g y + ε • fderiv ℝ Ψ y := by
    intro y
    have := (hdg y).hasFDerivAt.add ((hdΨ y).hasFDerivAt.const_mul ε)
    exact this.fderiv
  refine ⟨g1b_vecNormSq_smul hε he, fun z => g z + ε * Ψ z, hg.add (contDiff_const.mul hΨ),
    fun y => ?_, fun y z => ?_, fun y hy => ?_⟩
  · rw [hfd]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hε1, one_mul]
    exact add_le_add (hb1 y) (hK₁ y)
  · rw [hfd, hfd]
    have : fderiv ℝ g y + ε • fderiv ℝ Ψ y - (fderiv ℝ g z + ε • fderiv ℝ Ψ z)
        = (fderiv ℝ g y - fderiv ℝ g z) + ε • (fderiv ℝ Ψ y - fderiv ℝ Ψ z) := by
      rw [smul_sub]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, hε1, one_mul]
    have := hb2 y z
    have := hK₂ y z
    linarith only [‹‖fderiv ℝ g y - fderiv ℝ g z‖ ≤ M₂ * ‖y - z‖›, this]
  · have hΛ := g1b_Lam_pos (d := d) hK0
    have hball : shear e Ψ y ∈ Metric.ball (shear e Ψ p) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 := norm_shear_sub_le he hK0 (abs_sub_le_of_fderiv_bound hΨ hK₁) y p
      have h2 : ‖y - p‖ < r / g1b_Lam d K₁ := by
        rwa [Metric.mem_ball, dist_eq_norm] at hy
      have h3 : ‖y - p‖ * g1b_Lam d K₁ < r := (lt_div_iff₀ hΛ).1 h2
      unfold g1b_Lam at h1 h3
      linarith only [h1, h3]
    have hdot : vecDot e (shear e Ψ y) = vecDot e y - Ψ (y - vecDot e y • e) := by
      unfold shear
      exact vecDot_sub_smul_self he y _
    show shear e Ψ y ∈ H ↔ _
    rw [hH _ hball, g1b_proj_smul hε, proj_shear he, g1b_proj_smul hε, g1b_vecDot_smul, hdot,
      g1b_vecDot_smul]
    constructor <;> intro h' <;> linarith only [h']

end SuperdiffusionCLT.Section7
