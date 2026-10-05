/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareH
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareG
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlueH

/-!
# Poincare inequalities: affine images of shear preimages

The affine map `G w = s w + x₀` carries the shear preimage `{y | shear e Ψ y ∈ H}` to the shear
preimage `{y | shear e Ψ' y ∈ G '' H}` with `Ψ' z = s Ψ(s⁻¹ (z - P x₀))`, which has the same slope
bound as `Ψ` (`Section7.a10_affine_shear_preimage`, `Section7.a10_fderiv_PsiAff`), and `G '' H` is a
star-ball domain with the same ratio `D / s` (`Section7.a10_isStarBallDomain_affine`).
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The shear function of the affinely rescaled domain: `z ↦ s Ψ(s⁻¹ (z - P x₀))`. -/
noncomputable def a10_PsiAff (e : Vec d) (Ψ : Vec d → ℝ) (s : ℝ) (x₀ : Vec d) (z : Vec d) : ℝ :=
  s * Ψ (s⁻¹ • (z - (x₀ - vecDot e x₀ • e)))

theorem a10_contDiff_PsiAff (e : Vec d) {Ψ : Vec d → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (s : ℝ)
    (x₀ : Vec d) : ContDiff ℝ (⊤ : ℕ∞) (a10_PsiAff e Ψ s x₀) := by
  unfold a10_PsiAff
  exact contDiff_const.mul (hΨ.comp ((contDiff_id.sub contDiff_const).const_smul _))

theorem a10_fderiv_PsiAff (e : Vec d) {Ψ : Vec d → ℝ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) {s : ℝ}
    (hs : s ≠ 0) (x₀ z : Vec d) :
    fderiv ℝ (a10_PsiAff e Ψ s x₀) z =
      fderiv ℝ Ψ (s⁻¹ • (z - (x₀ - vecDot e x₀ • e))) := by
  set p : Vec d := x₀ - vecDot e x₀ • e with hp
  have hg : HasFDerivAt (fun z : Vec d => s⁻¹ • (z - p)) (s⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) z :=
    ((hasFDerivAt_id z).sub_const p).const_smul s⁻¹
  have h1 := ((hΨ.differentiable (by simp)) (s⁻¹ • (z - p))).hasFDerivAt.comp z hg
  have h2 := h1.const_mul s
  have h3 : fderiv ℝ (a10_PsiAff e Ψ s x₀) z =
      s • ((fderiv ℝ Ψ (s⁻¹ • (z - p))).comp (s⁻¹ • ContinuousLinearMap.id ℝ (Vec d))) :=
    h2.fderiv
  rw [h3]
  ext v
  simp [smul_smul, hs]

theorem a10_shear_PsiAff {e : Vec d} (Ψ : Vec d → ℝ) {s : ℝ}
    (hs : s ≠ 0) (x₀ w : Vec d) :
    shear e (a10_PsiAff e Ψ s x₀) (g1c_G s x₀ w) = g1c_G s x₀ (shear e Ψ w) := by
  unfold shear a10_PsiAff g1c_G
  have hdot : vecDot e (s • w + x₀) = s * vecDot e w + vecDot e x₀ := by
    simpa using g1b_vecDot_comb e w x₀ s 1
  have hP : (s • w + x₀) - vecDot e (s • w + x₀) • e - (x₀ - vecDot e x₀ • e) =
      s • (w - vecDot e w • e) := by
    rw [hdot]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hP, smul_smul, inv_mul_cancel₀ hs, one_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem a10_affine_shear_preimage {e : Vec d} (Ψ : Vec d → ℝ) {s : ℝ}
    (hs : s ≠ 0) (x₀ : Vec d) (H : Set (Vec d)) :
    g1c_G s x₀ '' (shear e Ψ ⁻¹' H) = shear e (a10_PsiAff e Ψ s x₀) ⁻¹' (g1c_G s x₀ '' H) := by
  ext y
  rw [Set.mem_preimage]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [a10_shear_PsiAff Ψ hs]
    exact ⟨_, hw, rfl⟩
  · intro hy
    obtain ⟨h1, hh1, hh⟩ := hy
    refine ⟨g1c_F s x₀ y, ?_, g1c_G_F hs x₀ y⟩
    rw [Set.mem_preimage]
    have : g1c_G s x₀ (shear e Ψ (g1c_F s x₀ y)) = g1c_G s x₀ h1 := by
      rw [← a10_shear_PsiAff Ψ hs, g1c_G_F hs, ← hh]
    have hinj : shear e Ψ (g1c_F s x₀ y) = h1 := by
      unfold g1c_G at this
      have := add_right_cancel this
      exact smul_right_injective (Vec d) hs this
    rw [hinj]
    exact hh1

theorem a10_isStarBallDomain_affine {H : Set (Vec d)} {x0 : Vec d} {s0 D : ℝ}
    (hH : IsStarBallDomain H x0 s0 D) {s : ℝ} (hs : 0 < s) (x₀ : Vec d) :
    IsStarBallDomain (g1c_G s x₀ '' H) (g1c_G s x₀ x0) (s * s0) (s * D) := by
  obtain ⟨hHo, hs0, hBH, hstar, hdiam⟩ := hH
  have hs' : s ≠ 0 := hs.ne'
  refine ⟨?_, by positivity, ?_, ?_, ?_⟩
  · exact (g1c_homeoG hs' x₀).isOpenMap _ hHo
  · intro y hy
    refine ⟨g1c_F s x₀ y, hBH ?_, g1c_G_F hs' x₀ y⟩
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    have : g1c_F s x₀ y - x0 = s⁻¹ • (y - g1c_G s x₀ x0) := by
      unfold g1c_F g1c_G
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      field_simp
      ring
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
    calc s⁻¹ * ‖y - g1c_G s x₀ x0‖ < s⁻¹ * (s * s0) := by gcongr
      _ = s0 := by field_simp
  · rintro _ ⟨x1, hx1, rfl⟩ b hb t ht
    have hb' : g1c_F s x₀ b ∈ Metric.ball x0 s0 := by
      rw [Metric.mem_ball, dist_eq_norm] at hb ⊢
      have : g1c_F s x₀ b - x0 = s⁻¹ • (b - g1c_G s x₀ x0) := by
        unfold g1c_F g1c_G
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
        field_simp
        ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
      calc s⁻¹ * ‖b - g1c_G s x₀ x0‖ < s⁻¹ * (s * s0) := by gcongr
        _ = s0 := by field_simp
    refine ⟨(1 - t) • x1 + t • g1c_F s x₀ b, hstar x1 hx1 _ hb' t ht, ?_⟩
    unfold g1c_G g1c_F
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    field_simp
    ring
  · rintro _ ⟨x1, hx1, rfl⟩ _ ⟨y1, hy1, rfl⟩
    have : g1c_G s x₀ x1 - g1c_G s x₀ y1 = s • (x1 - y1) := by
      unfold g1c_G
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left (hdiam x1 hx1 y1 hy1) hs.le

end SuperdiffusionCLT.Section7
