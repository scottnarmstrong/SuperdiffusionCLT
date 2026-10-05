/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareJ
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareI

/-!
# Poincare inequalities: the boundary family

`Section7.a10_boundary_family_poincare`: for a uniformly `C^{1,1}` domain `U` and a boundary point
`x₀`, at every admissible scale `s` there is an intermediate domain `W` that agrees with `U` near
`x₀` and carries the mean-value Poincare inequality with the constant `CP * s`, where `CP`
depends only on `d` and `M₁`. The domain `W` is the affine image of a shear preimage of the model
domain, hence a shear preimage of a star-ball domain with `D / s = 24 (d + 1)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization

variable {d : ℕ}

theorem a10_boundary_family_poincare [NeZero d] (M₁ : ℝ) :
    ∃ c₀ c₁ c₂ c r' M₁' M₂' D' CP : ℝ, 0 < c₀ ∧ c₀ < c₁ ∧ c₁ < c₂ ∧ 0 < c ∧ 0 < r' ∧ 0 ≤ CP ∧
      ∀ (U : Set (Vec d)) (r M₂ D : ℝ), IsUniformC11Domain U r M₁ M₂ D →
        ∀ x₀ ∈ frontier U, ∀ s : ℝ, 0 < s → c₂ * s ≤ r → M₂ * s ≤ 1 →
        ∃ W : Set (Vec d),
          IsUniformC11Domain ((fun y => s⁻¹ • (y - x₀)) '' W) r' M₁' M₂' D' ∧
          IsUniformC11Domain W (s * r') M₁' (M₂' / s) (s * D') ∧
          U ∩ Metric.ball x₀ (c₁ * s) = W ∩ Metric.ball x₀ (c₁ * s) ∧
          W ⊆ U ∩ Metric.ball x₀ (c₂ * s) ∧
          frontier W ∩ Metric.ball x₀ (c₁ * s) ⊆ frontier U ∧
          (∀ y ∈ U ∩ Metric.ball x₀ (c₀ * s), ∀ q ∈ frontier W \ frontier U, c * s ≤ dist y q) ∧
          ∀ u : H1Function W,
            eLpNorm (fun x => u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal) 2
                (volume.restrict W) ≤
              ENNReal.ofReal (CP * s) * eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict W) := by
  obtain ⟨r', M₁', M₂', D', c₁, c₂, K, hr', hc₁, hc₁₂, hK0, hglue⟩ :=
    a10_glue_normalized (d := d) (M := max M₁ 0) (le_max_right _ _)
  refine ⟨c₁ / 2, c₁, c₂, c₁ / 2, r', M₁', M₂', D',
    Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + (24 * ((d : ℝ) + 1)) ^ d)) * 6 * (1 + 2 * d * K),
    by positivity, by linarith only [hc₁], hc₁₂, by positivity, hr', by positivity, ?_⟩
  intro U r M₂ D hU x₀ hx₀ s hs hcs hMs
  have hs0 : s ≠ 0 := hs.ne'
  obtain ⟨hopen, hr, -, hch⟩ := hU
  have hchart : HasC11ChartAt (g1c_F s x₀ '' U) (g1c_F s x₀ x₀) (s⁻¹ * r) M₁ (M₂ / s⁻¹) :=
    (hch x₀ hx₀).affine (inv_pos.2 hs) _
  rw [g1c_F_x₀] at hchart
  obtain ⟨e, ψ, he, hψ, hb1, hb2, hV⟩ := hchart
  set V : Set (Vec d) := g1c_F s x₀ '' U with hVdef
  have hopenV : IsOpen V :=
    (affineHomeo (inv_ne_zero hs0) (-(s⁻¹ • x₀))).isOpenMap U hopen
  have hfrV : (0 : Vec d) ∈ frontier V := by
    rw [hVdef, g1c_frontier_F hs0]
    exact ⟨x₀, hx₀, g1c_F_x₀ x₀⟩
  have hψ0 : ψ 0 = 0 := by
    have h := vecDot_eq_of_mem_frontier hopenV hψ.continuous hV hfrV
      (Metric.mem_ball_self (by positivity))
    have h0 : vecDot e (0 : Vec d) = 0 := by simp [vecDot]
    rw [h0, zero_smul, sub_zero] at h
    exact h.symm
  have hLip : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ 1 * ‖y - z‖ := fun y z => by
    refine (hb2 y z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [div_inv_eq_mul]
    linarith only [hMs]
  have hR : c₂ ≤ s⁻¹ * r := by
    rw [inv_mul_eq_div, le_div_iff₀ hs]
    exact hcs
  obtain ⟨W₀, hW₀, hset, hsub, hfr, Ψ, hΨ, hKΨ, hW₀eq⟩ := hglue V e ψ (s⁻¹ * r) he hψ
    (fun y => (hb1 y).trans (le_max_left _ _)) hLip hψ0 hR hV
  set W : Set (Vec d) := g1c_G s x₀ '' W₀ with hWdef
  have key : ∀ y, y ∈ U ↔ g1c_F s x₀ y ∈ V := fun y => by
    rw [hVdef, g1c_mem_image_F hs0, g1c_G_F hs0]
  have keyW : ∀ y, y ∈ W ↔ g1c_F s x₀ y ∈ W₀ := g1c_mem_image_G hs0 x₀ W₀
  have hfun : (fun y : Vec d => s⁻¹ • (y - x₀)) = g1c_F s x₀ := by
    funext y; rw [g1c_F_eq]
  refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun, hWdef, g1c_image_F_G hs0]
    exact hW₀
  · exact hW₀.affineImage hs x₀
  · ext y
    simp only [Set.mem_inter_iff]
    rw [key, keyW, g1c_mem_ball_F hs]
    have := Set.ext_iff.1 hset (g1c_F s x₀ y)
    simp only [Set.mem_inter_iff] at this
    exact this
  · intro y hy
    have h := hsub ((keyW y).1 hy)
    exact ⟨(key y).2 h.1, (g1c_mem_ball_F hs x₀ y).2 h.2⟩
  · rintro q ⟨hq, hqb⟩
    rw [hWdef, g1c_frontier_G hs0] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    have hFw : g1c_F s x₀ (g1c_G s x₀ w) = w := g1c_F_G hs0 x₀ w
    have hball : w ∈ Metric.ball (0 : Vec d) c₁ := by
      have := (g1c_mem_ball_F hs x₀ _).1 hqb
      rwa [hFw] at this
    have hwV := hfr ⟨hw, hball⟩
    rw [hVdef, g1c_frontier_F hs0] at hwV
    obtain ⟨u, hu, hFu⟩ := hwV
    have : u = g1c_G s x₀ w := by
      rw [← hFu, g1c_G_F hs0]
    rwa [← this]
  · intro y hy q hq
    by_contra hlt
    have hlt' : dist y q < c₁ / 2 * s := not_le.1 hlt
    have hq1 : q ∈ Metric.ball x₀ (c₁ * s) := by
      have h1 := dist_triangle q y x₀
      have h2 : dist y x₀ < c₁ / 2 * s := hy.2
      rw [dist_comm q y] at h1
      rw [Metric.mem_ball]
      linarith only [h1, h2, hlt']
    have hq2 : q ∈ frontier W ∩ Metric.ball x₀ (c₁ * s) := ⟨hq.1, hq1⟩
    have hfrU : frontier W ∩ Metric.ball x₀ (c₁ * s) ⊆ frontier U := by
      rintro q' ⟨hq', hqb'⟩
      rw [hWdef, g1c_frontier_G hs0] at hq'
      obtain ⟨w, hw, rfl⟩ := hq'
      have hball : w ∈ Metric.ball (0 : Vec d) c₁ := by
        have := (g1c_mem_ball_F hs x₀ _).1 hqb'
        rwa [g1c_F_G hs0] at this
      have hwV := hfr ⟨hw, hball⟩
      rw [hVdef, g1c_frontier_F hs0] at hwV
      obtain ⟨u, hu, hFu⟩ := hwV
      have : u = g1c_G s x₀ w := by
        rw [← hFu, g1c_G_F hs0]
      rwa [← this]
    exact hq.2 (hfrU hq2)

  · intro u
    have hW1 : W = shear e (a10_PsiAff e Ψ s x₀) ⁻¹' (g1c_G s x₀ '' g1b_H e 1 1) := by
      rw [hWdef, hW₀eq, a10_affine_shear_preimage Ψ hs0]
    have hstarH := a10_isStarBallDomain_affine (a10_isStarBallDomain_H he) hs x₀
    have hKt : ∀ z, ‖fderiv ℝ (a10_PsiAff e Ψ s x₀) z‖ ≤ K := fun z => by
      rw [a10_fderiv_PsiAff e hΨ hs0 x₀ z]
      exact hKΨ _
    have hP := a10_poincare_shear hstarH he (a10_contDiff_PsiAff e hΨ s x₀) hKt hW1 u
    refine hP.trans (le_of_eq ?_)
    have hr : (s * 6) / (s * (1 / (4 * ((d : ℝ) + 1)))) = 24 * ((d : ℝ) + 1) := by
      field_simp
      ring
    rw [hr]
    congr 2
    ring

end SuperdiffusionCLT.Section7
