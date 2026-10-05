/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.UniformC

/-!
# Global `W^{1,p}` estimate: the boundary local estimate in unnormalized norms
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The scale-normalized local estimate at a boundary point, in unnormalized norms. -/
theorem p13_bdy_local [NeZero d] (hd : 2 ≤ d) {P : ℝ} (hP : 2 ≤ P) (M₁ : ℝ) :
    ∃ ε C K : ℝ, 0 < ε ∧ 0 < C ∧ 1 ≤ K ∧
      ∀ (U : Set (Vec d)) (e : Vec d) (ψ : Vec d → ℝ) (x₀ : Vec d) (r M₂ : ℝ) (m : ℤ),
        IsOpen U → vecNormSq e = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) →
        (∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) →
        vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e) →
        (∀ y ∈ Metric.ball x₀ r, (y ∈ U ↔ vecDot e y < ψ (y - vecDot e y • e))) →
        flattenLipConst d M₁ M₂ * (3 : ℝ) ^ m ≤ ε → K * (3 : ℝ) ^ m ≤ r →
        ∀ (φ : H10Function U) (F : Vec d → Vec d),
          IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function (fun _ => 0) F →
          MemLp F (ENNReal.ofReal P) (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) →
          eLpNorm φ.toH1Function.grad (ENNReal.ofReal P)
              (volume.restrict (U ∩ Metric.ball x₀ ((3 : ℝ) ^ m / (4 * K)))) ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal ((((3 : ℝ) ^ m) ^ d)⁻¹) ^ (1 / 2 - 1 / P : ℝ) *
                    eLpNorm φ.toH1Function.grad 2
                      (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) +
                  ENNReal.ofReal ((((3 : ℝ) ^ m) ^ d)⁻¹) ^ (1 / 2 - 1 / P : ℝ) *
                    ENNReal.ofReal (((3 : ℝ) ^ m)⁻¹) *
                    eLpNorm φ.toH1Function.toFun 2
                      (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m))) +
                eLpNorm F (ENNReal.ofReal P)
                  (volume.restrict (U ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m)))) := by
  obtain ⟨ε, C, K, hε, hC, hK, H⟩ := localW1p_boundary hd hP M₁
  refine ⟨ε, C, K, hε, hC, hK, ?_⟩
  intro U e ψ x₀ r M₂ m hU he hψ hb1 hb2 hx₀ hch hE hKr φ F hw hF
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hP0 : 0 < P := by linarith only [hP]
  obtain ⟨-, hmain⟩ := H U e ψ x₀ r M₂ m hU he hψ hb1 hb2 hx₀ hch hE hKr φ (fun _ => 0) F hw
    (by simp) (by simp) hF
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓdef
  have h2 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by simp
  have hPr : (1 / ENNReal.ofReal P).toReal = 1 / P := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hP0.le, one_div]
  have hP2 : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
  have hz : eLpNorm (fun _ : Vec d => (0 : ℝ)) (ENNReal.ofReal (p12_pstar d P)) (p12_nmeas ℓ
      (U ∩ Metric.ball x₀ (K * ℓ))) = 0 := eLpNorm_zero
  rw [p13_nmeas_eLpNorm ℓ _ _ hP2 ENNReal.ofReal_ne_top, p13_nmeas_eLpNorm ℓ _ _ hP2 ENNReal.ofReal_ne_top,
    p13_nmeas_eLpNorm ℓ _ _ (by norm_num) (by norm_num),
    p13_nmeas_eLpNorm ℓ _ _ (by norm_num) (by norm_num), hz, hPr, h2] at hmain
  simp only [mul_zero, add_zero] at hmain
  exact p13_unscale hℓ hP hmain

end SuperdiffusionCLT.Section7
