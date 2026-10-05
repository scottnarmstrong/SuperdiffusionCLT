/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryGlue

/-!
# The model domain in every axis direction, with uniform data

`Section7.g1c_exists_uniform_H_dir`: the model domains `g1b_H e a h`, `e` a unit vector, are
uniformly `C^{1,1}` with data `(r, M₁, M₂, D)` independent of `e`: each is the orthogonal
preimage (under a Householder reflection) of the model domain of a fixed axis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization Matrix

variable {d : ℕ}

theorem g1c_uniform_mono {U : Set (Vec d)} {r M₁ M₂ D M₁' M₂' : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (h1 : M₁ ≤ M₁') (h2 : M₂ ≤ M₂') :
    IsUniformC11Domain U r M₁' M₂' D :=
  ⟨h.1, h.2.1, h.2.2.1, fun x hx => (h.2.2.2 x hx).mono le_rfl h1 h2⟩

theorem g1c_vecDot_mulVec_orth {A : Mat d} (hA : A * Aᵀ = 1) (x y : Vec d) :
    vecDot (A *ᵥ x) (A *ᵥ y) = vecDot x y := by
  have := g1c_vecDot_transpose Aᵀ x (A *ᵥ y)
  rw [Matrix.transpose_transpose, Matrix.mulVec_mulVec, g1c_mul_eq_one hA, Matrix.one_mulVec] at this
  exact this

theorem g1c_Q_orth {e e₀ : Vec d} (he : vecNormSq e = 1) (he₀ : vecNormSq e₀ = 1) (a h : ℝ)
    (y : Vec d) :
    g1b_Q e a h y = g1b_Q e₀ a h (flattenHouseholder e e₀ *ᵥ y) := by
  set A := flattenHouseholder e e₀ with hAdef
  have hA : A * Aᵀ = 1 := flattenHouseholder_mul_transpose e e₀
  have hdot : vecDot e₀ (A *ᵥ y) = vecDot e y := by
    have := dotProduct_flattenHouseholder_mulVec (n := e) (u := e₀) he he₀ y
    exact this
  have hAe : A *ᵥ e = e₀ := flattenHouseholder_mulVec he he₀
  have hproj : A *ᵥ y - vecDot e₀ (A *ᵥ y) • e₀ = A *ᵥ (y - vecDot e y • e) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAe, hdot]
  unfold g1b_Q g1b_u g1b_v
  rw [hproj, hdot]
  unfold vecNormSq
  rw [g1c_vecDot_mulVec_orth hA]

theorem g1c_H_eq_preimage {e e₀ : Vec d} (he : vecNormSq e = 1) (he₀ : vecNormSq e₀ = 1)
    (a h : ℝ) :
    g1b_H e a h = {y | flattenHouseholder e e₀ *ᵥ y ∈ g1b_H e₀ a h} := by
  ext y
  show g1b_Q e a h y < 1 ↔ g1b_Q e₀ a h _ < 1
  rw [g1c_Q_orth he he₀]

theorem g1c_vecNormSq_single [NeZero d] : vecNormSq (Pi.single (0 : Fin d) (1 : ℝ)) = 1 := by
  unfold vecNormSq vecDot
  simp [Pi.single_apply]

/-- Uniform data of the model domain, independent of the axis direction. -/
theorem g1c_exists_uniform_H_dir [NeZero d] {a h : ℝ} (ha : 0 < a) (hh : 0 < h) :
    ∃ r M₁ M₂ D : ℝ, 0 ≤ M₁ ∧ 0 ≤ M₂ ∧ 0 < r ∧
      ∀ e : Vec d, vecNormSq e = 1 → IsUniformC11Domain (g1b_H e a h) r M₁ M₂ D := by
  obtain ⟨r, M₁, M₂, D, hH⟩ := g1b_exists_uniform_H (g1c_vecNormSq_single (d := d)) ha hh
  have hH' := g1c_uniform_mono hH (le_max_left M₁ 0) (le_max_left M₂ 0)
  refine ⟨r / ((d : ℝ) + 1), d * max M₁ 0, d ^ 2 * max M₂ 0, d * D, mul_nonneg (Nat.cast_nonneg d) (le_max_right _ _),
    mul_nonneg (sq_nonneg _) (le_max_right _ _), div_pos hH.2.1 (by positivity), fun e he => ?_⟩
  rw [g1c_H_eq_preimage he (g1c_vecNormSq_single (d := d))]
  exact g1c_isUniformC11Domain_orth (flattenHouseholder_mul_transpose e _)
    (le_max_right _ _) (le_max_right _ _) hH'

end SuperdiffusionCLT.Section7
