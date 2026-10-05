/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChart

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# Regularity of the transported coefficient

The coefficient `Ã(x) = DΨ DΨᵀ ∘ Ψ⁻¹ (x - τ)` of the flattened Laplace equation is smooth, and
Lipschitz with constant `C(d, M₁) M₂`, so that its partial derivatives are bounded by this constant.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_contDiff_flattenInv {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (u x₀ τ : Vec d) : ContDiff ℝ (⊤ : ℕ∞) (fun x => flattenInv e ψ x₀ u (x - τ)) := by
  unfold flattenInv
  refine (contDiff_shear hψ.neg).comp ?_
  refine contDiff_pi.2 fun k => ?_
  simp only [matVecMul, Pi.add_apply, Pi.sub_apply]
  refine ContDiff.add (ContDiff.sum fun l _ => ?_) contDiff_const
  exact contDiff_const.mul ((contDiff_apply ℝ ℝ l).comp (contDiff_id.sub contDiff_const))

/-- The transported coefficient is smooth. -/
theorem r3e_contDiff_coeff {e : Vec d} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (u x₀ τ : Vec d) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ) i j) := by
  have hJ : ∀ a b : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun x => shearJac e ψ (flattenInv e ψ x₀ u (x - τ)) a b) := fun a b => by
    simp only [shearJac, Matrix.sub_apply, Matrix.vecMulVec_apply, projGradVec]
    exact contDiff_const.sub (contDiff_const.mul
      ((contDiff_projGrad hψ b).comp (r3e_contDiff_flattenInv hψ u x₀ τ)))
  unfold flattenCoeff
  simp only [Matrix.mul_one, Matrix.mul_apply, matTranspose, Matrix.transpose_apply]
  refine ContDiff.sum fun l _ => ?_
  refine ContDiff.mul (ContDiff.sum fun k _ => ?_) contDiff_const
  exact contDiff_const.mul (ContDiff.sum fun m _ => (hJ _ _).mul (hJ _ _))

theorem r3e_coeff_form {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ z : Vec d) :
    flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) z =
      1 + vecMulVec (r3e_O e ψ x₀ u *ᵥ (projGradVec e ψ x₀ - projGradVec e ψ (flattenInv e ψ x₀ u z)))
          (r3e_O e ψ x₀ u *ᵥ e) +
        vecMulVec (r3e_O e ψ x₀ u *ᵥ e)
          (r3e_O e ψ x₀ u *ᵥ (projGradVec e ψ x₀ - projGradVec e ψ (flattenInv e ψ x₀ u z))) +
        ((projGradVec e ψ x₀ - projGradVec e ψ (flattenInv e ψ x₀ u z)) ⬝ᵥ
            (projGradVec e ψ x₀ - projGradVec e ψ (flattenInv e ψ x₀ u z))) •
          vecMulVec (r3e_O e ψ x₀ u *ᵥ e) (r3e_O e ψ x₀ u *ᵥ e) := by
  have hg := vecDot_self_projGradVec he hψ x₀
  have hOO := flattenHouseholder_mul_transpose (flattenNormal e (projGradVec e ψ x₀)) u
  unfold r3e_O
  rw [flattenCoeff_eq hg, ← flatten_gram hOO e]

theorem r3e_dot_sq_sub (a b : Vec d) : a ⬝ᵥ a - b ⬝ᵥ b = (a - b) ⬝ᵥ (a + b) := by
  rw [sub_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm b a]
  ring

theorem r3e_form_sub (O : Mat d) (e δ δ' : Vec d) (i j : Fin d) :
    ((1 : Mat d) + vecMulVec (O *ᵥ δ) (O *ᵥ e) + vecMulVec (O *ᵥ e) (O *ᵥ δ) +
        (δ ⬝ᵥ δ) • vecMulVec (O *ᵥ e) (O *ᵥ e)) i j -
      ((1 : Mat d) + vecMulVec (O *ᵥ δ') (O *ᵥ e) + vecMulVec (O *ᵥ e) (O *ᵥ δ') +
        (δ' ⬝ᵥ δ') • vecMulVec (O *ᵥ e) (O *ᵥ e)) i j =
      (O *ᵥ (δ - δ')) i * (O *ᵥ e) j + (O *ᵥ e) i * (O *ᵥ (δ - δ')) j +
        (δ ⬝ᵥ δ - δ' ⬝ᵥ δ') * ((O *ᵥ e) i * (O *ᵥ e) j) := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.mulVec_sub, Pi.sub_apply]
  ring

/-- Two point Lipschitz bound of the transported coefficient. -/
theorem r3e_coeff_sub_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ M₂ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁)
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (u x₀ : Vec d) {Kl : ℝ}
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ u y - flattenInv e ψ x₀ u z‖ ≤ Kl * ‖y - z‖)
    (z z' : Vec d) (i j : Fin d) :
    |flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) z i j -
        flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) z' i j| ≤
      (2 * d ^ 2 + 8 * d ^ 3 * M₁) * (2 * M₂ * ((1 + d) * Kl)) * ‖z - z'‖ := by
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have hM₂ : 0 ≤ M₂ := flatten_nonneg_of_lipschitz hb2 i
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set O : Mat d := r3e_O e ψ x₀ u with hO
  set y : Vec d := flattenInv e ψ x₀ u z with hy
  set y' : Vec d := flattenInv e ψ x₀ u z' with hy'
  set δ : Vec d := projGradVec e ψ x₀ - projGradVec e ψ y with hδ
  set δ' : Vec d := projGradVec e ψ x₀ - projGradVec e ψ y' with hδ'
  set η : Vec d := δ - δ' with hη
  have hA := r3e_O_entry_le e ψ x₀ u
  have hw : ∀ k, |(O *ᵥ e) k| ≤ d := fun k => by
    have := flatten_abs_mulVec_le hA e k
    have h1 : ‖e‖ ≤ 1 := norm_le_one_of_vecNormSq he
    nlinarith only [this, h1, hd]
  have hvη : ∀ k, |(O *ᵥ η) k| ≤ d * ‖η‖ := flatten_abs_mulVec_le hA η
  have hδn : ‖δ‖ ≤ 4 * M₁ := by
    have h1 := flatten_norm_projGradVec_le he hψ hb1 x₀
    have h2 := flatten_norm_projGradVec_le he hψ hb1 y
    calc ‖δ‖ ≤ ‖projGradVec e ψ x₀‖ + ‖projGradVec e ψ y‖ := norm_sub_le _ _
      _ ≤ 4 * M₁ := by linarith only [h1, h2]
  have hδn' : ‖δ'‖ ≤ 4 * M₁ := by
    have h1 := flatten_norm_projGradVec_le he hψ hb1 x₀
    have h2 := flatten_norm_projGradVec_le he hψ hb1 y'
    calc ‖δ'‖ ≤ ‖projGradVec e ψ x₀‖ + ‖projGradVec e ψ y'‖ := norm_sub_le _ _
      _ ≤ 4 * M₁ := by linarith only [h1, h2]
  have hηn : ‖η‖ ≤ 2 * M₂ * ((1 + d) * (Kl * ‖z - z'‖)) := by
    have h1 : η = projGradVec e ψ y' - projGradVec e ψ y := by
      rw [hη, hδ, hδ']; abel
    rw [h1]
    refine (flatten_norm_projGradVec_sub_le he hψ hM₂ hb2 y' y).trans ?_
    have h2 : ‖y' - y‖ ≤ Kl * ‖z - z'‖ := by
      have := hKlip z' z
      rwa [norm_sub_rev z' z] at this
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
  have hsum : ‖δ + δ'‖ ≤ 8 * M₁ := by
    calc ‖δ + δ'‖ ≤ ‖δ‖ + ‖δ'‖ := norm_add_le _ _
      _ ≤ 8 * M₁ := by linarith only [hδn, hδn']
  have hdd : |δ ⬝ᵥ δ - δ' ⬝ᵥ δ'| ≤ d * (‖η‖ * (8 * M₁)) := by
    have h1 : δ ⬝ᵥ δ - δ' ⬝ᵥ δ' = η ⬝ᵥ (δ + δ') := r3e_dot_sq_sub δ δ'
    rw [h1]
    refine (flatten_abs_dot_le η (δ + δ')).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)) hd
  have hdiff : flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) z i j -
      flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) z' i j =
      (O *ᵥ η) i * (O *ᵥ e) j + (O *ᵥ e) i * (O *ᵥ η) j +
        (δ ⬝ᵥ δ - δ' ⬝ᵥ δ') * ((O *ᵥ e) i * (O *ᵥ e) j) := by
    rw [r3e_coeff_form he hψ u x₀ z, r3e_coeff_form he hψ u x₀ z']
    exact r3e_form_sub O e δ δ' i j
  rw [hdiff]
  have e1 : |(O *ᵥ η) i| * |(O *ᵥ e) j| ≤ (d * ‖η‖) * d :=
    mul_le_mul (hvη i) (hw j) (abs_nonneg _) (by positivity)
  have e2 : |(O *ᵥ e) i| * |(O *ᵥ η) j| ≤ d * (d * ‖η‖) :=
    mul_le_mul (hw i) (hvη j) (abs_nonneg _) hd
  have e3 : |δ ⬝ᵥ δ - δ' ⬝ᵥ δ'| * (|(O *ᵥ e) i| * |(O *ᵥ e) j|) ≤
      (d * (‖η‖ * (8 * M₁))) * (d * d) :=
    mul_le_mul hdd (mul_le_mul (hw i) (hw j) (abs_nonneg _) hd) (by positivity) (by positivity)
  have hbd : |(O *ᵥ η) i * (O *ᵥ e) j + (O *ᵥ e) i * (O *ᵥ η) j +
        (δ ⬝ᵥ δ - δ' ⬝ᵥ δ') * ((O *ᵥ e) i * (O *ᵥ e) j)| ≤
      (2 * d ^ 2 + 8 * d ^ 3 * M₁) * ‖η‖ := by
    calc _ ≤ |(O *ᵥ η) i * (O *ᵥ e) j + (O *ᵥ e) i * (O *ᵥ η) j| +
          |(δ ⬝ᵥ δ - δ' ⬝ᵥ δ') * ((O *ᵥ e) i * (O *ᵥ e) j)| := abs_add_le _ _
      _ ≤ (|(O *ᵥ η) i * (O *ᵥ e) j| + |(O *ᵥ e) i * (O *ᵥ η) j|) +
          |(δ ⬝ᵥ δ - δ' ⬝ᵥ δ') * ((O *ᵥ e) i * (O *ᵥ e) j)| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ (2 * d ^ 2 + 8 * d ^ 3 * M₁) * ‖η‖ := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul]
          nlinarith only [e1, e2, e3]
  refine hbd.trans ?_
  have hC : 0 ≤ 2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁ := by positivity
  calc (2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) * ‖η‖
      ≤ (2 * d ^ 2 + 8 * d ^ 3 * M₁) * (2 * M₂ * ((1 + d) * (Kl * ‖z - z'‖))) :=
        mul_le_mul_of_nonneg_left hηn hC
    _ = _ := by ring

/-- The partial derivatives of the transported coefficient are bounded by `C(d, M₁) M₂`. -/
theorem r3e_coeff_fderiv_le {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ M₂ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁)
    (hb2 : ∀ y z, ‖fderiv ℝ ψ y - fderiv ℝ ψ z‖ ≤ M₂ * ‖y - z‖) (u x₀ τ : Vec d) {Kl : ℝ}
    (hKlip : ∀ y z : Vec d, ‖flattenInv e ψ x₀ u y - flattenInv e ψ x₀ u z‖ ≤ Kl * ‖y - z‖)
    (hKl : 0 ≤ Kl) (x : Vec d) (k i j : Fin d) :
    |fderiv ℝ (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ) i j) x
        (basisVec k)| ≤ (2 * d ^ 2 + 8 * d ^ 3 * M₁) * (2 * M₂ * ((1 + d) * Kl)) := by
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have hM₂ : 0 ≤ M₂ := flatten_nonneg_of_lipschitz hb2 i
  have hC : 0 ≤ (2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) * (2 * M₂ * ((1 + d) * Kl)) := by positivity
  have hlip : LipschitzWith (Real.toNNReal ((2 * (d : ℝ) ^ 2 + 8 * d ^ 3 * M₁) *
      (2 * M₂ * ((1 + d) * Kl))))
      (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ) i j) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC]
    have h := r3e_coeff_sub_le he hψ hb1 hb2 u x₀ hKlip (a - τ) (b - τ) i j
    rwa [sub_sub_sub_cancel_right] at h
  have h1 := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
  rw [Real.coe_toNNReal _ hC] at h1
  have h2 : ‖basisVec (d := d) k‖ = 1 := by simp [basisVec, Pi.norm_single]
  calc |fderiv ℝ (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ) i j) x (basisVec k)|
      = ‖fderiv ℝ (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ) i j) x
          (basisVec k)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ) i j) x‖ *
          ‖basisVec (d := d) k‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by rw [h2, mul_one]; exact h1

end SuperdiffusionCLT.Section7
