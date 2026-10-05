/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2InteriorD
public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyC
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB
public import SuperdiffusionCLT.Section7.Linfty.Energy

/-!
# Reduction to the smooth datum: representatives and the layer bound
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- An `H¹(W)` function with the value changed on a null set. -/
noncomputable def linf_h1_ae {W : Set (Vec d)} (g : H1Function W) (g' : Vec d → ℝ)
    (h : g' =ᵐ[volume.restrict W] g.toFun) : H1Function W where
  toFun := g'
  grad := g.grad
  memL2 := (memLp_congr_ae h).2 g.memL2
  gradMemL2 := g.gradMemL2
  hasWeakGradient := fun i φ hφ hφc hφU => by
    have h1 := g.hasWeakGradient i φ hφ hφc hφU
    rw [← h1]
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]

@[simp] theorem linf_h1_ae_toFun {W : Set (Vec d)} (g : H1Function W) (g' : Vec d → ℝ)
    (h : g' =ᵐ[volume.restrict W] g.toFun) : (linf_h1_ae g g' h).toFun = g' := rfl

@[simp] theorem linf_h1_ae_grad {W : Set (Vec d)} (g : H1Function W) (g' : Vec d → ℝ)
    (h : g' =ᵐ[volume.restrict W] g.toFun) : (linf_h1_ae g g' h).grad = g.grad := rfl

/-- `H¹₀` membership of an `H¹` function equal almost everywhere to an `H¹₀` function. -/
theorem linf_memH10_ae {W : Set (Vec d)} (hW : IsOpen W) (ψ : H10Function W) (h : H1Function W)
    (hae : h.toFun =ᵐ[volume.restrict W] ψ.toH1Function.toFun) : MemH10 W h.toFun := by
  have hgrad : h.grad =ᵐ[volume.restrict W] ψ.toH1Function.grad :=
    h1grad_ae_eq_of_toFun_ae_eq hW hae
  refine ⟨{ toH1Function := h
            approx := ψ.approx
            approx_smooth := ψ.approx_smooth
            approx_hasCompactSupport := ψ.approx_hasCompactSupport
            approx_support_subset := ψ.approx_support_subset
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl⟩
  · have h1 : ∀ n, eLpNorm (fun x => ψ.approx n x - h.toFun x) 2 (volume.restrict W) =
        eLpNorm (fun x => ψ.approx n x - ψ.toH1Function.toFun x) 2 (volume.restrict W) := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    simp only [h1]
    exact ψ.tendsto_approx
  · intro i
    have h1 : ∀ n, eLpNorm (fun x => fderiv ℝ (ψ.approx n) x (basisVec i) - h.grad x i) 2
        (volume.restrict W) = eLpNorm (fun x => fderiv ℝ (ψ.approx n) x (basisVec i) -
          ψ.toH1Function.grad x i) 2 (volume.restrict W) := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [hgrad] with x hx
      rw [hx]
    simp only [h1]
    exact ψ.tendsto_approx_grad i

/-- A bounded domain has bounded distances. -/
theorem linf_dist_le {W : Set (Vec d)} (hWb : IsBoundedDomain W) :
    ∃ D : ℝ, ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ D := by
  obtain ⟨R, hR, hW⟩ := hWb
  refine ⟨2 * R, fun x hx y hy => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have h1 := hW x hx i
  have h2 := hW y hy i
  have := abs_sub_le (x i) 0 (y i)
  simp only [sub_zero, zero_sub, abs_neg] at this
  linarith only [this, h1, h2]

theorem linf_isBounded {W : Set (Vec d)} (hWb : IsBoundedDomain W) : Bornology.IsBounded W := by
  obtain ⟨R, hR, hW⟩ := hWb
  refine (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).2 ⟨R, fun x hx => ?_⟩
  rw [mem_closedBall_zero_iff]
  exact (pi_norm_le_iff_of_nonneg hR.le).2 fun i => by
    rw [Real.norm_eq_abs]; exact hW x hx i

/-- The length of a scalar multiple. -/
theorem linf_eucNorm_smul (s : ℝ) (v : Vec d) : eucNorm (s • v) = |s| * eucNorm v := by
  unfold eucNorm
  have h : vecNormSq (s • v) = s ^ 2 * vecNormSq v := by
    unfold vecNormSq vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

/-- The gradient of the cutoff vanishes where the cutoff equals one. -/
theorem linf_lipGradient_cutoff_of_eq_one (W : Set (Vec d)) (r : ℝ) {x : Vec d}
    (hx : l2a_cutoff W r x = 1) : lipGradient (l2a_cutoff W r) x = 0 := by
  have hmax : IsLocalMax (l2a_cutoff W r) x :=
    Filter.Eventually.of_forall fun y => by rw [hx]; exact l2a_cutoff_le_one W r y
  funext i
  simp [lipGradient, hmax.fderiv_eq_zero]

/-- The length of the gradient of the cutoff is at most `d / r`. -/
theorem linf_eucNorm_lipGradient_cutoff_le [NeZero d] (W : Set (Vec d)) {r : ℝ} (hr : 0 < r)
    (x : Vec d) : eucNorm (lipGradient (l2a_cutoff W r) x) ≤ d / r := by
  have h1 : ‖lipGradient (l2a_cutoff W r) x‖ ≤ 1 / r :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      rw [Real.norm_eq_abs]; exact l2a_lipGradient_cutoff_abs_le W hr x i
  refine (r1_eucNorm_le_mul_norm _).trans ?_
  calc (d : ℝ) * ‖lipGradient (l2a_cutoff W r) x‖ ≤ d * (1 / r) :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
    _ = d / r := by ring

/-- Normalized `L²` norm of a length from an integral bound over a subset `A`. -/
theorem linf_lpBar_euc_le_layer {W A : Set (Vec d)} (h0 : volume W ≠ 0) (ht : volume W ≠ ⊤)
    (hA : volume A ≠ ⊤) {ξ : Vec d → Vec d} (hξ : MemLp ξ 2 (volume.restrict W)) {K : ℝ}
    (hK : 0 ≤ K) (h : ∫ x in W, vecNormSq (ξ x) ≤ K ^ 2 * (volume A).toReal) :
    lpBar W 2 (fun x => eucNorm (ξ x)) ≤ ENNReal.ofReal K * (volume A / volume W) ^ (1 / 2 : ℝ) := by
  rw [li1_lpBar_two_eq W _ (p13_memLp_euc hξ).aestronglyMeasurable h0 ht, p13_eLpNorm_euc hξ]
  have hJ0 : 0 ≤ ∫ x in W, vecNormSq (ξ x) := integral_nonneg fun x => s5_vecNormSq_nonneg _
  have hm0 : 0 ≤ (volume A).toReal := ENNReal.toReal_nonneg
  have h1 : (∫ x in W, vecNormSq (ξ x)) ^ (1 / 2 : ℝ) ≤ K * (volume A).toReal ^ (1 / 2 : ℝ) := by
    refine (Real.rpow_le_rpow hJ0 h (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (sq_nonneg K) hm0, ← Real.rpow_natCast, ← Real.rpow_mul hK]
    norm_num
  have h2 : ENNReal.ofReal ((∫ x in W, vecNormSq (ξ x)) ^ (1 / 2 : ℝ)) ≤
      volume A ^ (1 / 2 : ℝ) * ENNReal.ofReal K := by
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [ENNReal.ofReal_mul hK, mul_comm,
      ← ENNReal.ofReal_rpow_of_nonneg hm0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_toReal hA]
  calc (volume W)⁻¹ ^ (1 / 2 : ℝ) * ENNReal.ofReal ((∫ x in W, vecNormSq (ξ x)) ^ (1 / 2 : ℝ))
      ≤ (volume W)⁻¹ ^ (1 / 2 : ℝ) * (volume A ^ (1 / 2 : ℝ) * ENNReal.ofReal K) := by gcongr
    _ = ENNReal.ofReal K * (volume A / volume W) ^ (1 / 2 : ℝ) := by
      rw [show volume A / volume W = volume A * (volume W)⁻¹ from div_eq_mul_inv _ _,
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring

/-- Cross term, the other way round: `|(A ξ) · S| ≤ λ |ξ|² / 4 + Λ² |S|² / λ`. -/
theorem linf_cross_flux_le {lam Lam : ℝ} {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (ξ S : Vec d) :
    |vecDot (matVecMul A ξ) S| ≤ lam * vecNormSq ξ / 4 + Lam ^ 2 * vecNormSq S / lam := by
  have hlam : 0 < lam := hA.1
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hA.2.1
  have hs : 0 < lam / (2 * Lam ^ 2) := by positivity
  have h1 := s5_abs_vecDot_le_weighted (matVecMul A ξ) S hs
  have h2 := linf_vecNormSq_matVecMul_le hA ξ
  have h3 : lam / (2 * Lam ^ 2) * vecNormSq (matVecMul A ξ) ≤
      lam / (2 * Lam ^ 2) * (Lam ^ 2 * vecNormSq ξ) := mul_le_mul_of_nonneg_left h2 hs.le
  have e : (lam / (2 * Lam ^ 2) * (Lam ^ 2 * vecNormSq ξ) +
      vecNormSq S / (lam / (2 * Lam ^ 2))) / 2 =
      lam * vecNormSq ξ / 4 + Lam ^ 2 * vecNormSq S / lam := by
    field_simp
    ring
  have h4 : (lam / (2 * Lam ^ 2) * vecNormSq (matVecMul A ξ) +
      vecNormSq S / (lam / (2 * Lam ^ 2))) / 2 ≤
      (lam / (2 * Lam ^ 2) * (Lam ^ 2 * vecNormSq ξ) +
        vecNormSq S / (lam / (2 * Lam ^ 2))) / 2 := by
    linarith only [h3]
  linarith only [h1, h4, e]

theorem linf_vecDot_sub_right (x y z : Vec d) : vecDot x (y - z) = vecDot x y - vecDot x z := by
  unfold vecDot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The vector field `D - (s D + t w)` has length at most `|D| + |t| |w|` when `0 ≤ s ≤ 1`. -/
theorem linf_eucNorm_split_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (D w : Vec d) :
    eucNorm (D - (s • D + t • w)) ≤ eucNorm D + |t| * eucNorm w := by
  have e : D - (s • D + t • w) = (1 - s) • D + -(t • w) := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
    ring
  rw [e]
  refine (r1_eucNorm_add_le _ _).trans ?_
  rw [r1_eucNorm_neg, linf_eucNorm_smul, linf_eucNorm_smul, abs_of_nonneg (by linarith only [hs1])]
  have : (1 - s) * eucNorm D ≤ eucNorm D := by
    have := eucNorm_nonneg D
    nlinarith only [this, hs0]
  linarith only [this]

end SuperdiffusionCLT.Section7
