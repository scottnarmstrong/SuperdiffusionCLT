/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Datum

/-!
# The `L^∞` homogenization proposition: the smooth datum

`linf_datum`: mollify the globally Lipschitz representative of `linf_global_lipschitz`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- **The smooth datum** (`e.Dir.new.Linfty.gsmooth`), with bounds on
the whole space. -/
theorem linf_datum {U : Set (Vec d)} (hU : IsSmoothBoundedDomain U) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 < t → ∀ (g : H1Function (t • U)) (G : ℝ), 0 ≤ G →
      eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (t • U)) ≤ ENNReal.ofReal G →
      ∀ s : ℝ, 0 < s →
      ∃ gt : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) gt ∧
        (∀ᵐ x ∂volume.restrict (t • U), |gt x - g.toFun x| ≤ C * s * G) ∧
        (∀ x, ‖fderiv ℝ gt x‖ ≤ C * G) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ C * G / s) := by
  obtain ⟨C1, hC1, hglob⟩ := linf_global_lipschitz hU
  obtain ⟨Cm, hCm, hmol⟩ := li1_exists_mollification d
  refine ⟨C1 * (1 + Cm), ?_, fun t ht g G hG hgG s hs => ?_⟩
  · nlinarith only [hC1, hCm]
  have hfin : eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (t • U)) < ⊤ :=
    lt_of_le_of_lt hgG ENNReal.ofReal_lt_top
  obtain ⟨g', hae, hlip⟩ := hglob t ht g hfin
  have hGt : (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (t • U))).toReal ≤ G :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgG).trans (ENNReal.toReal_ofReal hG).le
  have hL0 : 0 ≤ C1 * G := by positivity
  obtain ⟨gt, hsm, happ, hder, hlipd, -⟩ := hmol g' (C1 * G) s hL0 hs (fun x y => by
    refine (hlip x y).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGt (by linarith only [hC1]))
      (norm_nonneg _))
  have hC1' : C1 ≤ C1 * (1 + Cm) := by nlinarith only [hC1, hCm]
  have hCm' : Cm * C1 ≤ C1 * (1 + Cm) := by nlinarith only [hC1, hCm]
  refine ⟨gt, hsm, ?_, fun x => (hder x).trans ?_, fun x => ?_⟩
  · filter_upwards [hae] with x hx
    rw [← hx]
    refine (happ x).trans ?_
    have : s * (C1 * G) ≤ C1 * (1 + Cm) * s * G := by
      have := mul_nonneg hs.le hG
      nlinarith only [this, hC1', hs, hG, mul_le_mul_of_nonneg_right hC1' (mul_nonneg hs.le hG)]
    linarith only [this]
  · exact mul_le_mul_of_nonneg_right hC1' hG
  · have hK : LipschitzWith (Real.toNNReal (Cm * (C1 * G) / s)) (fderiv ℝ gt) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      exact hlipd x y
    refine (norm_fderiv_le_of_lipschitz ℝ hK).trans ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    rw [div_le_div_iff_of_pos_right hs]
    nlinarith only [mul_le_mul_of_nonneg_right hCm' hG]

/-- Witness: the unit disc, the zero datum, `t = s = 1`, `G = 0`: the hypotheses of `linf_datum`
hold, and its conclusion is inhabited. -/
example : ∃ gt : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) gt ∧
    (∀ᵐ x ∂volume.restrict ((1 : ℝ) • Section6.euclidBall (d := 2) 1),
      |gt x - (0 : H1Function ((1 : ℝ) • Section6.euclidBall (d := 2) 1)).toFun x| ≤ 0) := by
  obtain ⟨C, -, h⟩ := linf_datum (d := 2) (U := Section6.euclidBall (d := 2) 1)
    (isSmoothBoundedDomain_euclidBall)
  have h0 : (fun x => eucNorm ((0 : H1Function ((1 : ℝ) • Section6.euclidBall (d := 2) 1)).grad x))
      = fun _ => 0 := by
    funext x
    have : (0 : H1Function ((1 : ℝ) • Section6.euclidBall (d := 2) 1)).grad x = 0 := rfl
    rw [this]
    simp [eucNorm, vecNormSq, vecDot]
  obtain ⟨gt, h1, h2, -⟩ := h 1 one_pos 0 0 le_rfl (by rw [h0]; simp) 1 one_pos
  exact ⟨gt, h1, by simpa using h2⟩

end SuperdiffusionCLT.Section7
