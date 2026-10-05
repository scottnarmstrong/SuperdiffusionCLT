/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.Dilation

/-!
# Dilation and the normalized norms

Under `y ↦ s y` from `s⁻¹ • U` to `U` the normalized measure `|V|⁻¹ 1_V dx` is carried to the
normalized measure of the image. Hence `lpBar` is invariant under dilation, and `wMinusOneBar`
(dual to the `H¹₀` functions with normalized gradient of norm at most one) picks up exactly the
factor `s⁻¹` for `s > 0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

theorem a18_measurableEmbedding {s : ℝ} (hs : s ≠ 0) :
    MeasurableEmbedding (fun y : Vec d => s • y) :=
  (Homeomorph.smulOfNeZero s hs).measurableEmbedding

theorem a18_volume_smul_inv {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) :
    volume (s⁻¹ • U) = ENNReal.ofReal |(s ^ d)⁻¹| * volume U := by
  have h := Measure.addHaar_preimage_smul (volume : Measure (Vec d)) hs U
  rw [Module.finrank_fin_fun, Set.preimage_smul₀ hs] at h
  exact h

theorem a18_map_restrict {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) :
    Measure.map (fun y : Vec d => s • y) (volume.restrict (s⁻¹ • U)) =
      ENNReal.ofReal |(s ^ d)⁻¹| • volume.restrict U := by
  have h1 := (a18_measurableEmbedding (d := d) hs).restrict_map volume U
  rw [Set.preimage_smul₀ hs] at h1
  have h2 := Measure.map_addHaar_smul (volume : Measure (Vec d)) hs
  rw [Module.finrank_fin_fun] at h2
  rw [← h1, h2, Measure.restrict_smul]

theorem a18_map_normalized {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) :
    Measure.map (fun y : Vec d => s • y) ((volume (s⁻¹ • U))⁻¹ • volume.restrict (s⁻¹ • U)) =
      (volume U)⁻¹ • volume.restrict U := by
  have hc0 : ENNReal.ofReal |(s ^ d)⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr (inv_ne_zero (pow_ne_zero d hs))
  have hct : ENNReal.ofReal |(s ^ d)⁻¹| ≠ ∞ := ENNReal.ofReal_ne_top
  rw [Measure.map_smul, a18_map_restrict hs, a18_volume_smul_inv hs,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), smul_smul, mul_right_comm,
    ENNReal.inv_mul_cancel hc0 hct, one_mul]
  exact (a18_measurableEmbedding (d := d) hs).measurable.aemeasurable

/-- **Scale invariance of `lpBar`.** -/
theorem lpBar_dilate {E : Type*} [NormedAddCommGroup E] {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d))
    (p : ℝ≥0∞) (F : Vec d → E) :
    lpBar (s⁻¹ • U) p (fun y => F (s • y)) = lpBar U p F := by
  unfold lpBar
  rw [← a18_map_normalized hs U]
  exact ((a18_measurableEmbedding (d := d) hs).eLpNorm_map_measure (g := F)).symm

theorem lpBar_dilate_of_eq {E : Type*} [NormedAddCommGroup E] {s : ℝ} (hs : s ≠ 0)
    {U V : Set (Vec d)} (h : V = s⁻¹ • U) (p : ℝ≥0∞) (F : Vec d → E) :
    lpBar V p (fun y => F (s • y)) = lpBar U p F := by
  subst h
  exact lpBar_dilate hs U p F

theorem a18_setIntegral_dilate {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) (F : Vec d → ℝ) :
    ∫ y in s⁻¹ • U, F (s • y) = |(s ^ d)⁻¹| * ∫ x in U, F x := by
  rw [← (a18_measurableEmbedding (d := d) hs).integral_map (f := fun y : Vec d => s • y),
    a18_map_restrict hs, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _),
    smul_eq_mul]

theorem a18_toReal_volume {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) :
    (volume (s⁻¹ • U)).toReal = |(s ^ d)⁻¹| * (volume U).toReal := by
  rw [a18_volume_smul_inv hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- The pairing of a scalar `h` with a test function, normalized by the volume, is carried by the
dilation with the factor `s`. -/
theorem a18_pairing_dilate {s : ℝ} (hs : s ≠ 0) (U : Set (Vec d)) (h Ψ Ψ' : Vec d → ℝ)
    (hΨ : ∀ y, Ψ (s • y) = s * Ψ' y) :
    ((volume U).toReal)⁻¹ * ∫ x in U, h x * Ψ x =
      s * (((volume (s⁻¹ • U)).toReal)⁻¹ * ∫ y in s⁻¹ • U, h (s • y) * Ψ' y) := by
  have hc : |(s ^ d)⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero (pow_ne_zero d hs))
  have h1 : ∫ y in s⁻¹ • U, s * (h (s • y) * Ψ' y) =
      |(s ^ d)⁻¹| * ∫ x in U, h x * Ψ x := by
    rw [← a18_setIntegral_dilate hs U (fun x => h x * Ψ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hΨ y]
    ring
  rw [integral_const_mul] at h1
  rw [a18_toReal_volume hs, mul_left_comm s, h1, mul_inv]
  have e : (|(s ^ d)⁻¹|)⁻¹ * ((volume U).toReal)⁻¹ * (|(s ^ d)⁻¹| * ∫ x in U, h x * Ψ x) =
      (|(s ^ d)⁻¹|)⁻¹ * |(s ^ d)⁻¹| * (((volume U).toReal)⁻¹ * ∫ x in U, h x * Ψ x) := by ring
  rw [e, inv_mul_cancel₀ hc, one_mul]

theorem a18_h10_smul_toFun {U : Set (Vec d)} (c : ℝ) (u : H10Function U) (x : Vec d) :
    (c • u).toH1Function.toFun x = c * u.toH1Function.toFun x := rfl

theorem a18_h10_smul_grad {U : Set (Vec d)} (c : ℝ) (u : H10Function U) (x : Vec d) :
    (c • u).toH1Function.grad x = c • u.toH1Function.grad x := rfl

theorem a18_dilate_dilate_set {s : ℝ} (hs : s ≠ 0) (V : Set (Vec d)) :
    (s⁻¹)⁻¹ • (s⁻¹ • V) = V := by
  rw [inv_inv, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- Undo the dilation: `ψ'(s⁻¹ x)` on `V` from `ψ'` on `s⁻¹ • V`. -/
noncomputable def a18Undil {s : ℝ} (hs : s ≠ 0) (V : Set (Vec d)) (ψ : H10Function (s⁻¹ • V)) :
    H10Function V :=
  (ψ.dilateArg (inv_ne_zero hs)).castSet (a18_dilate_dilate_set hs V)

theorem a18Undil_toFun {s : ℝ} (hs : s ≠ 0) (V : Set (Vec d)) (ψ : H10Function (s⁻¹ • V))
    (x : Vec d) : (a18Undil hs V ψ).toH1Function.toFun x = ψ.toH1Function.toFun (s⁻¹ • x) := by
  simp only [a18Undil, H10Function.castSet_toH1Function, H1Function.castSet_toFun,
    H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun]

theorem a18Undil_grad {s : ℝ} (hs : s ≠ 0) (V : Set (Vec d)) (ψ : H10Function (s⁻¹ • V))
    (x : Vec d) :
    (a18Undil hs V ψ).toH1Function.grad x = s⁻¹ • ψ.toH1Function.grad (s⁻¹ • x) := by
  simp only [a18Undil, H10Function.castSet_toH1Function, H1Function.castSet_grad,
    H10Function.dilateArg_toH1Function, H1Function.dilateArg_grad]

/-- **`W^{-1,p}` under dilation.** For `s > 0` the normalized negative norm of `h(s ·)` on
`s⁻¹ • V` is `s⁻¹` times that of `h` on `V`. -/
theorem wMinusOneBar_dilate {s : ℝ} (hs : 0 < s) (V : Set (Vec d)) (p : ℝ≥0∞) (h : Vec d → ℝ) :
    wMinusOneBar (s⁻¹ • V) p (fun y => h (s • y)) =
      ENNReal.ofReal s⁻¹ * wMinusOneBar V p h := by
  have hs0 : s ≠ 0 := hs.ne'
  have hsi : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hval : ∀ (Ψ Ψ' : Vec d → ℝ), (∀ y, Ψ (s • y) = s * Ψ' y) →
      ENNReal.ofReal |((volume (s⁻¹ • V)).toReal)⁻¹ * ∫ y in s⁻¹ • V, h (s • y) * Ψ' y| =
        ENNReal.ofReal s⁻¹ *
          ENNReal.ofReal |((volume V).toReal)⁻¹ * ∫ x in V, h x * Ψ x| := by
    intro Ψ Ψ' hΨ
    have e := a18_pairing_dilate hs0 V h Ψ Ψ' hΨ
    rw [e, ← ENNReal.ofReal_mul hsi, abs_mul s _, abs_of_pos hs, ← mul_assoc, inv_mul_cancel₀ hs0,
      one_mul]
  unfold wMinusOneBar
  apply le_antisymm
  · refine iSup_le fun ψ' => iSup_le fun hψ' => ?_
    have hgrad : ∀ x, (s • a18Undil hs0 V ψ').toH1Function.grad x =
        ψ'.toH1Function.grad (s⁻¹ • x) := by
      intro x
      rw [a18_h10_smul_grad, a18Undil_grad, smul_smul, mul_inv_cancel₀ hs0, one_smul]
    have hfeas : lpBar V p.conjExponent (s • a18Undil hs0 V ψ').toH1Function.grad ≤ 1 := by
      have e : (s • a18Undil hs0 V ψ').toH1Function.grad =
          fun x => ψ'.toH1Function.grad (s⁻¹ • x) := funext hgrad
      rw [e, lpBar_dilate_of_eq (inv_ne_zero hs0) (a18_dilate_dilate_set hs0 V).symm
        p.conjExponent ψ'.toH1Function.grad]
      exact hψ'
    have hΨ : ∀ y, (s • a18Undil hs0 V ψ').toH1Function.toFun (s • y) =
        s * ψ'.toH1Function.toFun y := by
      intro y
      rw [a18_h10_smul_toFun, a18Undil_toFun, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hval _ _ hΨ]
    exact mul_le_mul_right (le_iSup₂ (f := fun (ψ : H10Function V)
      (_ : lpBar V p.conjExponent ψ.toH1Function.grad ≤ 1) =>
        ENNReal.ofReal |((volume V).toReal)⁻¹ * ∫ x in V, h x * ψ.toH1Function.toFun x|)
      (s • a18Undil hs0 V ψ') hfeas) _
  · rw [ENNReal.mul_iSup]
    refine iSup_le fun ψ => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hψ => ?_
    have hgrad : ∀ y, (s⁻¹ • ψ.dilateArg hs0).toH1Function.grad y = ψ.toH1Function.grad (s • y) := by
      intro y
      rw [a18_h10_smul_grad, H10Function.dilateArg_toH1Function, H1Function.dilateArg_grad,
        smul_smul, inv_mul_cancel₀ hs0, one_smul]
    have hfeas : lpBar (s⁻¹ • V) p.conjExponent (s⁻¹ • ψ.dilateArg hs0).toH1Function.grad ≤ 1 := by
      have e : (s⁻¹ • ψ.dilateArg hs0).toH1Function.grad =
          fun y => ψ.toH1Function.grad (s • y) := funext hgrad
      rw [e, lpBar_dilate hs0 V p.conjExponent ψ.toH1Function.grad]
      exact hψ
    have hΨ : ∀ y, ψ.toH1Function.toFun (s • y) =
        s * (s⁻¹ • ψ.dilateArg hs0).toH1Function.toFun y := by
      intro y
      rw [a18_h10_smul_toFun, H10Function.dilateArg_toH1Function, H1Function.dilateArg_toFun,
        ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    rw [← hval _ _ hΨ]
    exact le_iSup₂ (f := fun (ψ : H10Function (s⁻¹ • V))
      (_ : lpBar (s⁻¹ • V) p.conjExponent ψ.toH1Function.grad ≤ 1) =>
        ENNReal.ofReal |((volume (s⁻¹ • V)).toReal)⁻¹ *
          ∫ y in s⁻¹ • V, h (s • y) * ψ.toH1Function.toFun y|)
      (s⁻¹ • ψ.dilateArg hs0) hfeas

/-- Witness: `lpBar` of the dilated function on the dilated cube, at `s = 2`. -/
example (U : Set (Vec 2)) (F : Vec 2 → ℝ) :
    lpBar ((2 : ℝ)⁻¹ • U) 2 (fun y => F ((2 : ℝ) • y)) = lpBar U 2 F :=
  lpBar_dilate two_ne_zero U 2 F

/-- Witness: `wMinusOneBar` at `s = 2` on the unit cube. -/
example (h : Vec 2 → ℝ) :
    wMinusOneBar ((2 : ℝ)⁻¹ • (Set.univ : Set (Vec 2))) 2 (fun y => h ((2 : ℝ) • y)) =
      ENNReal.ofReal (2 : ℝ)⁻¹ * wMinusOneBar Set.univ 2 h :=
  wMinusOneBar_dilate two_pos _ _ h

end SuperdiffusionCLT.Section7
