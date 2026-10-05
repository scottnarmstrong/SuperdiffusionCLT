/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ProductLaw
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3

/-!
# Range of dependence and tail of the product law from the seed

The restriction sigma-algebra of the dilated field on `U` is contained in the restriction
sigma-algebra of the seed field on the contracted set `U' = {y | 3^n y ∈ U}`. Hence a seed with
range of dependence `√d` gives shell `n` the range `3^n √d`. The J3 statement is a statement
about the single shell marginal, which is `scaledShellLaw ν₀ n`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The contracted set `{y | 3^n y ∈ U}`. -/
def nv_contractSet (n : ℕ) (U : Set (Vec d)) : Set (Vec d) :=
  (fun y : Vec d ↦ ((3 : ℝ) ^ n) • y) ⁻¹' U

theorem nv_measurableSet_contractSet (n : ℕ) {U : Set (Vec d)} (hU : MeasurableSet U) :
    MeasurableSet (nv_contractSet n U) :=
  hU.preimage (continuous_const_smul _).measurable

theorem nv_forgetShell_dilate (n : ℕ) (j : ShellField d) :
    ShellField.forgetShell (dilate (nv_scaleUnit n) j) =
      dilateReg (n : ℤ) (ShellField.forgetShell j) := by
  apply RegCoeffField.ext
  intro x
  simp [dilateReg_apply]

theorem nv_restrictReg_dilateReg (n : ℕ) (U : Set (Vec d)) (hU : MeasurableSet U)
    (a : RegCoeffField d) :
    restrictReg U hU (dilateReg (n : ℤ) a) =
      dilateReg (n : ℤ) (restrictReg (nv_contractSet n U) (nv_measurableSet_contractSet n hU) a) := by
  apply RegCoeffField.ext
  intro x
  have h3 : ((3 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hx : ((3 : ℝ) ^ n) • (((3 : ℝ) ^ n)⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ h3, one_smul]
  by_cases hxU : x ∈ U
  · have hmem : ((3 : ℝ) ^ n)⁻¹ • x ∈ nv_contractSet n U := by
      show ((3 : ℝ) ^ n) • (((3 : ℝ) ^ n)⁻¹ • x) ∈ U
      rw [hx]; exact hxU
    simp [restrictReg_apply, dilateReg_apply, Set.indicator_of_mem hxU,
      Set.indicator_of_mem hmem]
  · have hmem : ((3 : ℝ) ^ n)⁻¹ • x ∉ nv_contractSet n U := by
      intro h
      apply hxU
      have h' : ((3 : ℝ) ^ n) • (((3 : ℝ) ^ n)⁻¹ • x) ∈ U := h
      rwa [hx] at h'
    simp [restrictReg_apply, dilateReg_apply, Set.indicator_of_notMem hxU,
      Set.indicator_of_notMem hmem]

/-- The pullback of the restriction sigma-algebra on `U` along the dilation is below the
restriction sigma-algebra of the seed on the contracted set. -/
theorem nv_comap_dilate_restrictionSigma_le (n : ℕ) (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurableSpace.comap (dilate (nv_scaleUnit n))
        (ShellField.shellRestrictionSigma U hU) ≤
      ShellField.shellRestrictionSigma (nv_contractSet n U) (nv_measurableSet_contractSet n hU) := by
  unfold ShellField.shellRestrictionSigma
  rw [MeasurableSpace.comap_comp]
  have : (fun j : ShellField d ↦ restrictReg U hU (ShellField.forgetShell j)) ∘
        dilate (nv_scaleUnit n) =
      dilateReg (n : ℤ) ∘ (fun j : ShellField d ↦
        restrictReg (nv_contractSet n U) (nv_measurableSet_contractSet n hU)
          (ShellField.forgetShell j)) := by
    funext j
    simp only [Function.comp_apply, nv_forgetShell_dilate, nv_restrictReg_dilateReg]
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_dilateReg (d := d) (n : ℤ)).comap_le

theorem nv_vecNorm_smul (c : ℝ) (x : Vec d) :
    Book.Ch02.vecNorm (c • x) = |c| * Book.Ch02.vecNorm x := by
  change ‖(WithLp.toLp 2 (c • x) : EuclideanSpace ℝ (Fin d))‖ =
    |c| * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖
  have h : (WithLp.toLp 2 (c • x) : EuclideanSpace ℝ (Fin d)) =
      c • (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) := rfl
  rw [h, norm_smul, Real.norm_eq_abs]

/-- Separation by `3^n √d` after contraction becomes separation by `√d`. -/
theorem nv_separated_contract (n : ℕ) {U V : Set (Vec d)}
    (h : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      (3 : ℝ) ^ n * Real.sqrt (d : ℝ) ≤ Book.Ch02.vecNorm (x - y)) :
    ∀ ⦃x y : Vec d⦄, x ∈ nv_contractSet n U → y ∈ nv_contractSet n V →
      Real.sqrt (d : ℝ) ≤ Book.Ch02.vecNorm (x - y) := by
  intro x y hx hy
  have h1 := h hx hy
  rw [← smul_sub, nv_vecNorm_smul, abs_of_pos (by positivity)] at h1
  exact le_of_mul_le_mul_left h1 (by positivity)

/-- The seed hypothesis for J1V2: range of dependence `√d` of the seed shell. -/
theorem nv_shellLawJ1Restriction_productLaw (ν₀ : ProbabilityMeasure (ShellField d))
    (hν : ∀ (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V),
      (∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → Real.sqrt (d : ℝ) ≤ Book.Ch02.vecNorm (x - y)) →
      Indep (ShellField.shellRestrictionSigma U hU) (ShellField.shellRestrictionSigma V hV)
        ν₀.toMeasure) :
    ShellLawJ1Restriction d (nv_productLaw ν₀) where
  restriction_range_dependence n U V hU hV hsep := by
    rw [nv_shellMarginalLaw_productLaw_toMeasure]
    have hind := hν _ _ (nv_measurableSet_contractSet n hU) (nv_measurableSet_contractSet n hV)
      (nv_separated_contract n hsep)
    have h1 := (Indep_iff _ _ _).1 hind
    refine (Indep_iff _ _ _).2 fun s t hs ht ↦ ?_
    have hD : Measurable (dilate (nv_scaleUnit n) : ShellField d → ShellField d) :=
      measurable_dilate _
    have hs' : MeasurableSet[ShellField.shellRestrictionSigma (nv_contractSet n U)
        (nv_measurableSet_contractSet n hU)] (dilate (nv_scaleUnit n) ⁻¹' s) :=
      nv_comap_dilate_restrictionSigma_le n U hU _ ⟨s, hs, rfl⟩
    have ht' : MeasurableSet[ShellField.shellRestrictionSigma (nv_contractSet n V)
        (nv_measurableSet_contractSet n hV)] (dilate (nv_scaleUnit n) ⁻¹' t) :=
      nv_comap_dilate_restrictionSigma_le n V hV _ ⟨t, ht, rfl⟩
    have hsM : MeasurableSet s := ShellField.shellRestrictionSigma_le U hU _ hs
    have htM : MeasurableSet t := ShellField.shellRestrictionSigma_le V hV _ ht
    rw [Measure.map_apply hD (hsM.inter htM), Measure.map_apply hD hsM,
      Measure.map_apply hD htM, Set.preimage_inter]
    exact h1 _ _ hs' ht'

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
