/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryLocalized

/-!
# Zero extension of a localized zero trace function to the window

For `Ω ⊆ Q` open and `u ∈ H¹(Ω)` with localized zero trace in `Q`, the literal zero extension of
`u` and of its gradient is an `H¹(Q)` function.  The weak gradient identity against a test function
`φ` supported in `Q` is read off the global zero extension of the `H¹₀(Ω)` function `ζ u`, where the
cutoff `ζ` equals `1` near `tsupport φ`.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem dgloc_weak_gradient {Ω Q : Set (Vec d)} (hΩ : IsOpen Ω) (hQ : IsOpen Q)
    (u : H1Function Ω) (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) (i : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφQ : tsupport φ ⊆ Q) :
    ∫ x in Q, Ω.indicator u.toFun x * (fderiv ℝ φ x) (basisVec i) =
      -∫ x in Q, (Ω.indicator u.grad x) i * φ x := by
  obtain ⟨ζ, hζ, hζc, hζQ, hζ1⟩ := dgloc_exists_cutoff hφc hQ hφQ
  obtain ⟨w, hwf, hwg⟩ := dgloc_cut_grad_eq hΩ u hz hζ hζc hζQ
  have hglob := H10Function.hasWeakGradientOn_univ_zeroExtension w hΩ.measurableSet i φ hφ hφc
    (Set.subset_univ _)

  have hdφ : ∀ x, x ∉ tsupport φ → (fderiv ℝ φ x) (basisVec i) = 0 := fun x hx => by
    have : fderiv ℝ φ x = 0 := by
      by_contra h
      exact hx (support_fderiv_subset ℝ h)
    simp [this]
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hQc : ∀ x, x ∉ Q → x ∉ tsupport φ := fun x hx h => hx (hφQ h)
  have e1 : ∫ x in Q, Ω.indicator u.toFun x * (fderiv ℝ φ x) (basisVec i) =
      ∫ x, w.zeroExtension x * (fderiv ℝ φ x) (basisVec i) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hdφ x (hQc x hx), mul_zero]]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hxs : x ∈ tsupport φ
    · by_cases hxΩ : x ∈ Ω
      · simp only [Set.indicator_of_mem hxΩ, H10Function.zeroExtension_apply_of_mem w hxΩ,
          hwf x, (hζ1 x hxs).self_of_nhds, one_mul]
      · simp [Set.indicator_of_notMem hxΩ, H10Function.zeroExtension_apply_of_not_mem w hxΩ]
    · simp [hdφ x hxs]
  have hae : ∀ᵐ x ∂volume, x ∈ Ω → x ∈ tsupport φ → w.toH1Function.grad x = u.grad x := by
    rw [← ae_restrict_iff' hΩ.measurableSet]
    filter_upwards [hwg] with x hx hxs
    exact hx (hζ1 x hxs)
  have e2 : ∫ x in Q, (Ω.indicator u.grad x) i * φ x =
      ∫ x, w.zeroExtensionGrad x i * φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hφ0 x (hQc x hx), mul_zero]]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    by_cases hxs : x ∈ tsupport φ
    · by_cases hxΩ : x ∈ Ω
      · simp only [Set.indicator_of_mem hxΩ, H10Function.zeroExtensionGrad_apply_of_mem w hxΩ,
          hx hxΩ hxs]
      · simp [Set.indicator_of_notMem hxΩ, H10Function.zeroExtensionGrad_apply_of_not_mem w hxΩ]
    · simp [hφ0 x hxs]
  rw [e1, e2]
  simpa only [Measure.restrict_univ] using hglob

/-- **The zero extension to the window**: `u ∈ H¹(Ω)` with localized zero trace in `Q ⊇ Ω` extends
by zero to an `H¹(Q)` function, with the zero extension of its gradient. -/
noncomputable def dgloc_zeroExt {Ω Q : Set (Vec d)} (hΩ : IsOpen Ω) (hQ : IsOpen Q)
    (hΩQ : Ω ⊆ Q) (u : H1Function Ω) (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) :
    H1Function Q where
  toFun := Ω.indicator u.toFun
  grad := Ω.indicator u.grad
  memL2 := by
    rw [MemL2On, memLp_indicator_iff_restrict hΩ.measurableSet, Measure.restrict_restrict
      hΩ.measurableSet, Set.inter_eq_left.2 hΩQ]
    exact u.memL2
  gradMemL2 := by
    intro i
    have h : (fun x => (Ω.indicator u.grad x) i) = Ω.indicator (fun x => u.grad x i) := by
      funext x
      by_cases hx : x ∈ Ω <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    rw [MemL2On, h, memLp_indicator_iff_restrict hΩ.measurableSet, Measure.restrict_restrict
      hΩ.measurableSet, Set.inter_eq_left.2 hΩQ]
    exact u.gradMemL2 i
  hasWeakGradient := fun i _ hφ hφc hφQ => dgloc_weak_gradient hΩ hQ u hz i hφ hφc hφQ

theorem dgloc_zeroExt_toFun {Ω Q : Set (Vec d)} (hΩ : IsOpen Ω) (hQ : IsOpen Q)
    (hΩQ : Ω ⊆ Q) (u : H1Function Ω) (hz : LocalizedZeroTraceFunctionOn Ω Q u.toFun) :
    (dgloc_zeroExt hΩ hQ hΩQ u hz).toFun = Ω.indicator u.toFun := rfl

end SuperdiffusionCLT.Section7
