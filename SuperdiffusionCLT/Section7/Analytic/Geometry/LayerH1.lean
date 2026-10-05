/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerPoincare

/-!
# Boundary-layer inequality for `H¹` functions without zero trace: the chart estimate

For a `C¹` function `g` on a chart of a `C^{1,1}` domain, with `V = {e·y < γ(Py)}` and `A` a
measurable piece of `V` whose vertical gap to the graph is at most `ℓ`, the mass of `g²` on `A`
is bounded by `ℓ/(σ₁ - σ₀)` times the mass on the part of the chart within `ρ + σ₁` plus
`σ₁ ℓ` times the mass of the gradient there.  The proof: for each `y ∈ A` and `σ ∈ [σ₀, σ₁]`,
`g(y)² ≤ 2 g(y - σ e)² + 2 σ₁ ∫₀^{σ₁} |∇g(y - ξ e)|² dξ`; average over `σ` and integrate over `A`,
using that the vertical sections of `A` have length at most `ℓ`.
-/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-! ### The one-dimensional estimate -/

/-- Fundamental theorem of calculus along a segment `y + τ v`, `0 ≤ τ ≤ T`, with a nonzero value at
the end of the segment. -/
theorem hl_enorm_le_add_lintegral_line {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) {v : Vec d}
    (hv : ‖v‖ ≤ 1) {y : Vec d} {T L : ℝ} (hT0 : 0 ≤ T) (hTL : T ≤ L) :
    ‖g y‖ₑ ≤ ‖g (y + T • v)‖ₑ + ∫⁻ τ in Set.Icc 0 L, ‖fderiv ℝ g (y + τ • v)‖ₑ := by
  set φ : ℝ → ℝ := fun τ => g (y + τ • v) with hφ
  have hder : ∀ τ, HasDerivAt φ (fderiv ℝ g (y + τ • v) v) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => y + τ • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add y
    exact ((hg.differentiable one_ne_zero) (y + τ • v)).hasFDerivAt.comp_hasDerivAt τ h1
  have hcont : Continuous fun τ : ℝ => fderiv ℝ g (y + τ • v) v := by
    have : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
    exact (this.comp (by fun_prop)).clm_apply continuous_const
  have hftc : ∫ τ in (0 : ℝ)..T, fderiv ℝ g (y + τ • v) v = φ T - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hder τ)
      (hcont.intervalIntegrable _ _)
  have hφ0 : φ 0 = g y := by simp [hφ]
  have h1 : g y = φ T - ∫ τ in Set.Ioc 0 T, fderiv ℝ g (y + τ • v) v := by
    rw [← intervalIntegral.integral_of_le hT0, hftc, hφ0]
    ring
  have h2 : ‖g y‖ₑ ≤ ‖φ T‖ₑ + ‖∫ τ in Set.Ioc 0 T, fderiv ℝ g (y + τ • v) v‖ₑ := by
    conv_lhs => rw [h1]
    exact enorm_sub_le
  refine h2.trans (add_le_add le_rfl ?_)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono fun τ => ?_).trans
    (lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right hTL)))
  have hle : ‖fderiv ℝ g (y + τ • v) v‖ ≤ ‖fderiv ℝ g (y + τ • v)‖ :=
    ((fderiv ℝ g (y + τ • v)).le_opNorm v).trans
      (mul_le_of_le_one_right (norm_nonneg _) hv)
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hle

/-- The squared form of the one-dimensional estimate. -/
theorem hl_sq_le_line {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) {v : Vec d} (hv : ‖v‖ ≤ 1)
    {y : Vec d} {T L : ℝ} (hT0 : 0 ≤ T) (hTL : T ≤ L) :
    ‖g y‖ₑ ^ (2 : ℝ) ≤ 2 * ‖g (y + T • v)‖ₑ ^ (2 : ℝ) +
      2 * (ENNReal.ofReal L * ∫⁻ τ in Set.Icc 0 L, ‖fderiv ℝ g (y + τ • v)‖ₑ ^ (2 : ℝ)) := by
  have h1 := hl_enorm_le_add_lintegral_line hg hv (y := y) hT0 hTL
  have hmeas' : Measurable fun w => ‖fderiv ℝ g w‖ₑ :=
    (hg.continuous_fderiv one_ne_zero).enorm.measurable
  have h2 := layerPoincare_lintegral_Icc_rpow_le (q := 2) (L := L) (by norm_num)
    (f := fun τ => ‖fderiv ℝ g (y + τ • v)‖ₑ)
    ((hmeas'.comp (by fun_prop : Measurable fun τ : ℝ => y + τ • v)).aemeasurable)
  have h3 := ENNReal.rpow_le_rpow h1 (z := 2) (by norm_num)
  have h4 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  have h5 := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖g (y + T • v)‖ₑ
    (∫⁻ τ in Set.Icc 0 L, ‖fderiv ℝ g (y + τ • v)‖ₑ) (by norm_num : (1 : ℝ) ≤ 2)
  rw [h4] at h5
  calc ‖g y‖ₑ ^ (2 : ℝ) ≤ _ := h3
    _ ≤ _ := h5
    _ ≤ 2 * (‖g (y + T • v)‖ₑ ^ (2 : ℝ) + ENNReal.ofReal L *
          ∫⁻ τ in Set.Icc 0 L, ‖fderiv ℝ g (y + τ • v)‖ₑ ^ (2 : ℝ)) := by
        refine mul_le_mul_right (add_le_add le_rfl (h2.trans ?_)) _
        rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one]
    _ = _ := by ring

/-! ### Sweeping along a direction -/

/-- Translating a piece `A` along `ξ v` for `ξ` in an interval and integrating: the sweep
integral is controlled by the length `ℓ` of the sections of `A` in the direction `v`. -/
theorem hl_sweep {F : Vec d → ℝ≥0∞} (hF : Measurable F) (v : Vec d) {I : Set ℝ}
    (hI : MeasurableSet I) {A B : Set (Vec d)} (hA : MeasurableSet A) (hBm : MeasurableSet B)
    {ℓ : ℝ} (hB : ∀ y ∈ A, ∀ ξ ∈ I, y + ξ • v ∈ B)
    (hsec : ∀ z : Vec d, volume {ξ : ℝ | ξ ∈ I ∧ z - ξ • v ∈ A} ≤ ENNReal.ofReal ℓ) :
    ∫⁻ ξ in I, ∫⁻ y in A, F (y + ξ • v) ≤ ENNReal.ofReal ℓ * ∫⁻ z in B, F z := by
  have h1 : ∀ ξ : ℝ, ∫⁻ y in A, F (y + ξ • v) = ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v) * F z := by
    intro ξ
    rw [← lintegral_indicator hA]
    have := lintegral_add_right_eq_self (μ := (volume : Measure (Vec d)))
      (fun z => A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v) * F z) (ξ • v)
    rw [← this]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ A
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hmeasA : Measurable fun p : Vec d × ℝ =>
      A.indicator (fun _ => (1 : ℝ≥0∞)) (p.1 - p.2 • v) * F p.1 := by
    refine Measurable.mul ?_ (hF.comp measurable_fst)
    exact (measurable_const.indicator hA).comp (by fun_prop)
  calc ∫⁻ ξ in I, ∫⁻ y in A, F (y + ξ • v)
      = ∫⁻ ξ in I, ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v) * F z := by
        refine lintegral_congr fun ξ => h1 ξ
    _ = ∫⁻ z, ∫⁻ ξ in I, A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v) * F z := by
        have hm : AEMeasurable (fun p : ℝ × Vec d =>
            A.indicator (fun _ => (1 : ℝ≥0∞)) (p.2 - p.1 • v) * F p.2)
            ((volume.restrict I).prod volume) :=
          (hmeasA.comp measurable_swap).aemeasurable
        exact lintegral_lintegral_swap hm
    _ ≤ ∫⁻ z, B.indicator (fun z => ENNReal.ofReal ℓ * F z) z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ B
        · rw [Set.indicator_of_mem hz]
          have : ∫⁻ ξ in I, A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v) * F z =
              (∫⁻ ξ in I, A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v)) * F z := by
            rw [lintegral_mul_const]
            exact (measurable_const.indicator hA).comp (by fun_prop)
          rw [this]
          refine mul_le_mul_left ?_ _
          have hset : MeasurableSet {ξ : ℝ | ξ ∈ I ∧ z - ξ • v ∈ A} :=
            hI.inter (hA.preimage (by fun_prop))
          calc ∫⁻ ξ in I, A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v)
              = ∫⁻ ξ in I, {ξ : ℝ | z - ξ • v ∈ A}.indicator (fun _ => (1 : ℝ≥0∞)) ξ := by
                refine lintegral_congr fun ξ => ?_
                by_cases h : z - ξ • v ∈ A <;> simp [Set.indicator, h]
            _ = volume ({ξ : ℝ | z - ξ • v ∈ A} ∩ I) := by
                have hS : MeasurableSet {ξ : ℝ | z - ξ • v ∈ A} := hA.preimage (by fun_prop)
                rw [lintegral_indicator_const hS, one_mul, Measure.restrict_apply hS]
            _ = volume {ξ : ℝ | ξ ∈ I ∧ z - ξ • v ∈ A} := by
                congr 1
                ext ξ
                simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
                tauto
            _ ≤ ENNReal.ofReal ℓ := hsec z
        · rw [Set.indicator_of_notMem hz]
          have : ∀ ξ ∈ I, A.indicator (fun _ => (1 : ℝ≥0∞)) (z - ξ • v) * F z = 0 := by
            intro ξ hξ
            by_cases h : z - ξ • v ∈ A
            · exfalso
              apply hz
              have := hB _ h ξ hξ
              simpa using this
            · simp [Set.indicator_of_notMem h]
          rw [setLIntegral_congr_fun hI this]
          simp
    _ = ENNReal.ofReal ℓ * ∫⁻ z in B, F z := by
        rw [lintegral_indicator hBm, lintegral_const_mul _ hF]


theorem hl_sweep_swap {F : Vec d → ℝ≥0∞} (hF : Measurable F) (v : Vec d) {I : Set ℝ}
    (hI : MeasurableSet I) {A B : Set (Vec d)} (hA : MeasurableSet A) (hBm : MeasurableSet B)
    {ℓ : ℝ} (hB : ∀ y ∈ A, ∀ ξ ∈ I, y + ξ • v ∈ B)
    (hsec : ∀ z : Vec d, volume {ξ : ℝ | ξ ∈ I ∧ z - ξ • v ∈ A} ≤ ENNReal.ofReal ℓ) :
    ∫⁻ y in A, ∫⁻ ξ in I, F (y + ξ • v) ≤ ENNReal.ofReal ℓ * ∫⁻ z in B, F z := by
  have hm : AEMeasurable (fun p : Vec d × ℝ => F (p.1 + p.2 • v))
      ((volume.restrict A).prod (volume.restrict I)) :=
    (hF.comp (by fun_prop : Measurable fun p : Vec d × ℝ => p.1 + p.2 • v)).aemeasurable
  exact le_trans (le_of_eq (lintegral_lintegral_swap hm)) (hl_sweep hF v hI hA hBm hB hsec)

theorem hl_measurable_inner {F : Vec d → ℝ≥0∞} (hF : Measurable F) (v : Vec d) (I : Set ℝ) :
    Measurable fun y : Vec d => ∫⁻ ξ in I, F (y + ξ • v) :=
  (hF.comp (by fun_prop : Measurable fun p : Vec d × ℝ => p.1 + p.2 • v)).lintegral_prod_right'
    (ν := volume.restrict I)

/-! ### The chart estimate for a `C¹` function -/

/-- **The chart estimate.** `g ∈ C¹`, `A ⊆ U ∩ B(c, ρ)` measurable with vertical gap at most `ℓ`
to the graph; `0 ≤ σ₀ ≤ σ₁`, `ρ + σ₁ < r`. -/
theorem hl_chart_c1 {U : Set (Vec d)} (hU : IsOpen U) {c : Vec d} {r : ℝ} {e : Vec d}
    (he : vecNormSq e = 1) {γ : Vec d → ℝ}
    (hch : ∀ y ∈ Metric.ball c r, (y ∈ U ↔ vecDot e y < γ (y - vecDot e y • e)))
    {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) {ρ σ₀ σ₁ ℓ : ℝ} (hσ₀ : 0 ≤ σ₀) (hσ : σ₀ ≤ σ₁)
    (hR : ρ + σ₁ < r) {A : Set (Vec d)} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hAb : A ⊆ Metric.ball c ρ)
    (hAℓ : ∀ y ∈ A, γ (y - vecDot e y • e) - vecDot e y ≤ ℓ) :
    ENNReal.ofReal (σ₁ - σ₀) * ∫⁻ y in A, ‖g y‖ₑ ^ (2 : ℝ) ≤
      2 * ENNReal.ofReal ℓ * (∫⁻ z in U ∩ Metric.closedBall c (ρ + σ₁), ‖g z‖ₑ ^ (2 : ℝ)) +
        2 * ENNReal.ofReal (σ₁ - σ₀) * ENNReal.ofReal σ₁ * ENNReal.ofReal ℓ *
          ∫⁻ z in U ∩ Metric.closedBall c (ρ + σ₁), ‖fderiv ℝ g z‖ₑ ^ (2 : ℝ) := by
  set B : Set (Vec d) := U ∩ Metric.closedBall c (ρ + σ₁) with hBdef
  have hBm : MeasurableSet B := hU.measurableSet.inter Metric.isClosed_closedBall.measurableSet
  have he1 := norm_le_one_of_vecNormSq he
  have hv : ‖-e‖ ≤ 1 := by rwa [norm_neg]
  set F1 : Vec d → ℝ≥0∞ := fun z => ‖g z‖ₑ ^ (2 : ℝ) with hF1
  set F2 : Vec d → ℝ≥0∞ := fun z => ‖fderiv ℝ g z‖ₑ ^ (2 : ℝ) with hF2
  have hF1m : Measurable F1 := hg.continuous.enorm.measurable.pow_const _
  have hF2m : Measurable F2 :=
    (hg.continuous_fderiv one_ne_zero).enorm.measurable.pow_const _
  set I₀ : Set ℝ := Set.Icc σ₀ σ₁ with hI₀
  set I₁ : Set ℝ := Set.Icc 0 σ₁ with hI₁
  have hshift : ∀ (y : Vec d) (ξ : ℝ), y + ξ • (-e) = y + (-ξ) • e := fun y ξ => by
    rw [smul_neg, ← neg_smul]
  have hy_ball : ∀ y ∈ A, ‖y - c‖ < ρ := fun y hy => by
    simpa [dist_eq_norm] using hAb hy
  have hB : ∀ I : Set ℝ, I ⊆ Set.Icc 0 σ₁ → ∀ y ∈ A, ∀ ξ ∈ I, y + ξ • (-e) ∈ B := by
    intro I hI y hy ξ hξ
    obtain ⟨hξ0, hξ1⟩ := hI hξ
    have hyr : y ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith only [hy_ball y hy, hR, hσ₀, hσ]
    have hyU := hAU hy
    have hdist : ‖y + ξ • (-e) - c‖ ≤ ρ + σ₁ := by
      calc ‖y + ξ • (-e) - c‖ = ‖(y - c) + ξ • (-e)‖ := by congr 1; abel
        _ ≤ ‖y - c‖ + ‖ξ • (-e)‖ := norm_add_le _ _
        _ ≤ ρ + σ₁ := by
            have h2 : ‖ξ • (-e)‖ ≤ ξ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
              exact mul_le_of_le_one_right hξ0 hv
            linarith only [hy_ball y hy, h2, hξ1]
    refine ⟨?_, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hdist⟩
    have hzr : y + ξ • (-e) ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith only [hdist, hR]
    rw [hch _ hzr, hshift, layerPoincare_proj_add_smul he, layerPoincare_vecDot_add_smul, he]
    have := (hch y hyr).1 hyU
    linarith only [this, hξ0]
  have hsec : ∀ z : Vec d, ∀ I : Set ℝ,
      volume {ξ : ℝ | ξ ∈ I ∧ z - ξ • (-e) ∈ A} ≤ ENNReal.ofReal ℓ := by
    intro z I
    have hsub : {ξ : ℝ | ξ ∈ I ∧ z - ξ • (-e) ∈ A} ⊆
        Set.Ico (γ (z - vecDot e z • e) - vecDot e z - ℓ) (γ (z - vecDot e z • e) - vecDot e z) := by
      rintro ξ ⟨-, hξ⟩
      have hyA : z + ξ • e ∈ A := by simpa using hξ
      have hyr : z + ξ • e ∈ Metric.ball c r := by
        have := hy_ball _ hyA
        rw [Metric.mem_ball, dist_eq_norm]
        linarith only [this, hR, hσ₀, hσ]
      have hpos := sub_pos.2 ((hch _ hyr).1 (hAU hyA))
      have hle := hAℓ _ hyA
      rw [layerPoincare_proj_add_smul he, layerPoincare_vecDot_add_smul, he] at hpos hle
      constructor <;> linarith only [hpos, hle]
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_le_ofReal (by linarith only)
  have hI₀B : I₀ ⊆ Set.Icc 0 σ₁ := Set.Icc_subset_Icc_left hσ₀
  have hmain : ∀ y ∈ A, ENNReal.ofReal (σ₁ - σ₀) * F1 y ≤
      2 * (∫⁻ σ in I₀, F1 (y + σ • (-e))) +
        2 * (ENNReal.ofReal (σ₁ - σ₀) * (ENNReal.ofReal σ₁ * ∫⁻ τ in I₁, F2 (y + τ • (-e)))) := by
    intro y _
    have hpt : ∀ σ ∈ I₀, F1 y ≤ 2 * F1 (y + σ • (-e)) +
        2 * (ENNReal.ofReal σ₁ * (∫⁻ τ in I₁, F2 (y + τ • (-e)))) := by
      intro σ hσ'
      exact hl_sq_le_line hg hv (y := y) (le_trans hσ₀ hσ'.1) hσ'.2
    have h1 := setLIntegral_mono' (μ := (volume : Measure ℝ))
      (measurableSet_Icc (a := σ₀) (b := σ₁)) hpt
    have hm1 : Measurable fun σ : ℝ => F1 (y + σ • (-e)) :=
      hF1m.comp (by fun_prop : Measurable fun σ : ℝ => y + σ • (-e))
    rw [setLIntegral_const, lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
      setLIntegral_const, Real.volume_Icc] at h1
    refine le_trans (le_of_eq ?_) (h1.trans (le_of_eq ?_))
    · exact mul_comm _ _
    · ring
  have hs1 := hl_sweep_swap hF1m (-e) measurableSet_Icc hA hBm (hB I₀ hI₀B) (fun z => hsec z I₀)
  have hs2 := hl_sweep_swap hF2m (-e) measurableSet_Icc hA hBm (hB I₁ le_rfl) (fun z => hsec z I₁)
  calc ENNReal.ofReal (σ₁ - σ₀) * ∫⁻ y in A, F1 y
      = ∫⁻ y in A, ENNReal.ofReal (σ₁ - σ₀) * F1 y :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ y in A, (2 * (∫⁻ σ in I₀, F1 (y + σ • (-e))) +
        2 * (ENNReal.ofReal (σ₁ - σ₀) * (ENNReal.ofReal σ₁ * (∫⁻ τ in I₁, F2 (y + τ • (-e)))))) :=
        setLIntegral_mono' hA hmain
    _ = 2 * (∫⁻ y in A, ∫⁻ σ in I₀, F1 (y + σ • (-e))) +
        2 * (ENNReal.ofReal (σ₁ - σ₀) * (ENNReal.ofReal σ₁ *
          (∫⁻ y in A, ∫⁻ τ in I₁, F2 (y + τ • (-e))))) := by
        have m1 := hl_measurable_inner hF1m (-e) I₀
        have m2 := hl_measurable_inner hF2m (-e) I₁
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ ((m2.const_mul _).const_mul _),
          lintegral_const_mul _ (m2.const_mul _), lintegral_const_mul _ m2]
    _ ≤ 2 * (ENNReal.ofReal ℓ * (∫⁻ z in B, F1 z)) +
        2 * (ENNReal.ofReal (σ₁ - σ₀) * (ENNReal.ofReal σ₁ *
          (ENNReal.ofReal ℓ * (∫⁻ z in B, F2 z)))) := by
        gcongr
    _ = _ := by
        simp only [hF1, hF2]
        ring

end SuperdiffusionCLT.Section7
