/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.ShearH1B

/-!
# Poincare inequalities on domains: the translation identity

For `u` with weak gradient `g` on an open set `W`, and a vector `h`, almost every `x` whose segment
`[x, x + h]` lies in `W` satisfies `u (x + h) - u x = ∫₀¹ ⟨g (x + s h), h⟩ ds`
(`Section7.a10_translate_identity_dir`). The proof tests against translates of smooth compactly
supported functions, so it needs no smooth approximation of `u` inside `W`.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem a10_exists_ball_support {χ : Vec d → ℝ} (hc : HasCompactSupport χ) :
    ∃ R : ℝ, ∀ y : Vec d, R < ‖y‖ → χ y = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Vec d)
  refine ⟨R, fun y hy => ?_⟩
  by_contra hne
  have hmem : y ∈ Metric.closedBall (0 : Vec d) R := hR (subset_tsupport _ hne)
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  exact absurd hmem (not_le.2 hy)

theorem a10_integrable_family {f : Vec d → ℝ} (hf : LocallyIntegrable f volume)
    (hfm : Measurable f) {χ : Vec d → ℝ} (hχm : Measurable χ) {M R : ℝ}
    (hM : ∀ y, ‖χ y‖ ≤ M) (hR : ∀ y : Vec d, R < ‖y‖ → χ y = 0) (h : Vec d) :
    Integrable (fun p : ℝ × Vec d => χ (p.2 - p.1 • h) * f p.2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  set B : Set (Vec d) := Metric.closedBall 0 (R + ‖h‖) with hB
  have hfB : IntegrableOn f B volume := hf.integrableOn_isCompact (isCompact_closedBall _ _)
  have hk : Integrable (B.indicator fun y => ‖f y‖) volume :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2 hfB.norm
  have hk2 : Integrable (fun p : ℝ × Vec d => B.indicator (fun y => ‖f y‖) p.2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
    hk.comp_snd _
  refine Integrable.mono' (hk2.const_mul M) ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_).mul ?_
    · exact hχm.comp (by fun_prop)
    · exact (hfm.comp measurable_snd).aestronglyMeasurable
  · have hae : ∀ᵐ p ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure (Vec d))),
        p.1 ∈ Icc (0 : ℝ) 1 :=
      (Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hae] with p hp
    by_cases hy : ‖p.2‖ ≤ R + ‖h‖
    · have hyB : p.2 ∈ B := by
        rw [hB, Metric.mem_closedBall, dist_zero_right]; exact hy
      rw [Set.indicator_of_mem hyB, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · have hyB : p.2 ∉ B := by
        rw [hB, Metric.mem_closedBall, dist_zero_right]; exact hy
      rw [Set.indicator_of_notMem hyB]
      have hs0 : 0 ≤ p.1 := hp.1
      have hs1 : p.1 ≤ 1 := hp.2
      have hnorm : R < ‖p.2 - p.1 • h‖ := by
        have h1 : ‖p.2‖ ≤ ‖p.2 - p.1 • h‖ + ‖p.1 • h‖ := by
          have := norm_add_le (p.2 - p.1 • h) (p.1 • h)
          rwa [sub_add_cancel] at this
        have h2 : ‖p.1 • h‖ ≤ ‖h‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
          exact mul_le_of_le_one_left (norm_nonneg _) hs1
        linarith only [h1, h2, not_le.1 hy]
      rw [hR _ hnorm, zero_mul, norm_zero, mul_zero]

/-- Translating the family: `(s, x) ↦ (s, x + s h)` preserves `volume.restrict (Icc 0 1) × volume`. -/
theorem a10_measurePreserving_shift (h : Vec d) :
    MeasurePreserving (fun p : ℝ × Vec d => (p.1, p.2 + p.1 • h))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  refine MeasurePreserving.skew_product (g := fun s x => x + s • h)
    (MeasurePreserving.id _) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun s => (Measure.IsAddRightInvariant.map_add_right_eq_self (μ := (volume : Measure (Vec d))) (s • h))

/-- The shifted family `(s,x) ↦ χ(x) f(x + s h)` is integrable. -/
theorem a10_integrable_family_shift {f : Vec d → ℝ} (hf : LocallyIntegrable f volume)
    (hfm : Measurable f) {χ : Vec d → ℝ} (hχm : Measurable χ) {M R : ℝ}
    (hM : ∀ y, ‖χ y‖ ≤ M) (hR : ∀ y : Vec d, R < ‖y‖ → χ y = 0) (h : Vec d) :
    Integrable (fun p : ℝ × Vec d => χ p.2 * f (p.2 + p.1 • h))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  have h1 := a10_integrable_family hf hfm hχm hM hR h
  have h2 := (a10_measurePreserving_shift (d := d) h).integrable_comp
    (g := fun p : ℝ × Vec d => χ (p.2 - p.1 • h) * f p.2) h1.aestronglyMeasurable
  have h3 := h2.2 h1
  refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [Function.comp]

theorem a10_locInt_translate {U : Vec d → ℝ} (hU : LocallyIntegrable U volume) (a : Vec d) :
    LocallyIntegrable (fun x => U (x + a)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hK' : IsCompact ((fun x => x + a) '' K) := hK.image (by fun_prop)
  have h1 : IntegrableOn U ((fun x => x + a) '' K) volume := hU.integrableOn_isCompact hK'
  have h2 : Integrable (((fun x => x + a) '' K).indicator U) volume :=
    (integrable_indicator_iff hK'.measurableSet).2 h1
  have h3 := h2.comp_add_right a
  refine (integrable_indicator_iff hK.measurableSet).1 ?_
  refine h3.congr (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  by_cases hx : x ∈ K
  · have : x + a ∈ (fun x => x + a) '' K := ⟨x, hx, rfl⟩
    rw [Set.indicator_of_mem this, Set.indicator_of_mem hx]
  · have : x + a ∉ (fun x => x + a) '' K := fun ⟨y, hy, hyx⟩ => hx (by
      have : y = x := add_right_cancel hyx
      rwa [this] at hy)
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hx]

/-- The fundamental theorem along a segment, for the weak gradient: for a test function `φ`
with `tsupport φ ⊆ {x | [x, x+h] ⊆ W}`, the weak identity transported along the segment. -/
theorem a10_weak_shift {W : Set (Vec d)} {U Gh : Vec d → ℝ} (h : Vec d)
    (hweak : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ x, U x * fderiv ℝ φ x h = -∫ x, Gh x * φ x)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) {s : ℝ}
    (hsub : ∀ y ∈ tsupport φ, y + s • h ∈ W) :
    ∫ y, fderiv ℝ φ (y - s • h) h * U y = -∫ y, φ (y - s • h) * Gh y := by
  set φs : Vec d → ℝ := fun y => φ (y + -(s • h)) with hφs
  have hφs_smooth : ContDiff ℝ (⊤ : ℕ∞) φs := hφ.comp (contDiff_id.add contDiff_const)
  have hφs_c : HasCompactSupport φs := hφc.comp_homeomorph (Homeomorph.addRight (-(s • h)))
  have hφs_ts : tsupport φs ⊆ W := by
    have : tsupport φs = (Homeomorph.addRight (-(s • h))) ⁻¹' tsupport φ :=
      tsupport_comp_eq_preimage φ (Homeomorph.addRight (-(s • h)))
    rw [this]
    intro y hy
    have hy' : y + -(s • h) ∈ tsupport φ := hy
    have := hsub _ hy'
    rwa [neg_add_cancel_right] at this
  have key := hweak φs hφs_smooth hφs_c hφs_ts
  simp only [hφs, fderiv_comp_add_right] at key
  simp only [sub_eq_add_neg]
  rw [show (fun y : Vec d => fderiv ℝ φ (y + -(s • h)) h * U y) =
      fun y => U y * fderiv ℝ φ (y + -(s • h)) h from funext fun y => mul_comm _ _,
    show (fun y : Vec d => φ (y + -(s • h)) * Gh y) =
      fun y => Gh y * φ (y + -(s • h)) from funext fun y => mul_comm _ _]
  exact key

theorem a10_isOpen_segment_set {W : Set (Vec d)} (hW : IsOpen W) (h : Vec d) :
    IsOpen {x : Vec d | ∀ s ∈ Icc (0 : ℝ) 1, x + s • h ∈ W} := by
  rw [Metric.isOpen_iff]
  intro x hx
  have hcomp : IsCompact ((fun s : ℝ => x + s • h) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hsub⟩ := hcomp.exists_thickening_subset_open hW (by
    rintro _ ⟨s, hs, rfl⟩
    exact hx s hs)
  refine ⟨δ, hδ, fun y hy s hs => hsub ?_⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨x + s • h, ⟨s, hs, rfl⟩, ?_⟩
  rw [dist_add_right]
  exact Metric.mem_ball.1 hy

theorem a10_locInt_segment_avg {Gh : Vec d → ℝ} (hGm : Measurable Gh)
    (hGl : LocallyIntegrable Gh volume) (h : Vec d) :
    LocallyIntegrable (fun x : Vec d => ∫ s in Icc (0 : ℝ) 1, Gh (x + s • h)) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  set χ : Vec d → ℝ := (Metric.closedBall (0 : Vec d) R).indicator (fun _ => (1 : ℝ)) with hχ
  have hχm : Measurable χ := measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  have hfam := a10_integrable_family_shift hGl hGm hχm (M := 1) (R := R)
    (fun y => by
      by_cases hy : y ∈ Metric.closedBall (0 : Vec d) R
      · simp [hχ, Set.indicator_of_mem hy]
      · simp [hχ, Set.indicator_of_notMem hy])
    (fun y hy => by
      have : y ∉ Metric.closedBall (0 : Vec d) R := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact not_le.2 hy
      simp [hχ, Set.indicator_of_notMem this]) h
  have h1 := (hfam.swap).integral_prod_left
  have h2 : Integrable (fun x : Vec d => χ x * ∫ s in Icc (0 : ℝ) 1, Gh (x + s • h)) volume := by
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp]
    exact (MeasureTheory.integral_const_mul (χ x) (fun s : ℝ => Gh (x + s • h))).symm ▸ rfl
  have h3 : IntegrableOn (fun x : Vec d => ∫ s in Icc (0 : ℝ) 1, Gh (x + s • h))
      (Metric.closedBall (0 : Vec d) R) volume := by
    refine (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).1 ?_
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Metric.closedBall (0 : Vec d) R
    · simp [hχ, Set.indicator_of_mem hx]
    · simp [hχ, Set.indicator_of_notMem hx]
  exact h3.mono_set hR

/-- Translation identity: for a function with weak directional derivative `Gh` along `h`, almost
every `x` whose segment `[x, x+h]` lies in `W` satisfies `U (x+h) - U x = ∫₀¹ Gh (x + s h) ds`. -/
theorem a10_translate_identity_dir {W : Set (Vec d)} (hW : IsOpen W)
    {U Gh : Vec d → ℝ} (hUm : Measurable U) (hGm : Measurable Gh)
    (hUl : LocallyIntegrable U volume) (hGl : LocallyIntegrable Gh volume) (h : Vec d)
    (hweak : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ x, U x * fderiv ℝ φ x h = -∫ x, Gh x * φ x) :
    ∀ᵐ x : Vec d, (∀ s ∈ Icc (0 : ℝ) 1, x + s • h ∈ W) →
      U (x + h) - U x = ∫ s in Icc (0 : ℝ) 1, Gh (x + s • h) := by
  set O : Set (Vec d) := {x : Vec d | ∀ s ∈ Icc (0 : ℝ) 1, x + s • h ∈ W} with hO
  have hOopen : IsOpen O := a10_isOpen_segment_set hW h
  set F : Vec d → ℝ := fun x => ∫ s in Icc (0 : ℝ) 1, Gh (x + s • h) with hF
  have hFloc : LocallyIntegrable F volume := a10_locInt_segment_avg hGm hGl h
  have hli : LocallyIntegrableOn (fun x => U (x + h) - U x - F x) O volume :=
    (((a10_locInt_translate hUl h).sub hUl).sub hFloc).locallyIntegrableOn O
  have htest : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ O → ∫ x, φ x • (U (x + h) - U x - F x) = 0 := by
    intro φ hφ hφc hφO
    have hφcont : Continuous φ := hφ.continuous
    obtain ⟨R, hR⟩ := a10_exists_ball_support hφc
    obtain ⟨M, hM⟩ := hφcont.bounded_above_of_compact_support hφc
    set ψ : Vec d → ℝ := fun z => fderiv ℝ φ z h with hψ
    have hψcont : Continuous ψ :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψc : HasCompactSupport ψ := hφc.fderiv_apply ℝ h
    obtain ⟨Mψ, hMψ⟩ := hψcont.bounded_above_of_compact_support hψc
    obtain ⟨Rψ, hRψ⟩ := a10_exists_ball_support hψc
    have I1 : Integrable (fun x => φ x * U (x + h)) volume := by
      have := (a10_locInt_translate hUl h).integrable_smul_left_of_hasCompactSupport hφcont hφc
      simpa [smul_eq_mul] using this
    have I2 : Integrable (fun x => φ x * U x) volume := by
      have := hUl.integrable_smul_left_of_hasCompactSupport hφcont hφc
      simpa [smul_eq_mul] using this
    have I3 : Integrable (fun x => φ x * F x) volume := by
      have := hFloc.integrable_smul_left_of_hasCompactSupport hφcont hφc
      simpa [smul_eq_mul] using this
    have hφh : HasCompactSupport (fun y => φ (y - h)) := by
      have := hφc.comp_homeomorph (Homeomorph.addRight (-h))
      simpa [Function.comp_def, sub_eq_add_neg] using this
    have I4 : Integrable (fun y => φ (y - h) * U y) volume := by
      have := hUl.integrable_smul_left_of_hasCompactSupport
        (hφcont.comp (continuous_id.sub continuous_const)) hφh
      simpa [smul_eq_mul] using this
    -- K1
    have K1 : ∫ x, φ x * U (x + h) = ∫ y, φ (y - h) * U y := by
      have := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
        (fun y => φ (y - h) * U y) h
      simpa using this
    -- K2 and K3
    have K2 : ∀ y : Vec d, φ (y - h) - φ y = -∫ s in Icc (0 : ℝ) 1, ψ (y - s • h) := by
      intro y
      have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => φ (y - s • h))
          (-ψ (y - s • h)) s := by
        intro s _
        have h1 : HasDerivAt (fun s : ℝ => y - s • h) (-h) s := by
          have := ((hasDerivAt_id s).smul_const h).const_sub y
          simpa using this
        have h2 := ((hφ.differentiable (by simp)) (y - s • h)).hasFDerivAt.comp_hasDerivAt s h1
        simpa [hψ, Function.comp_def] using h2
      have hint : IntervalIntegrable (fun s : ℝ => -ψ (y - s • h)) volume 0 1 :=
        (hψcont.comp (continuous_const.sub (continuous_id.smul continuous_const))).neg.intervalIntegrable _ _
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
        integral_neg] at this
      simp only [one_smul, zero_smul, sub_zero] at this
      linarith only [this]
    have K3 : ∫ y, U y * (φ (y - h) - φ y) =
        -∫ s in Icc (0 : ℝ) 1, ∫ y, ψ (y - s • h) * U y := by
      have hfam := a10_integrable_family hUl hUm hψcont.measurable hMψ hRψ h
      have hsw := hfam.swap
      calc ∫ y, U y * (φ (y - h) - φ y)
          = ∫ y, -(∫ s in Icc (0 : ℝ) 1, ψ (y - s • h) * U y) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only
            rw [K2 y, integral_mul_const]
            ring
        _ = -∫ y, ∫ s in Icc (0 : ℝ) 1, ψ (y - s • h) * U y := by rw [integral_neg]
        _ = -∫ s in Icc (0 : ℝ) 1, ∫ y, ψ (y - s • h) * U y := by
            rw [integral_integral_swap (f := fun y s => ψ (y - s • h) * U y) hsw]
    have K4 : ∀ s ∈ Icc (0 : ℝ) 1, ∫ y, ψ (y - s • h) * U y = -∫ x, φ x * Gh (x + s • h) := by
      intro s hs
      have hsub : ∀ y ∈ tsupport φ, y + s • h ∈ W := fun y hy => hφO hy s hs
      have h1 := a10_weak_shift h hweak hφ hφc hsub
      have h2 : ∫ y, φ (y - s • h) * Gh y = ∫ x, φ x * Gh (x + s • h) := by
        have := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
          (fun y => φ (y - s • h) * Gh y) (s • h)
        simpa using this.symm
      rw [← h2]
      exact h1
    have K6 : ∫ s in Icc (0 : ℝ) 1, ∫ x, φ x * Gh (x + s • h) = ∫ x, φ x * F x := by
      have hfam := a10_integrable_family_shift hGl hGm hφcont.measurable hM hR h
      have hsw := hfam.swap
      rw [← integral_integral_swap (f := fun x s => φ x * Gh (x + s • h)) hsw]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hF]
      exact MeasureTheory.integral_const_mul (φ x) (fun s : ℝ => Gh (x + s • h))
    have e1 : ∫ x, φ x • (U (x + h) - U x - F x) =
        ((∫ x, φ x * U (x + h)) - (∫ x, φ x * U x)) - ∫ x, φ x * F x := by
      calc ∫ x, φ x • (U (x + h) - U x - F x)
          = ∫ x, ((φ x * U (x + h) - φ x * U x) - φ x * F x) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            simp only [smul_eq_mul]
            ring
        _ = (∫ x, (φ x * U (x + h) - φ x * U x)) - ∫ x, φ x * F x :=
            integral_sub (I1.sub I2) I3
        _ = ((∫ x, φ x * U (x + h)) - (∫ x, φ x * U x)) - ∫ x, φ x * F x := by
            rw [integral_sub I1 I2]
    have e2 : (∫ x, φ x * U (x + h)) - (∫ x, φ x * U x) = ∫ y, U y * (φ (y - h) - φ y) := by
      rw [K1, ← integral_sub I4 I2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only
      ring
    have e3 : ∫ s in Icc (0 : ℝ) 1, ∫ y, ψ (y - s • h) * U y =
        -∫ s in Icc (0 : ℝ) 1, ∫ x, φ x * Gh (x + s • h) := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Icc K4
    rw [e1, e2, K3, e3, K6]
    ring
  have hmain := hOopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) hli htest
  filter_upwards [hmain] with x hx hxO
  have := hx hxO
  simp only [hF] at this
  linarith only [this]

end SuperdiffusionCLT.Section7
