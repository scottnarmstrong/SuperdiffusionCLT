/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.HeatGenerator

/-!
# Averages over a shift family: differentiation under the integral

For a measure `ν` on a parameter space `Ω`, a weight `w : Ω → ℝ` and a shift `s : Ω → E`, the
average `x ↦ ∫ w ω • h (x + s ω) ∂ν` of a function `h` is as smooth as `h`: the derivative is the
average of the derivative.  This is the single analytic input of the heat core statement
(`SuperdiffusionCLT.Section8.Brownian.HeatCoreB`): the heat resolvent of a smooth
compactly supported function is such an average, over the product of the exponential weight and
the Gaussian shift.

Main results (all names begin with the prefix heatCore, followed by an underscore):

* `heatCore_avg`: the average of `h`.
* `heatCore_hasFDerivAt_avg`, `heatCore_continuous_avg`, `heatCore_tendsto_avg`: derivative,
  continuity, and decay at infinity of the average.
* `heatCore_contDiff_two_avg`: a `C²` function with bounded derivatives of order at most two has
  a `C²` average, whose second derivative is the average of the second derivative.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization MeasureTheory Topology

noncomputable section

section Average

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω]

/-- The average of `h` over the shifts `s` with weight `w` and measure `ν`. -/
def heatCore_avg (ν : Measure Ω) (w : Ω → ℝ) (s : Ω → Vec d) (h : Vec d → H) (x : Vec d) : H :=
  ∫ ω, w ω • h (x + s ω) ∂ν

theorem heatCore_aestronglyMeasurable {ν : Measure Ω} {w : Ω → ℝ} {s : Ω → Vec d}
    (hw : Integrable w ν) (hs : Measurable s) {h : Vec d → H} (hh : Continuous h) (x : Vec d) :
    AEStronglyMeasurable (fun ω ↦ w ω • h (x + s ω)) ν := by
  have h1 : AEStronglyMeasurable (fun ω ↦ x + s ω) ν :=
    (measurable_const.add hs).aestronglyMeasurable
  exact hw.aestronglyMeasurable.smul (hh.comp_aestronglyMeasurable h1)

theorem heatCore_integrable {ν : Measure Ω} {w : Ω → ℝ} {s : Ω → Vec d}
    (hw : Integrable w ν) (hs : Measurable s) {h : Vec d → H} (hh : Continuous h) {B : ℝ}
    (hB : ∀ y, ‖h y‖ ≤ B) (x : Vec d) :
    Integrable (fun ω ↦ w ω • h (x + s ω)) ν := by
  refine Integrable.mono' (hw.norm.mul_const B) (heatCore_aestronglyMeasurable hw hs hh x)
    (Eventually.of_forall fun ω ↦ ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

/-- The average of a function with bounded derivative is differentiable, with the average of the
derivative as its derivative. -/
theorem heatCore_hasFDerivAt_avg {ν : Measure Ω} {w : Ω → ℝ} {s : Ω → Vec d}
    (hw : Integrable w ν) (hs : Measurable s) {h : Vec d → H} (hh : Differentiable ℝ h)
    (hD : Continuous (fderiv ℝ h)) {B K : ℝ} (hB : ∀ y, ‖h y‖ ≤ B)
    (hK : ∀ y, ‖fderiv ℝ h y‖ ≤ K) (x : Vec d) :
    HasFDerivAt (heatCore_avg ν w s h) (heatCore_avg ν w s (fderiv ℝ h) x) x := by
  have hF : ∀ y, AEStronglyMeasurable (fun ω ↦ w ω • h (y + s ω)) ν := fun y ↦
    heatCore_aestronglyMeasurable hw hs hh.continuous y
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (y : Vec d) ω ↦ w ω • h (y + s ω))
    (F' := fun (y : Vec d) ω ↦ w ω • fderiv ℝ h (y + s ω)) (bound := fun ω ↦ ‖w ω‖ * K)
    (s := Set.univ) Filter.univ_mem (Eventually.of_forall hF)
    (heatCore_integrable hw hs hh.continuous hB x)
    (heatCore_aestronglyMeasurable hw hs hD x) (Eventually.of_forall fun ω y _ ↦ ?_)
    (hw.norm.mul_const K) (Eventually.of_forall fun ω y _ ↦ ?_)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
  · have h1 : HasFDerivAt (fun z : Vec d ↦ h (z + s ω)) (fderiv ℝ h (y + s ω)) y := by
      have h2 : HasFDerivAt (fun z : Vec d ↦ z + s ω) (ContinuousLinearMap.id ℝ (Vec d)) y :=
        (hasFDerivAt_id y).add_const (s ω)
      have h3 := (hh (y + s ω)).hasFDerivAt.comp y h2
      rwa [ContinuousLinearMap.comp_id] at h3
    exact h1.const_smul (w ω)

/-- The average of a bounded continuous function is continuous. -/
theorem heatCore_continuous_avg {ν : Measure Ω} {w : Ω → ℝ} {s : Ω → Vec d}
    (hw : Integrable w ν) (hs : Measurable s) {h : Vec d → H} (hh : Continuous h) {B : ℝ}
    (hB : ∀ y, ‖h y‖ ≤ B) : Continuous (heatCore_avg ν w s h) := by
  refine continuous_of_dominated (F := fun (y : Vec d) ω ↦ w ω • h (y + s ω))
    (bound := fun ω ↦ ‖w ω‖ * B) (fun y ↦ heatCore_aestronglyMeasurable hw hs hh y)
    (fun y ↦ Eventually.of_forall fun ω ↦ ?_) (hw.norm.mul_const B)
    (Eventually.of_forall fun ω ↦ ?_)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  · exact continuous_const.smul (hh.comp (continuous_id.add continuous_const))

/-- The average of a bounded function vanishing at infinity vanishes at infinity. -/
theorem heatCore_tendsto_avg {ν : Measure Ω} {w : Ω → ℝ} {s : Ω → Vec d}
    (hw : Integrable w ν) (hs : Measurable s) {h : Vec d → H} (hh : Continuous h) {B : ℝ}
    (hB : ∀ y, ‖h y‖ ≤ B) (h0 : Tendsto h (cocompact (Vec d)) (𝓝 0)) :
    Tendsto (heatCore_avg ν w s h) (cocompact (Vec d)) (𝓝 0) := by
  have hshift : ∀ a : Vec d, Tendsto (fun x : Vec d ↦ x + a) (cocompact (Vec d))
      (cocompact (Vec d)) := fun a ↦
    tendsto_iff_comap.mpr (Homeomorph.comap_cocompact (Homeomorph.addRight a)).symm.le
  have := isCountablyGenerated_cocompact d
  have key : Tendsto (fun x ↦ ∫ ω, w ω • h (x + s ω) ∂ν) (cocompact (Vec d))
      (𝓝 (∫ _ : Ω, (0 : H) ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ω ↦ ‖w ω‖ * B)
      (Eventually.of_forall fun y ↦ heatCore_aestronglyMeasurable hw hs hh y)
      (Eventually.of_forall fun y ↦ Eventually.of_forall fun ω ↦ ?_) (hw.norm.mul_const B)
      (Eventually.of_forall fun ω ↦ ?_)
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · have := ((h0.comp (hshift (s ω))).const_smul (w ω))
      simpa using this
  rw [integral_zero] at key
  exact key

/-- **A `C²` function with bounded derivatives has a `C²` average**, and the second derivative of
the average is the average of the second derivative. -/
theorem heatCore_contDiff_two_avg {ν : Measure Ω} {w : Ω → ℝ} {s : Ω → Vec d}
    (hw : Integrable w ν) (hs : Measurable s) {g : Vec d → H} (hg : ContDiff ℝ 2 g) {B K K2 : ℝ}
    (hB : ∀ y, ‖g y‖ ≤ B) (hK : ∀ y, ‖fderiv ℝ g y‖ ≤ K)
    (hK2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ K2) :
    ContDiff ℝ 2 (heatCore_avg ν w s g) ∧
      ∀ y, fderiv ℝ (fderiv ℝ (heatCore_avg ν w s g)) y
        = heatCore_avg ν w s (fderiv ℝ (fderiv ℝ g)) y := by
  have h2 : ContDiff ℝ (1 + 1) g := by rw [one_add_one_eq_two]; exact hg
  obtain ⟨hdiff, -, hg1⟩ := contDiff_succ_iff_fderiv.mp h2
  have h1 : ContDiff ℝ (0 + 1) (fderiv ℝ g) := by simpa using hg1
  obtain ⟨hdiff1, -, hg2⟩ := contDiff_succ_iff_fderiv.mp h1
  have e1 : fderiv ℝ (heatCore_avg ν w s g) = heatCore_avg ν w s (fderiv ℝ g) := funext fun y ↦
    (heatCore_hasFDerivAt_avg hw hs hdiff hg1.continuous hB hK y).fderiv
  have e2 : fderiv ℝ (heatCore_avg ν w s (fderiv ℝ g))
      = heatCore_avg ν w s (fderiv ℝ (fderiv ℝ g)) := funext fun y ↦
    (heatCore_hasFDerivAt_avg hw hs hdiff1 hg2.continuous hK hK2 y).fderiv
  have hcont : Continuous (heatCore_avg ν w s (fderiv ℝ (fderiv ℝ g))) :=
    heatCore_continuous_avg hw hs hg2.continuous hK2
  refine ⟨?_, fun y ↦ by rw [e1, e2]⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from by norm_num, contDiff_succ_iff_fderiv]
  refine ⟨fun y ↦ (heatCore_hasFDerivAt_avg hw hs hdiff hg1.continuous hB hK y).differentiableAt,
    by simp, ?_⟩
  rw [e1, contDiff_one_iff_fderiv, e2]
  exact ⟨fun y ↦ (heatCore_hasFDerivAt_avg hw hs hdiff1 hg2.continuous hK hK2 y).differentiableAt,
    hcont⟩

end Average

section Smooth

open scoped ContDiff

variable {d : ℕ}

theorem heatCore_continuous_fderiv {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g) :
    Continuous (fderiv ℝ g) :=
  hg.continuous_fderiv (by simp)

theorem heatCore_continuous_fderiv_fderiv {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g) :
    Continuous (fderiv ℝ (fderiv ℝ g)) :=
  (hg.fderiv_right (m := 1) (by simp)).continuous_fderiv (by simp)

theorem heatCore_hasCompactSupport_fderiv {g : Vec d → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (fderiv ℝ g) :=
  hc.fderiv (𝕜 := ℝ)

theorem heatCore_hasCompactSupport_fderiv_fderiv {g : Vec d → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (fderiv ℝ (fderiv ℝ g)) :=
  (heatCore_hasCompactSupport_fderiv hc).fderiv (𝕜 := ℝ)

theorem heatCore_bound_fderiv {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ K, ∀ y, ‖fderiv ℝ g y‖ ≤ K := by
  have h1 : Continuous (fderiv ℝ g) := heatCore_continuous_fderiv hg
  have h2 : HasCompactSupport (fderiv ℝ g) := heatCore_hasCompactSupport_fderiv hc
  exact h1.bounded_above_of_compact_support h2

theorem heatCore_norm_iteratedFDeriv_two (u : Vec d → ℝ) (x : Vec d) :
    ‖iteratedFDeriv ℝ 2 u x‖ = ‖fderiv ℝ (fderiv ℝ u) x‖ := by
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

theorem heatCore_bound_fderiv_fderiv {g : Vec d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : ∃ K, ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ K := by
  have h1 : Continuous (iteratedFDeriv ℝ 2 g) := hg.continuous_iteratedFDeriv (by simp)
  have h2 : HasCompactSupport (iteratedFDeriv ℝ 2 g) := hc.iteratedFDeriv (𝕜 := ℝ) 2
  obtain ⟨K, hK⟩ := h1.bounded_above_of_compact_support h2
  exact ⟨K, fun y ↦ by rw [← heatCore_norm_iteratedFDeriv_two]; exact hK y⟩

theorem heatCore_tendsto_fderiv_fderiv {g : Vec d → ℝ} (hc : HasCompactSupport g) :
    Tendsto (fderiv ℝ (fderiv ℝ g)) (cocompact (Vec d)) (𝓝 0) :=
  (heatCore_hasCompactSupport_fderiv_fderiv hc).is_zero_at_infty

theorem heatCore_contDiff_avg_of_smooth {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {w : Ω → ℝ} {s : Ω → Vec d} (hw : Integrable w ν) (hs : Measurable s) {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) {B K K2 : ℝ} (hB : ∀ y, ‖g y‖ ≤ B) (hK : ∀ y, ‖fderiv ℝ g y‖ ≤ K)
    (hK2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ K2) :
    ContDiff ℝ 2 (heatCore_avg ν w s g) ∧
      ∀ y, fderiv ℝ (fderiv ℝ (heatCore_avg ν w s g)) y
        = heatCore_avg ν w s (fderiv ℝ (fderiv ℝ g)) y :=
  heatCore_contDiff_two_avg hw hs (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hB hK hK2

theorem heatCore_tendsto_avg_fderiv_fderiv {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {w : Ω → ℝ} {s : Ω → Vec d} (hw : Integrable w ν) (hs : Measurable s) {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {K2 : ℝ}
    (hK2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ K2) :
    Tendsto (fun x ↦ ‖heatCore_avg ν w s (fderiv ℝ (fderiv ℝ g)) x‖) (cocompact (Vec d))
      (𝓝 0) := by
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ g)) := heatCore_continuous_fderiv_fderiv hg
  have hz : Tendsto (fderiv ℝ (fderiv ℝ g)) (cocompact (Vec d)) (𝓝 0) :=
    heatCore_tendsto_fderiv_fderiv hc
  have h := heatCore_tendsto_avg (h := fderiv ℝ (fderiv ℝ g)) hw hs hD2 hK2 hz
  exact (tendsto_zero_iff_norm_tendsto_zero (f := heatCore_avg ν w s (fderiv ℝ (fderiv ℝ g)))).mp h

/-- **The average of a smooth compactly supported function is `C²` with second derivative
vanishing at infinity.** -/
theorem heatCore_avg_regular {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {w : Ω → ℝ}
    {s : Ω → Vec d} (hw : Integrable w ν) (hs : Measurable s) {g : Vec d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) {B : ℝ} (hB : ∀ y, ‖g y‖ ≤ B) :
    ContDiff ℝ 2 (heatCore_avg ν w s g) ∧
      Tendsto (iteratedFDeriv ℝ 2 (heatCore_avg ν w s g)) (cocompact (Vec d)) (𝓝 0) := by
  obtain ⟨K, hK⟩ := heatCore_bound_fderiv hg hc
  obtain ⟨K2, hK2⟩ := heatCore_bound_fderiv_fderiv hg hc
  obtain ⟨hC2, hder⟩ := heatCore_contDiff_avg_of_smooth hw hs hg hB hK hK2
  have hn := heatCore_tendsto_avg_fderiv_fderiv hw hs hg hc hK2
  have hnorm : ∀ x, ‖iteratedFDeriv ℝ 2 (heatCore_avg ν w s g) x‖
      = ‖heatCore_avg ν w s (fderiv ℝ (fderiv ℝ g)) x‖ := fun x ↦ by
    rw [heatCore_norm_iteratedFDeriv_two, hder]
  exact ⟨hC2, tendsto_zero_iff_norm_tendsto_zero.mpr (hn.congr fun x ↦ (hnorm x).symm)⟩

end Smooth

end

end SuperdiffusionCLT.Section8.Brownian
