/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Truncation
public import Homogenization.Sobolev.W1p.ConvolutionLp
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Lipschitz multipliers, weak gradient and test functions

A Lipschitz function `η : Vec d → ℝ` (for the inherited sup norm, `LipschitzWith K η`) has, as
weak partial derivative on the whole space, its a.e. classical derivative (Rademacher).  Hence the
weak-gradient identity of an `H¹(U)` function extends from smooth test functions to compactly
supported Lipschitz test functions, and the product of an `H¹(U)` function with a bounded Lipschitz
function is `H¹(U)` (`mulLip`).  Compactly supported multipliers give `H¹₀(U)` (`mulLipH10`).
-/

@[expose] public section

open scoped ENNReal NNReal Convolution Topology
open MeasureTheory Set Filter Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

/-- Directional slopes converge to the derivative at a point of differentiability. -/
theorem tendsto_slope_direction {f : Vec d → ℝ} {x : Vec d} (hx : DifferentiableAt ℝ f x)
    (e : Vec d) :
    Tendsto (fun t : ℝ => (f (x + t • e) - f x) / t) (𝓝[≠] 0) (𝓝 (fderiv ℝ f x e)) := by
  have hγ : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hx' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • e) := by simpa using hx.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => f (x + t • e)) (fderiv ℝ f x e) 0 :=
    hx'.comp_hasDerivAt (0 : ℝ) hγ
  have := h1.tendsto_slope_zero
  refine this.congr fun t => ?_
  simp [div_eq_inv_mul]

theorem lipschitzWith_hasWeakPartialDerivOn_univ {K : ℝ≥0} {η : Vec d → ℝ}
    (hη : LipschitzWith K η) (i : Fin d) :
    HasWeakPartialDerivOn Set.univ i η (fun x => fderiv ℝ η x (basisVec i)) := by
  intro φ hφ hφc _
  simp only [Measure.restrict_univ]
  set e : Vec d := basisVec i with he
  have hηc : Continuous η := hη.continuous
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφcont : Continuous φ := hφ.continuous
  obtain ⟨Kφ, hKφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  let hh : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos : ∀ n, 0 < hh n := fun n => by positivity
  have hle1 : ∀ n, hh n ≤ 1 := fun n => by
    simp only [hh]
    rw [div_le_one (by positivity)]; linarith only [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have h0 : Tendsto hh atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h0' : Tendsto hh atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall fun n => (hpos n).ne'⟩
  have h0'' : Tendsto (fun n => -hh n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using h0.neg,
      Eventually.of_forall fun n => (neg_ne_zero.2 (hpos n).ne')⟩
  have hnorme : ‖e‖ = 1 := by simp [he, basisVec, Pi.norm_single]
  set S : Set (Vec d) := Metric.cthickening 1 (tsupport φ) with hSdef
  have hS : IsCompact S := hφc.isCompact.cthickening
  obtain ⟨Mη, hMη⟩ := hS.exists_bound_of_continuousOn hηc.continuousOn
  set Q : ℕ → Vec d → ℝ := fun n x => (φ (x + hh n • e) - φ x) / hh n with hQ
  set R : ℕ → Vec d → ℝ := fun n x => (η x - η (x - hh n • e)) / hh n with hR
  -- the shifted functions are compactly supported
  have hshc : ∀ n, HasCompactSupport (fun x => φ (x + hh n • e)) := fun n =>
    hφc.comp_homeomorph (Homeomorph.addRight (hh n • e))
  -- support of the slope
  have hQS : ∀ n x, x ∉ S → Q n x = 0 := by
    intro n x hxS
    have h1 : φ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hxS (Metric.self_subset_cthickening _ hm)
    have h2 : φ (x + hh n • e) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      apply hxS
      refine Metric.mem_cthickening_of_dist_le x (x + hh n • e) 1 _ hm ?_
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, hnorme, Real.norm_of_nonneg (hpos n).le]
      linarith only [hle1 n]
    simp [hQ, h1, h2]
  have hQb : ∀ n x, |Q n x| ≤ Kφ := by
    intro n x
    have := hKφ.dist_le_mul (x + hh n • e) x
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, hnorme,
      Real.norm_of_nonneg (hpos n).le] at this
    simp only [hQ, abs_div, abs_of_pos (hpos n)]
    rw [div_le_iff₀ (hpos n)]
    simpa [mul_comm] using this
  -- first limit
  have T1 : Tendsto (fun n => ∫ x, η x * Q n x) atTop
      (𝓝 (∫ x, η x * fderiv ℝ φ x e)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => S.indicator (fun _ => Mη * Kφ) x) (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (hηc.mul (((hφcont.comp (continuous_id.add continuous_const)).sub hφcont).div_const _)).aestronglyMeasurable
    · rw [integrable_indicator_iff hS.measurableSet]
      exact integrableOn_const hS.measure_lt_top.ne
    · refine Eventually.of_forall fun x => ?_
      by_cases hxS : x ∈ S
      · simp only [hxS, indicator_of_mem, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul (by simpa using hMη x hxS) (hQb n x) (abs_nonneg _) ((abs_nonneg _).trans (by simpa using hMη x hxS))
      · simp [hxS, hQS n x hxS]
    · refine Eventually.of_forall fun x => ?_
      exact ((tendsto_slope_direction (hφd x) e).comp h0').const_mul (η x)
  -- second limit
  have T2 : Tendsto (fun n => ∫ x, -(R n x * φ x)) atTop
      (𝓝 (∫ x, -(fderiv ℝ η x e * φ x))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (K : ℝ) * |φ x|) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact (((hηc.sub (hηc.comp (continuous_sub_right _))).div_const _).mul hφcont).neg.aestronglyMeasurable
    · exact (hφcont.abs.integrable_of_hasCompactSupport hφc.abs).const_mul (K : ℝ)
    · refine Eventually.of_forall fun x => ?_
      have h1 := hη.dist_le_mul x (x - hh n • e)
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel, norm_smul, hnorme,
        Real.norm_of_nonneg (hpos n).le, mul_one] at h1
      have h2 : |R n x| ≤ K := by
        simp only [hR, abs_div, abs_of_pos (hpos n)]
        rw [div_le_iff₀ (hpos n)]; linarith only [h1]
      rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    · filter_upwards [hη.ae_differentiableAt] with x hx
      have h1 := (tendsto_slope_direction hx e).comp h0''
      have h2 : Tendsto (fun n => R n x) atTop (𝓝 (fderiv ℝ η x e)) := by
        refine h1.congr fun n => ?_
        simp only [Function.comp, hR, neg_smul, sub_eq_add_neg]
        rw [div_neg, ← neg_div]; ring_nf
      exact (h2.mul_const (φ x)).neg
  -- the translation identity
  have hI1 : ∀ n, Integrable (fun x => η x * φ (x + hh n • e)) := fun n =>
    (hηc.mul (hφcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hshc n).mul_left
  have hI2 : Integrable (fun x => η x * φ x) :=
    (hηc.mul hφcont).integrable_of_hasCompactSupport hφc.mul_left
  have hI3 : ∀ n, Integrable (fun x => η (x - hh n • e) * φ x) := fun n =>
    ((hηc.comp (continuous_id.sub continuous_const)).mul hφcont).integrable_of_hasCompactSupport
      hφc.mul_left
  have hshift : ∀ n, ∫ x, η x * φ (x + hh n • e) = ∫ x, η (x - hh n • e) * φ x := fun n => by
    have := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
      (fun x => η (x - hh n • e) * φ x) (hh n • e)
    simpa using this
  have hid : ∀ n, ∫ x, η x * Q n x = ∫ x, -(R n x * φ x) := fun n => by
    have e1 : ∫ x, η x * Q n x =
        ((∫ x, η x * φ (x + hh n • e)) - ∫ x, η x * φ x) / hh n := by
      rw [← integral_sub (hI1 n) hI2, ← integral_div]
      congr 1; funext x; simp only [hQ]; ring
    have e2 : ∫ x, -(R n x * φ x) =
        ((∫ x, η (x - hh n • e) * φ x) - ∫ x, η x * φ x) / hh n := by
      rw [← integral_sub (hI3 n) hI2, ← integral_div]
      congr 1; funext x; simp only [hR]; ring
    rw [e1, e2, hshift n]
  have hlim := tendsto_nhds_unique T1 (T2.congr fun n => (hid n).symm)
  rw [integral_neg] at hlim
  exact hlim

theorem memLp_two_of_bounded_of_zero_off {F : Vec d → ℝ} {C : ℝ} {S : Set (Vec d)}
    (hS : IsCompact S) (hF : AEStronglyMeasurable F volume)
    (hC : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖F x‖ ≤ C) (hz : ∀ x, x ∉ S → F x = 0) :
    MemLp F 2 volume := by
  have hind : F = S.indicator F := by
    funext x
    by_cases hx : x ∈ S
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hz x hx]
  rw [hind, memLp_indicator_iff_restrict hS.isClosed.measurableSet]
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top⟩
  exact MemLp.of_bound (hF.mono_measure Measure.restrict_le_self) C (ae_restrict_of_ae hC)

/-- The coordinate derivatives of a Lipschitz function are a.e. bounded by the constant. -/
theorem lipschitzWith_ae_norm_partialDeriv_le {K : ℝ≥0} {η : Vec d → ℝ}
    (hη : LipschitzWith K η) (i : Fin d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ‖fderiv ℝ η x (basisVec i)‖ ≤ K := by
  refine Filter.Eventually.of_forall fun x => ?_
  have h1 : ‖fderiv ℝ η x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hη
  have h2 : ‖basisVec (d := d) i‖ = 1 := by simp [basisVec, Pi.norm_single]
  calc ‖fderiv ℝ η x (basisVec i)‖ ≤ ‖fderiv ℝ η x‖ * ‖basisVec (d := d) i‖ :=
        (fderiv ℝ η x).le_opNorm _
    _ ≤ K := by rw [h2, mul_one]; exact h1

theorem aestronglyMeasurable_partialDeriv (η : Vec d → ℝ) (i : Fin d) :
    AEStronglyMeasurable (fun x => fderiv ℝ η x (basisVec i)) volume :=
  (measurable_fderiv_apply_const ℝ η (basisVec i)).aestronglyMeasurable

/-- Mollification of an `L²` function by the scaled unit kernel is `L²`. -/
theorem memLp_two_convolution_scaledUnitKernel {g : Vec d → ℝ} (hg : MemLp g 2 volume)
    {a : ℝ} (ha : 0 < a) :
    MemLp (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 2 volume := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hk_compact := hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
  have hconv_cont := hk_compact.continuous_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (continuous_scaledConvexApproxKernel hρ.continuous a)
    (hg.locallyIntegrable (by norm_num))
  exact (young_convolution_nonneg_integral_one_of_aemeasurable (by norm_num) (by norm_num)
    (scaledConvexApproxKernel_nonneg hρ ha) (integrable_scaledConvexApproxKernel hρ ha)
    (integral_scaledConvexApproxKernel hρ ha)
    (measurable_scaledConvexApproxKernel hρ.continuous a) hg.aemeasurable).trans_lt
    hg.eLpNorm_lt_top

/-- Pairing an `L²(U)` function with mollifications converges to the pairing with the limit. -/
theorem tendsto_setIntegral_mul_convolution {G F : Vec d → ℝ} (hG : MemL2On U G)
    (hF : MemLp F 2 volume) {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {ε : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (haε : ∀ n, a n = ε n * δ) (hε : Tendsto ε atTop (𝓝 0))
    (hεp : ∀ᶠ n in atTop, 0 < ε n) :
    Tendsto (fun n => ∫ x in U, G x *
        (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) (a n) ⋆[
          ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x) atTop (𝓝 (∫ x in U, G x * F x)) := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have h := tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel (p := 2) hρ
    (by norm_num) (by norm_num) hF hδ hε hεp
  have h' : Tendsto (fun n => eLpNorm (fun x =>
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) (a n) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] F) x - F x) 2 (volume.restrict U)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => bot_le)
      (fun n => ?_)
    rw [haε n]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have := tendsto_setIntegral_mul_of_tendsto_eLpNorm_two (U := U) hG
    (fun n => (memLp_two_convolution_scaledUnitKernel hF (ha n)).restrict U) (hF.restrict U) h'
  simpa only [mul_comm] using this

/-- **Lipschitz test functions.**  If `ψ` is Lipschitz with compact support in `U` then
`∫_U u ∂ᵢψ = - ∫_U (∂ᵢu) ψ` for every `u ∈ H¹(U)`. -/
theorem H1Function.integral_mul_partial_lip_eq (hU : IsOpen U) (u : H1Function U)
    {K : ℝ≥0} {ψ : Vec d → ℝ} (hψ : LipschitzWith K ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (i : Fin d) :
    ∫ x in U, u.toFun x * fderiv ℝ ψ x (basisVec i) = -∫ x in U, u.grad x i * ψ x := by
  classical
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  obtain ⟨δ, hδ, hδU⟩ := hψc.isCompact.exists_cthickening_subset_open hU hψU
  let a : ℕ → ℝ := fun n => unitConvexApproxScale n * δ
  have hsc : ∀ n, 0 < unitConvexApproxScale n := fun n => by
    unfold unitConvexApproxScale; positivity
  have ha : ∀ n, 0 < a n := fun n => mul_pos (hsc n) hδ
  have haδ : ∀ n, a n ≤ δ := fun n =>
    calc a n ≤ 1 * δ := mul_le_mul_of_nonneg_right (unitConvexApproxScale_le_one n) hδ.le
      _ = δ := one_mul δ
  have hε0 : Tendsto unitConvexApproxScale atTop (𝓝 0) := tendsto_unitConvexApproxScale_zero
  have hεp : ∀ᶠ n in atTop, 0 < unitConvexApproxScale n := Eventually.of_forall hsc
  have hψcont : Continuous ψ := hψ.continuous
  have hψmem : MemLp ψ 2 volume := hψcont.memLp_of_hasCompactSupport hψc
  set Dψ : Vec d → ℝ := fun x => fderiv ℝ ψ x (basisVec i) with hDψ
  have hDzero : ∀ x, x ∉ tsupport ψ → Dψ x = 0 := fun x hx => by
    simp [hDψ, fderiv_of_notMem_tsupport ℝ hx]
  have hDmem : MemLp Dψ 2 volume :=
    memLp_two_of_bounded_of_zero_off (C := K) hψc.isCompact (aestronglyMeasurable_partialDeriv ψ i)
      (lipschitzWith_ae_norm_partialDeriv_le hψ i) hDzero
  have hweak := lipschitzWith_hasWeakPartialDerivOn_univ hψ i
  let k : ℕ → Vec d → ℝ := fun n =>
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) (a n)
  have hkc : ∀ n, HasCompactSupport (k n) := fun n =>
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (ha n)
  have hks : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (k n) := fun n => contDiff_scaledConvexApproxKernel hρ _
  have hk0 : ∀ n y, a n < ‖y‖ → k n y = 0 := fun n y hy =>
    scaledUnitKernel_eq_zero_of_lt_norm (ha n) hy
  let M : ℕ → Vec d → ℝ := fun n => k n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ
  have hMs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (M n) := fun n =>
    (hkc n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hks n)
      (hψmem.locallyIntegrable (by norm_num))
  have hMsupp : ∀ n, Function.support (M n) ⊆ Metric.cthickening (a n) (tsupport ψ) := fun n =>
    support_convolution_subset_cthickening (hk0 n)
  have hMts : ∀ n, tsupport (M n) ⊆ Metric.cthickening (a n) (tsupport ψ) := fun n =>
    closure_minimal (hMsupp n) Metric.isClosed_cthickening
  have hMc : ∀ n, HasCompactSupport (M n) := fun n =>
    HasCompactSupport.of_support_subset_isCompact (hψc.isCompact.cthickening (r := a n)) (hMsupp n)
  have hMU : ∀ n, tsupport (M n) ⊆ U := fun n =>
    (hMts n).trans ((Metric.cthickening_mono (haδ n) _).trans hδU)
  have hderiv : ∀ n x, fderiv ℝ (M n) x (basisVec i) =
      (k n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Dψ) x := fun n x =>
    fderiv_convolution_eq_of_hasWeakPartialDerivOn (hkc n) (hks n)
      (hψmem.locallyIntegrable (by norm_num)) hweak x
  have hid : ∀ n, ∫ x in U, u.toFun x * (k n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Dψ) x =
      -∫ x in U, u.grad x i * M n x := fun n => by
    have := u.hasWeakGradient i (M n) (hMs n) (hMc n) (hMU n)
    simpa only [hderiv] using this
  have h1 := tendsto_setIntegral_mul_convolution (U := U) u.memL2 hDmem ha hδ
    (fun n => rfl) hε0 hεp
  have h2 := tendsto_setIntegral_mul_convolution (U := U) (u.gradMemL2 i) hψmem ha hδ
    (fun n => rfl) hε0 hεp
  exact tendsto_nhds_unique (h1.congr fun n => hid n) h2.neg

end SuperdiffusionCLT.Section7
