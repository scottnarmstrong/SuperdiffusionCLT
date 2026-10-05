/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ConvolutionLp
public import Homogenization.Sobolev.W1p.GlobalMollifierLp
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryLayer
public import SuperdiffusionCLT.Section7.Analytic.Morrey.ZeroTrace

/-!
# Boundary-layer Poincare inequality: the vertical estimate

Ingredients for `Section7.exists_layerPoincare`:

* a one-dimensional estimate along the chart direction `e`: a `C^1` function vanishing at
  the end of each vertical segment of length `L` through `y ∈ A` satisfies
  `∫_A |g|^q ≤ L^q ∫_B |∇g|^q`, for every `q ≥ 1`;
* the localized Young inequality for convolution with the scaled mollifier;
* the chart lemma: in a `C^{1,1}` chart, a `C^1` function vanishing above the graph shifted by
  `κ a` satisfies the layer estimate with `L = κ (ρ + a)`.
-/

@[expose] public section

open MeasureTheory Homogenization Convolution
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-! ### The vertical estimate -/

/-- Fundamental theorem of calculus along a segment `y + τ e`, `0 ≤ τ ≤ T`, ending at a zero. -/
theorem layerPoincare_enorm_le_lintegral_line {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) {e : Vec d}
    (he : ‖e‖ ≤ 1) {y : Vec d} {T L : ℝ} (hT0 : 0 ≤ T) (hTL : T ≤ L)
    (hz : g (y + T • e) = 0) :
    ‖g y‖ₑ ≤ ∫⁻ τ in Set.Icc 0 L, ‖fderiv ℝ g (y + τ • e)‖ₑ := by
  set φ : ℝ → ℝ := fun τ => g (y + τ • e) with hφ
  have hder : ∀ τ, HasDerivAt φ (fderiv ℝ g (y + τ • e) e) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => y + τ • e) e τ := by
      simpa using ((hasDerivAt_id τ).smul_const e).const_add y
    exact ((hg.differentiable one_ne_zero) (y + τ • e)).hasFDerivAt.comp_hasDerivAt τ h1
  have hcont : Continuous fun τ : ℝ => fderiv ℝ g (y + τ • e) e := by
    have : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
    exact (this.comp (by fun_prop)).clm_apply continuous_const
  have hftc : ∫ τ in (0 : ℝ)..T, fderiv ℝ g (y + τ • e) e = φ T - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hder τ)
      (hcont.intervalIntegrable _ _)
  have hφT : φ T = 0 := hz
  have hφ0 : φ 0 = g y := by simp [hφ]
  have h1 : ‖g y‖ₑ = ‖∫ τ in Set.Ioc 0 T, fderiv ℝ g (y + τ • e) e‖ₑ := by
    rw [← intervalIntegral.integral_of_le hT0, hftc, hφT, hφ0, zero_sub, enorm_neg]
  rw [h1]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine (lintegral_mono fun τ => ?_).trans
    (lintegral_mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right hTL)))
  have hle : ‖fderiv ℝ g (y + τ • e) e‖ ≤ ‖fderiv ℝ g (y + τ • e)‖ :=
    ((fderiv ℝ g (y + τ • e)).le_opNorm e).trans
      (mul_le_of_le_one_right (norm_nonneg _) he)
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hle

/-- Hölder on an interval: `(∫ f)^q ≤ L^(q-1) ∫ f^q`. -/
theorem layerPoincare_lintegral_Icc_rpow_le {f : ℝ → ℝ≥0∞} {L q : ℝ} (hq : 1 ≤ q)
    (hf : AEMeasurable f (volume.restrict (Set.Icc 0 L))) :
    (∫⁻ τ in Set.Icc 0 L, f τ) ^ q ≤
      ENNReal.ofReal L ^ (q - 1) * ∫⁻ τ in Set.Icc 0 L, f τ ^ q := by
  rcases hq.eq_or_lt with h | h
  · subst h
    simp
  have hq0 : 0 < q := by linarith only [h]
  have hH : q.HolderConjugate q.conjExponent := Real.HolderConjugate.conjExponent h
  have hmain := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) L)) hH hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc, sub_zero,
    one_mul] at hmain
  have h2 := ENNReal.rpow_le_rpow hmain hq0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  have e1 : 1 / q * q = 1 := by field_simp
  have e2 : 1 / q.conjExponent * q = q - 1 := by
    rw [Real.conjExponent]
    field_simp
  rw [e1, e2, ENNReal.rpow_one] at h2
  rw [mul_comm]
  exact h2

/-- **The vertical estimate.** If every point of `A` is joined, by a segment `y + τ e`, `0 ≤ τ ≤ L`,
inside `B`, to a zero of the `C^1` function `g`, then `∫_A |g|^q ≤ L^q ∫_B |∇g|^q`. -/
theorem layerPoincare_vertical {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) {e : Vec d} (he : ‖e‖ ≤ 1)
    {q L : ℝ} (hq : 1 ≤ q) {A : Set (Vec d)} (hA : MeasurableSet A)
    {B : Set (Vec d)} (hBm : MeasurableSet B)
    (hT : ∀ y ∈ A, ∃ T, 0 ≤ T ∧ T ≤ L ∧ g (y + T • e) = 0)
    (hB : ∀ y ∈ A, ∀ τ ∈ Set.Icc (0 : ℝ) L, y + τ • e ∈ B) :
    ∫⁻ y in A, ‖g y‖ₑ ^ q ≤
      ENNReal.ofReal L ^ q * ∫⁻ w in B, ‖fderiv ℝ g w‖ₑ ^ q := by
  have hq0 : 0 < q := by linarith only [hq]
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hmeas : Measurable fun w => ‖fderiv ℝ g w‖ₑ ^ q := hDc.enorm.measurable.pow_const q
  have hmeas' : Measurable fun w => ‖fderiv ℝ g w‖ₑ := hDc.enorm.measurable
  have hpt : ∀ y ∈ A, ‖g y‖ₑ ^ q ≤ ENNReal.ofReal L ^ (q - 1) *
      ∫⁻ τ in Set.Icc (0 : ℝ) L, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q := by
    intro y hy
    obtain ⟨T, hT0, hTL, hz⟩ := hT y hy
    have h1 := layerPoincare_enorm_le_lintegral_line hg he hT0 hTL hz
    refine (ENNReal.rpow_le_rpow h1 hq0.le).trans ?_
    refine layerPoincare_lintegral_Icc_rpow_le hq ?_
    exact (hmeas'.comp (by fun_prop : Measurable fun τ : ℝ => y + τ • e)).aemeasurable
  have hstep1 : ∫⁻ y in A, ‖g y‖ₑ ^ q ≤ ∫⁻ y in A, ENNReal.ofReal L ^ (q - 1) *
      ∫⁻ τ in Set.Icc (0 : ℝ) L, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q :=
    setLIntegral_mono' hA hpt
  have hjoint : Measurable fun p : Vec d × ℝ => ‖fderiv ℝ g (p.1 + p.2 • e)‖ₑ ^ q :=
    hmeas.comp (by fun_prop)
  have hswap : ∫⁻ y in A, ∫⁻ τ in Set.Icc (0 : ℝ) L, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q =
      ∫⁻ τ in Set.Icc (0 : ℝ) L, ∫⁻ y in A, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q :=
    lintegral_lintegral_swap hjoint.aemeasurable
  have htrans : ∀ τ ∈ Set.Icc (0 : ℝ) L, ∫⁻ y in A, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q ≤
      ∫⁻ w in B, ‖fderiv ℝ g w‖ₑ ^ q := by
    intro τ hτ
    calc ∫⁻ y in A, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q
        = ∫⁻ y, A.indicator (fun y => ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q) y :=
          (lintegral_indicator hA _).symm
      _ ≤ ∫⁻ y, B.indicator (fun w => ‖fderiv ℝ g w‖ₑ ^ q) (y + τ • e) :=
          lintegral_mono fun y => by
            by_cases hy : y ∈ A
            · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hB y hy τ hτ)]
            · rw [Set.indicator_of_notMem hy]
              exact bot_le
      _ = ∫⁻ y, B.indicator (fun w => ‖fderiv ℝ g w‖ₑ ^ q) y :=
          lintegral_add_right_eq_self (fun w => B.indicator (fun w => ‖fderiv ℝ g w‖ₑ ^ q) w)
            (τ • e)
      _ = ∫⁻ w in B, ‖fderiv ℝ g w‖ₑ ^ q := lintegral_indicator hBm _
  have hc : ENNReal.ofReal L ^ (q - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith only [hq]) ENNReal.ofReal_ne_top
  calc ∫⁻ y in A, ‖g y‖ₑ ^ q
      ≤ ∫⁻ y in A, ENNReal.ofReal L ^ (q - 1) *
          ∫⁻ τ in Set.Icc (0 : ℝ) L, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q := hstep1
    _ = ENNReal.ofReal L ^ (q - 1) * ∫⁻ y in A,
          ∫⁻ τ in Set.Icc (0 : ℝ) L, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q :=
        lintegral_const_mul' _ _ hc
    _ = ENNReal.ofReal L ^ (q - 1) * ∫⁻ τ in Set.Icc (0 : ℝ) L,
          ∫⁻ y in A, ‖fderiv ℝ g (y + τ • e)‖ₑ ^ q := by rw [hswap]
    _ ≤ ENNReal.ofReal L ^ (q - 1) * ∫⁻ τ in Set.Icc (0 : ℝ) L,
          ∫⁻ w in B, ‖fderiv ℝ g w‖ₑ ^ q :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Icc htrans) _
    _ = ENNReal.ofReal L ^ (q - 1) * (ENNReal.ofReal L * ∫⁻ w in B, ‖fderiv ℝ g w‖ₑ ^ q) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Icc, sub_zero]
        ring
    _ = ENNReal.ofReal L ^ q * ∫⁻ w in B, ‖fderiv ℝ g w‖ₑ ^ q := by
        rw [← mul_assoc]
        congr 1
        conv_rhs => rw [show q = (q - 1) + 1 by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith only [hq]) zero_le_one,
          ENNReal.rpow_one]

/-! ### Localized Young inequality -/

theorem layerPoincare_lintegral_enorm_rpow_eq {f : Vec d → ℝ} {q : ℝ} (hq : 0 < q)
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ x, ‖f x‖ₑ ^ q = eLpNorm f (ENNReal.ofReal q) volume ^ q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq.ne',
    ENNReal.rpow_one]

/-- Convolution with the scaled mollifier does not increase the `L^q` mass, localized to balls:
the `L^q` integral of `k ⋆ G` over `B(c, R)` is at most that of `G` over `B(c, R + a)`. -/
theorem layerPoincare_young_closedBall {ρ G : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) {a : ℝ}
    (ha : 0 < a) (hG : LocallyIntegrable G volume) {q : ℝ} (hq : 1 ≤ q) (c : Vec d) (R : ℝ) :
    ∫⁻ x in Metric.closedBall c R,
        ‖(scaledConvexApproxKernel ρ a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x‖ₑ ^ q ≤
      ∫⁻ x in Metric.closedBall c (R + a), ‖G x‖ₑ ^ q := by
  have hq0 : 0 < q := by linarith only [hq]
  set k := scaledConvexApproxKernel ρ a with hk
  set S := Metric.closedBall c (R + a) with hS
  have hSm : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hG'loc : LocallyIntegrable (S.indicator G) volume := hG.indicator hSm
  have hG' : AEMeasurable (S.indicator G) volume := hG'loc.aestronglyMeasurable.aemeasurable
  have heq : ∀ x ∈ Metric.closedBall c R,
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G)) x := by
    intro x hx
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases hkt : k t = 0
    · simp [hkt]
    · have ht : ‖t‖ ≤ a := scaledKernel_ne_zero_norm_le hρ ha hkt
      have hxc : ‖x - c‖ ≤ R := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.1 hx
      have hmem : x - t ∈ S := by
        rw [hS, Metric.mem_closedBall, dist_eq_norm]
        calc ‖x - t - c‖ = ‖(x - c) - t‖ := by congr 1; abel
          _ ≤ ‖x - c‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ R + a := add_le_add hxc ht
      simp only [Set.indicator_of_mem hmem]
  have hk0 : ∀ y, 0 ≤ k y := scaledConvexApproxKernel_nonneg hρ ha
  have hk : ContDiff ℝ (⊤ : ℕ∞) k := contDiff_scaledConvexApproxKernel hρ a
  have hkc : HasCompactSupport k :=
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
  have hp1 : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hyoung := young_convolution_nonneg_integral_one_of_aemeasurable hp1 ENNReal.ofReal_ne_top
    hk0 (integrable_scaledConvexApproxKernel hρ ha) (integral_scaledConvexApproxKernel hρ ha)
    (measurable_scaledConvexApproxKernel hρ.continuous a) hG'
  calc ∫⁻ x in Metric.closedBall c R,
        ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x‖ₑ ^ q
      = ∫⁻ x in Metric.closedBall c R,
        ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G)) x‖ₑ ^ q :=
        setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
          (fun x hx => by rw [heq x hx])
    _ ≤ ∫⁻ x, ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G)) x‖ₑ ^ q :=
        setLIntegral_le_lintegral _ _
    _ = eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G))
          (ENNReal.ofReal q) volume ^ q :=
        layerPoincare_lintegral_enorm_rpow_eq hq0
          ((hkc.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
            hk.continuous hG'loc).aestronglyMeasurable)
    _ ≤ eLpNorm (S.indicator G) (ENNReal.ofReal q) volume ^ q :=
        ENNReal.rpow_le_rpow hyoung hq0.le
    _ = ∫⁻ x, ‖S.indicator G x‖ₑ ^ q :=
        (layerPoincare_lintegral_enorm_rpow_eq hq0 hG'loc.aestronglyMeasurable).symm
    _ = ∫⁻ x in S, ‖G x‖ₑ ^ q := by
        rw [← lintegral_indicator hSm]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ S
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hq0]

/-! ### The chart lemma -/

theorem layerPoincare_vecDot_add_smul (e y : Vec d) (T : ℝ) :
    vecDot e (y + T • e) = vecDot e y + T * vecNormSq e := by
  simp only [vecDot, vecNormSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem layerPoincare_proj_add_smul {e : Vec d} (he : vecNormSq e = 1) (y : Vec d) (T : ℝ) :
    (y + T • e) - vecDot e (y + T • e) • e = y - vecDot e y • e := by
  rw [layerPoincare_vecDot_add_smul, he]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The chart lemma.** In a `C^{1,1}` chart at the frontier point `x'`, a `C^1` function `g`
vanishing above the graph shifted by `κ a` satisfies the layer estimate with `L = κ (ρ + a)`,
`κ = d + (1 + d) M₁`, for every measurable `A ⊆ U ∩ B(x', ρ)`. -/
theorem layerPoincare_chart {U : Set (Vec d)} (hU : IsOpen U) {x' : Vec d}
    (hx' : x' ∈ frontier U) {r R : ℝ} {e : Vec d} (he : vecNormSq e = 1) {γ : Vec d → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) {M₁ : ℝ} (hb : ∀ y, ‖fderiv ℝ γ y‖ ≤ M₁)
    (hch : ∀ y ∈ Metric.ball x' r, (y ∈ U ↔ vecDot e y < γ (y - vecDot e y • e)))
    {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) {a ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (hR : ρ + ((d : ℝ) + (1 + d) * M₁) * (ρ + a) < R) (hRr : R ≤ r)
    (hz : ∀ w ∈ Metric.ball x' R,
      γ (w - vecDot e w • e) + ((d : ℝ) + (1 + d) * M₁) * a ≤ vecDot e w → g w = 0)
    {q : ℝ} (hq : 1 ≤ q) {A : Set (Vec d)} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hAb : A ⊆ Metric.ball x' ρ) :
    ∫⁻ y in A, ‖g y‖ₑ ^ q ≤
      ENNReal.ofReal (((d : ℝ) + (1 + d) * M₁) * (ρ + a)) ^ q *
        ∫⁻ w in Metric.closedBall x' R, ‖fderiv ℝ g w‖ₑ ^ q := by
  set κ : ℝ := (d : ℝ) + (1 + d) * M₁ with hκ
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  have hκ0 : 0 ≤ κ := by positivity
  have he1 := norm_le_one_of_vecNormSq he
  have hL0 : 0 ≤ κ * (ρ + a) := by positivity
  have hRpos : 0 < R := by linarith only [hR, hρ, hL0]
  have hrpos : 0 < r := by linarith only [hRr, hRpos]
  have hxb : x' ∈ Metric.ball x' r := Metric.mem_ball_self hrpos
  refine layerPoincare_vertical hg he1 hq hA Metric.isClosed_closedBall.measurableSet ?_ ?_
  · intro y hy
    have hyx : ‖y - x'‖ < ρ := by simpa [dist_eq_norm] using hAb hy
    have hyb : y ∈ Metric.ball x' r := by
      rw [Metric.mem_ball, dist_eq_norm]
      linarith only [hyx, hR, hL0, hRr]
    obtain ⟨hpos, hle⟩ := vertical_dist_le hU he hγ hb hch (hAU hy) hyb hx' hxb
    have hle' : κ * ‖y - x'‖ ≤ κ * ρ := mul_le_mul_of_nonneg_left hyx.le hκ0
    have hka : 0 ≤ κ * a := by positivity
    set T : ℝ := γ (y - vecDot e y • e) - vecDot e y + κ * a with hT
    have hT0 : 0 ≤ T := by linarith only [hpos, hka]
    have hTL : T ≤ κ * (ρ + a) := by
      have : κ * (ρ + a) = κ * ρ + κ * a := by ring
      linarith only [hle, hle', this]
    refine ⟨T, hT0, hTL, hz _ ?_ ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖y + T • e - x'‖ ≤ ‖y - x'‖ + ‖T • e‖ := by
        calc ‖y + T • e - x'‖ = ‖(y - x') + T • e‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖T • e‖ ≤ T := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT0]
        exact mul_le_of_le_one_right hT0 he1
      linarith only [h1, h2, hyx, hTL, hR]
    · rw [layerPoincare_proj_add_smul he, layerPoincare_vecDot_add_smul, he]
      linarith only [hT]
  · intro y hy τ hτ
    have hyx : ‖y - x'‖ < ρ := by simpa [dist_eq_norm] using hAb hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : ‖y + τ • e - x'‖ ≤ ‖y - x'‖ + ‖τ • e‖ := by
      calc ‖y + τ • e - x'‖ = ‖(y - x') + τ • e‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖τ • e‖ ≤ τ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      exact mul_le_of_le_one_right hτ.1 he1
    linarith only [h1, h2, hyx, hτ.2, hR]

end SuperdiffusionCLT.Section7
