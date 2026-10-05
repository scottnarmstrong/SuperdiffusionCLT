/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.MeanZero
public import Homogenization.Sobolev.L2Ambient
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerH1
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerH1B
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerPoincareB

/-!
# Boundary-layer inequality for `H¹` functions: the chart estimate for Sobolev data

The chart estimate of `LayerH1.lean` holds for `C¹` functions.  For `w ∈ H¹(U)` it is obtained by
applying it to the inward mollifications `K_n ⋆ (U.indicator w)`, whose kernels are translated by
`κ a_n e` so that their supports stay inside `U` on the whole chart, and passing to the limit
(`L²` convergence and Fatou on the left, the localized Young inequality on the right).
-/

@[expose] public section

open MeasureTheory Homogenization Convolution Filter Topology
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The inward ball: for `y ∈ U` in the chart and `l ≥ κ a`, the ball of radius `a` about `y - l e`
lies in `U`. -/
theorem hl_closedBall_inward_subset {U : Set (Vec d)} {c : Vec d} {r : ℝ} {e : Vec d}
    (he : vecNormSq e = 1) {γ : Vec d → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) {M₁ : ℝ}
    (hb : ∀ y, ‖fderiv ℝ γ y‖ ≤ M₁)
    (hch : ∀ y ∈ Metric.ball c r, (y ∈ U ↔ vecDot e y < γ (y - vecDot e y • e)))
    {y : Vec d} (hyU : y ∈ U) (hyr : y ∈ Metric.ball c r) {a l : ℝ}
    (hl : ((d : ℝ) + (1 + d) * M₁) * a ≤ l) (hl0 : 0 ≤ l) (hr : ‖y - c‖ + l + a < r) :
    Metric.closedBall (y - l • e) a ⊆ U := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  set δz : Vec d := z - (y - l • e) with hδz
  have hδa : ‖δz‖ ≤ a := hz
  have hzeq : z = (y + δz) + (-l) • e := by
    rw [hδz, neg_smul]
    abel
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  have he1 := norm_le_one_of_vecNormSq he
  have hzr : z ∈ Metric.ball c r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖z - c‖ ≤ ‖y - c‖ + ‖δz‖ + ‖l • e‖ := by
      calc ‖z - c‖ = ‖(y - c) + δz + (-l) • e‖ := by
            congr 1
            rw [hzeq]
            abel
        _ ≤ ‖(y - c) + δz‖ + ‖(-l) • e‖ := norm_add_le _ _
        _ ≤ ‖y - c‖ + ‖δz‖ + ‖(-l) • e‖ := by gcongr; exact norm_add_le _ _
        _ = ‖y - c‖ + ‖δz‖ + ‖l • e‖ := by rw [neg_smul, norm_neg]
    have h2 : ‖l • e‖ ≤ l := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]
      exact mul_le_of_le_one_right hl0 he1
    linarith only [h1, h2, hδa, hr]
  rw [hch z hzr, hzeq, layerPoincare_proj_add_smul he, layerPoincare_vecDot_add_smul, he]
  have hy := (hch y hyr).1 hyU
  have h1 := abs_proj_comp_sub_le he hγ hb (y + δz) y
  have h2 := abs_vecDot_le he δz
  have h3 : ‖y + δz - y‖ ≤ a := by simpa using hδa
  have h4 : (1 + (d : ℝ)) * M₁ * ‖y + δz - y‖ ≤ (1 + (d : ℝ)) * M₁ * a :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : (d : ℝ) * ‖δz‖ ≤ d * a := mul_le_mul_of_nonneg_left hδa (Nat.cast_nonneg d)
  have h6 : vecDot e (y + δz) = vecDot e y + vecDot e δz := by
    have : y + δz = y + δz := rfl
    unfold vecDot
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have h7 := (abs_le.1 (h1.trans h4)).1
  have h8 := (abs_le.1 (h2.trans h5)).2
  have h9 : ((d : ℝ) + (1 + d) * M₁) * a = d * a + (1 + d) * M₁ * a := by ring
  linarith only [hy, h6, h7, h8, h9, hl]

theorem hl_lintegral_indicator_set {U : Set (Vec d)} (hUm : MeasurableSet U) (f : Vec d → ℝ)
    {S : Set (Vec d)} {q : ℝ} (hq : 0 < q) :
    ∫⁻ x in S, ‖U.indicator f x‖ₑ ^ q = ∫⁻ x in U ∩ S, ‖f x‖ₑ ^ q := by
  have h : ∀ x, ‖U.indicator f x‖ₑ ^ q = U.indicator (fun x => ‖f x‖ₑ ^ q) x := by
    intro x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hq]
  simp_rw [h]
  rw [lintegral_indicator hUm, Measure.restrict_restrict hUm]

/-- The zero extension of an `H¹(U)` function and of its gradient (and the norm majorant) are
`L²`, hence locally integrable, on the whole space. -/
theorem hl_memLp_extensions {U : Set (Vec d)} (hUm : MeasurableSet U) (w : H1Function U) :
    MemLp (U.indicator w.toFun) 2 volume ∧
      (∀ i, MemLp (U.indicator fun x => w.grad x i) 2 volume) ∧
      MemLp (U.indicator fun x => (d : ℝ) * ‖w.grad x‖) 2 volume := by
  have h1 : MemLp (U.indicator w.toFun) 2 volume :=
    (memLp_indicator_iff_restrict hUm).2 w.memL2
  have h2 : ∀ i, MemLp (U.indicator fun x => w.grad x i) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hUm).2 (w.gradMemL2 i)
  refine ⟨h1, h2, ?_⟩
  have h3 := layerPoincare_memLp_gradNorm (Du := fun x => fun i => U.indicator (fun y => w.grad y i) x)
    h2
  convert h3 using 1
  ext x
  by_cases hx : x ∈ U
  · simp [Set.indicator_of_mem hx]
  · have h0 : (fun i : Fin d => (0 : ℝ)) = 0 := rfl
    simp only [Set.indicator_of_notMem hx, h0, norm_zero, mul_zero]

/-- **The chart estimate for `H¹` data.** -/
theorem hl_chart_h1 {U : Set (Vec d)} (hU : IsOpen U) (w : H1Function U) {c : Vec d} {r : ℝ}
    {e : Vec d} (he : vecNormSq e = 1) {γ : Vec d → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) {M₁ : ℝ}
    (hb : ∀ y, ‖fderiv ℝ γ y‖ ≤ M₁)
    (hch : ∀ y ∈ Metric.ball c r, (y ∈ U ↔ vecDot e y < γ (y - vecDot e y • e)))
    {ρ σ₀ σ₁ ℓ R' : ℝ} (hσ₀ : 0 ≤ σ₀) (hσ : σ₀ ≤ σ₁) (hR : ρ + σ₁ < R') (hR' : R' < r)
    {A : Set (Vec d)} (hA : MeasurableSet A) (hAU : A ⊆ U) (hAb : A ⊆ Metric.ball c ρ)
    (hAℓ : ∀ y ∈ A, γ (y - vecDot e y • e) - vecDot e y ≤ ℓ) :
    ENNReal.ofReal (σ₁ - σ₀) * ∫⁻ y in A, ‖w.toFun y‖ₑ ^ (2 : ℝ) ≤
      2 * ENNReal.ofReal ℓ * (∫⁻ z in U ∩ Metric.closedBall c R', ‖w.toFun z‖ₑ ^ (2 : ℝ)) +
        2 * ENNReal.ofReal (σ₁ - σ₀) * ENNReal.ofReal σ₁ * ENNReal.ofReal ℓ *
          ∫⁻ z in U ∩ Metric.closedBall c R', ‖(d : ℝ) * ‖w.grad z‖‖ₑ ^ (2 : ℝ) := by
  have hUm : MeasurableSet U := hU.measurableSet
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  have he1 := norm_le_one_of_vecNormSq he
  set κ : ℝ := (d : ℝ) + (1 + d) * M₁ with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with ha
  have hapos : ∀ n, 0 < a n := fun n => by simp only [ha]; positivity
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set l : ℕ → ℝ := fun n => κ * a n with hl
  have hl0 : ∀ n, 0 ≤ l n := fun n => mul_nonneg hκ0 (hapos n).le
  set K : ℕ → Vec d → ℝ := fun n => hl_kernel (a n) (l n) e with hK
  set δ : ℕ → ℝ := fun n => 2 * (l n + a n) with hδ
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    have : Tendsto (fun n => 2 * (κ * a n + a n)) atTop (𝓝 (2 * (κ * 0 + 0))) :=
      ((ha0.const_mul κ).add ha0).const_mul 2
    simpa using this
  obtain ⟨hwt, hDt, hGt⟩ := hl_memLp_extensions hUm w
  set wt : Vec d → ℝ := U.indicator w.toFun with hwtdef
  have hwtloc : LocallyIntegrable wt volume := hwt.locallyIntegrable (by norm_num)
  have hDtloc : ∀ i, LocallyIntegrable (U.indicator fun x => w.grad x i) volume := fun i =>
    (hDt i).locallyIntegrable (by norm_num)
  have hGtloc : LocallyIntegrable (U.indicator fun x => (d : ℝ) * ‖w.grad x‖) volume :=
    hGt.locallyIntegrable (by norm_num)
  have hKcont : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (K n) := fun n => hl_kernel_contDiff _ _
  have hKcs : ∀ n, HasCompactSupport (K n) := fun n => hl_kernel_hasCompactSupport (hapos n) _ _
  have hKnn : ∀ n y, 0 ≤ K n y := fun n y => hl_kernel_nonneg (hapos n) _ _ y
  have hKint : ∀ n, Integrable (K n) volume := fun n => hl_kernel_integrable (hapos n) _ _
  have hK1 : ∀ n, ∫ y, K n y = 1 := fun n => hl_kernel_integral (hapos n) _ _
  have hKs : ∀ n y, K n y ≠ 0 → ‖y‖ ≤ l n + a n := fun n y hy =>
    hl_kernel_norm_le (hapos n) (hl0 n) he1 hy
  set g : ℕ → Vec d → ℝ := fun n => K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] wt with hg
  have hgsm : ∀ n, ContDiff ℝ 1 (g n) := fun n =>
    (HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hKcs n)
      (hKcont n) hwtloc).of_le (by exact_mod_cast le_top)
  set I1 : ℝ≥0∞ := ∫⁻ z in U ∩ Metric.closedBall c R', ‖w.toFun z‖ₑ ^ (2 : ℝ) with hI1
  set I2 : ℝ≥0∞ := ∫⁻ z in U ∩ Metric.closedBall c R', ‖(d : ℝ) * ‖w.grad z‖‖ₑ ^ (2 : ℝ) with hI2
  set T : ℝ≥0∞ := 2 * ENNReal.ofReal ℓ * I1 + 2 * ENNReal.ofReal (σ₁ - σ₀) * ENNReal.ofReal σ₁ *
    ENNReal.ofReal ℓ * I2 with hT
  have hRr : ρ + σ₁ < r := by linarith only [hR, hR']
  have hev : ∀ᶠ n in atTop, (κ + 1) * a n < R' - (ρ + σ₁) := by
    have h0 : Tendsto (fun n => (κ + 1) * a n) atTop (𝓝 ((κ + 1) * 0)) := ha0.const_mul _
    rw [mul_zero] at h0
    exact (tendsto_order.1 h0).2 _ (by linarith only [hR])
  have hbound : ∀ n, (κ + 1) * a n < R' - (ρ + σ₁) →
      ENNReal.ofReal (σ₁ - σ₀) * ∫⁻ y in A, ‖g n y‖ₑ ^ (2 : ℝ) ≤ T := by
    intro n hn
    have hlsum : l n + a n = (κ + 1) * a n := by simp only [hl]; ring
    have hchart := hl_chart_c1 hU he hch (hgsm n) hσ₀ hσ hRr hA hAU hAb hAℓ
    set B : Set (Vec d) := U ∩ Metric.closedBall c (ρ + σ₁) with hB
    have hBm : MeasurableSet B := hUm.inter Metric.isClosed_closedBall.measurableSet
    have hyoung1 := hl_young_closedBall (K := K n) (G := wt) (hKnn n) (hKint n) (hK1 n)
      (hKcont n).continuous.measurable (hKcont n).continuous (hKcs n) (δ := l n + a n) (hKs n)
      hwtloc c (ρ + σ₁)
    have hyoung2 := hl_young_closedBall (K := K n) (G := U.indicator fun x => (d : ℝ) * ‖w.grad x‖)
      (hKnn n) (hKint n) (hK1 n) (hKcont n).continuous.measurable (hKcont n).continuous (hKcs n)
      (δ := l n + a n) (hKs n) hGtloc c (ρ + σ₁)
    have hrad : ρ + σ₁ + (l n + a n) ≤ R' := by linarith only [hlsum, hn]
    have hB1 : ∫⁻ z in B, ‖g n z‖ₑ ^ (2 : ℝ) ≤ I1 := by
      calc ∫⁻ z in B, ‖g n z‖ₑ ^ (2 : ℝ)
          ≤ ∫⁻ z in Metric.closedBall c (ρ + σ₁), ‖g n z‖ₑ ^ (2 : ℝ) :=
            lintegral_mono_set Set.inter_subset_right
        _ ≤ ∫⁻ z in Metric.closedBall c (ρ + σ₁ + (l n + a n)), ‖wt z‖ₑ ^ (2 : ℝ) := hyoung1
        _ ≤ ∫⁻ z in Metric.closedBall c R', ‖wt z‖ₑ ^ (2 : ℝ) :=
            lintegral_mono_set (Metric.closedBall_subset_closedBall hrad)
        _ = I1 := hl_lintegral_indicator_set hUm w.toFun (by norm_num)
    have hB2 : ∫⁻ z in B, ‖fderiv ℝ (g n) z‖ₑ ^ (2 : ℝ) ≤ I2 := by
      have hpt : ∀ z ∈ B, ‖fderiv ℝ (g n) z‖ₑ ^ (2 : ℝ) ≤
          ‖(K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (U.indicator fun x => (d : ℝ) * ‖w.grad x‖)) z‖ₑ ^ (2 : ℝ) := by
        intro z hz
        have hzc : ‖z - c‖ ≤ ρ + σ₁ := by simpa [dist_eq_norm] using hz.2
        have hzr : z ∈ Metric.ball c r := by
          rw [Metric.mem_ball, dist_eq_norm]
          linarith only [hzc, hRr]
        have hsub : tsupport (fun y => K n (z - y)) ⊆ U :=
          (hl_kernel_reflect_subset (hapos n) (l n) e z).trans
            (hl_closedBall_inward_subset he hγ hb hch hz.1 hzr (a := a n) (l := l n)
              (le_of_eq (by simp only [hl, hκ])) (hl0 n)
              (by linarith only [hzc, hlsum, hn, hR']))
        have hbd := hl_norm_fderiv_conv_le hUm (hKcont n) (hKcs n) (hKnn n)
          (w := w.toFun) (Du := w.grad) hwtloc w.hasWeakGradient hDtloc hGtloc z hsub
        have hH0 : 0 ≤ (K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (U.indicator fun x => (d : ℝ) * ‖w.grad x‖)) z := by
          rw [convolution_def]
          refine integral_nonneg fun t => mul_nonneg (hKnn n t) ?_
          by_cases hy : z - t ∈ U
          · simp only [Set.indicator_of_mem hy]; positivity
          · simp [Set.indicator_of_notMem hy]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg hH0]
        exact ENNReal.ofReal_le_ofReal hbd
      calc ∫⁻ z in B, ‖fderiv ℝ (g n) z‖ₑ ^ (2 : ℝ)
          ≤ ∫⁻ z in B, ‖(K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (U.indicator fun x => (d : ℝ) * ‖w.grad x‖)) z‖ₑ ^ (2 : ℝ) :=
            setLIntegral_mono' hBm hpt
        _ ≤ ∫⁻ z in Metric.closedBall c (ρ + σ₁), ‖(K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            (U.indicator fun x => (d : ℝ) * ‖w.grad x‖)) z‖ₑ ^ (2 : ℝ) :=
            lintegral_mono_set Set.inter_subset_right
        _ ≤ ∫⁻ z in Metric.closedBall c (ρ + σ₁ + (l n + a n)),
            ‖(U.indicator fun x => (d : ℝ) * ‖w.grad x‖) z‖ₑ ^ (2 : ℝ) := hyoung2
        _ ≤ ∫⁻ z in Metric.closedBall c R',
            ‖(U.indicator fun x => (d : ℝ) * ‖w.grad x‖) z‖ₑ ^ (2 : ℝ) :=
            lintegral_mono_set (Metric.closedBall_subset_closedBall hrad)
        _ = I2 := hl_lintegral_indicator_set hUm (fun x => (d : ℝ) * ‖w.grad x‖) (by norm_num)
    refine hchart.trans ?_
    rw [hT]
    gcongr
  -- passage to the limit
  have hconv := hl_tendsto_conv_sub hδ0 hKnn hKint hK1
    (fun n y hy => by
      have := hKs n y hy
      have hp := hapos n
      simp only [hδ]
      linarith only [this, hp, hl0 n])
    (fun n => (hKcont n).continuous) hKcs hwt
  have hmeasconv : TendstoInMeasure volume g atTop wt :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, hns, hae⟩ := hmeasconv.exists_seq_tendsto_ae
  have hlim : ∀ᵐ x ∂(volume.restrict A), Tendsto
      (fun i => ENNReal.ofReal (σ₁ - σ₀) * ‖g (ns i) x‖ₑ ^ (2 : ℝ)) atTop
      (𝓝 (ENNReal.ofReal (σ₁ - σ₀) * ‖wt x‖ₑ ^ (2 : ℝ))) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    exact (ENNReal.continuous_rpow_const (y := 2)).tendsto _ |>.comp
      ((continuous_enorm.tendsto _).comp hx)
  have hmeasg : ∀ i, Measurable fun y => ENNReal.ofReal (σ₁ - σ₀) * ‖g (ns i) y‖ₑ ^ (2 : ℝ) :=
    fun i => ((hgsm (ns i)).continuous.enorm.measurable.pow_const _).const_mul _
  have hevns : ∀ᶠ i in atTop, (κ + 1) * a (ns i) < R' - (ρ + σ₁) :=
    hns.tendsto_atTop.eventually hev
  calc ENNReal.ofReal (σ₁ - σ₀) * ∫⁻ y in A, ‖w.toFun y‖ₑ ^ (2 : ℝ)
      = ∫⁻ y in A, ENNReal.ofReal (σ₁ - σ₀) * ‖wt y‖ₑ ^ (2 : ℝ) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun hA (fun y hy => ?_)
        simp only [hwtdef, Set.indicator_of_mem (hAU hy)]
    _ = ∫⁻ y in A, liminf (fun i => ENNReal.ofReal (σ₁ - σ₀) * ‖g (ns i) y‖ₑ ^ (2 : ℝ))
          atTop :=
        lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun i => ∫⁻ y in A, ENNReal.ofReal (σ₁ - σ₀) * ‖g (ns i) y‖ₑ ^ (2 : ℝ)) atTop :=
        lintegral_liminf_le hmeasg
    _ ≤ T := by
        refine le_trans liminf_le_limsup (limsup_le_of_le (h := ?_))
        filter_upwards [hevns] with i hi
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact hbound _ hi

/-! ### Summing over a grid of cells -/

open scoped Classical in
/-- Cells of side `t` with anchors within `t` of one of their points: the balls of radius `R'` about
the anchors of the nonempty cells overlap at most `(2 Bn + 1)^d` times. -/
theorem hl_cell_sum {U : Set (Vec d)} {t : ℝ} (ht : 0 < t) {R' : ℝ}
    {Bn : ℕ} (hBn : (R' + t) / t ≤ Bn) (A : (Fin d → ℤ) → Set (Vec d))
    (c : (Fin d → ℤ) → Vec d) (hcell : ∀ k, ∀ y ∈ A k, ∀ i, ⌊y i / t⌋ = k i)
    (hanch : ∀ k, (A k).Nonempty → ∃ y₀ ∈ A k, ‖y₀ - c k‖ < t) {F : Vec d → ℝ≥0∞}
    (hF : AEMeasurable F (volume.restrict U)) :
    ∑' k, (if (A k).Nonempty then ∫⁻ z in U ∩ Metric.closedBall (c k) R', F z else 0) ≤
      (((2 * Bn + 1) ^ d : ℕ) : ℝ≥0∞) * ∫⁻ z in U, F z := by
  classical
  set S : (Fin d → ℤ) → Set (Vec d) :=
    fun k => if (A k).Nonempty then Metric.closedBall (c k) R' else ∅ with hS
  have hSm : ∀ k, MeasurableSet (S k) := fun k => by
    by_cases hk : (A k).Nonempty
    · simp only [hS, hk, ↓reduceIte]
      exact Metric.isClosed_closedBall.measurableSet
    · simp only [hS, hk, ↓reduceIte]
      exact MeasurableSet.empty
  have hconv : ∀ k, (if (A k).Nonempty then ∫⁻ z in U ∩ Metric.closedBall (c k) R', F z else 0) =
      ∫⁻ z in U, (S k).indicator F z := by
    intro k
    rw [lintegral_indicator (hSm k), Measure.restrict_restrict (hSm k)]
    by_cases hk : (A k).Nonempty
    · simp only [hS, hk, ↓reduceIte, Set.inter_comm]
    · simp only [hS, hk, ↓reduceIte, Set.empty_inter, Measure.restrict_empty, lintegral_zero_measure]
  set Nn : ℕ := (2 * Bn + 1) ^ d with hNn
  have hpt : ∀ z, ∑' k, (S k).indicator F z ≤ (Nn : ℝ≥0∞) * F z := by
    intro z
    set P := Fintype.piFinset fun i : Fin d =>
      Finset.Icc (⌊z i / t⌋ - (Bn : ℤ)) (⌊z i / t⌋ + (Bn : ℤ)) with hP
    have hmem : ∀ k, z ∈ S k → k ∈ P := by
      intro k hk
      by_cases hne : (A k).Nonempty
      · obtain ⟨y₀, hy₀, hy₀c⟩ := hanch k hne
        simp only [hS, hne, ↓reduceIte, Metric.mem_closedBall, dist_eq_norm] at hk
        refine layerPoincare_box ht (m := (R' + t) / t) hBn ?_ (hcell k y₀ hy₀)
        calc ‖z - y₀‖ = ‖(z - c k) + (c k - y₀)‖ := by congr 1; abel
          _ ≤ ‖z - c k‖ + ‖c k - y₀‖ := norm_add_le _ _
          _ < (R' + t) / t * t := by
              rw [norm_sub_rev (c k) y₀, div_mul_cancel₀ _ ht.ne']
              linarith only [hk, hy₀c]
      · simp only [hS, hne, ↓reduceIte] at hk
        exact absurd hk (Set.notMem_empty z)
    rw [tsum_eq_sum (s := P) (fun k hk => by
      rw [Set.indicator_of_notMem]
      exact fun hz => hk (hmem k hz))]
    calc ∑ k ∈ P, (S k).indicator F z ≤ ∑ k ∈ P, F z :=
          Finset.sum_le_sum fun k _ => Set.indicator_le_self _ _ z
      _ = P.card • F z := Finset.sum_const _
      _ = (Nn : ℝ≥0∞) * F z := by
          rw [nsmul_eq_mul, hP, layerPoincare_card_box]
  calc ∑' k, (if (A k).Nonempty then ∫⁻ z in U ∩ Metric.closedBall (c k) R', F z else 0)
      = ∑' k, ∫⁻ z in U, (S k).indicator F z := tsum_congr hconv
    _ = ∫⁻ z in U, ∑' k, (S k).indicator F z :=
        (lintegral_tsum fun k => hF.indicator (hSm k)).symm
    _ ≤ ∫⁻ z in U, (Nn : ℝ≥0∞) * F z := lintegral_mono hpt
    _ = (Nn : ℝ≥0∞) * ∫⁻ z in U, F z := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top Nn)

/-- The cell grid assembly for `s ≤ r / 16`. -/
theorem hl_layer_small [NeZero d] {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (w : H1Function U) {s : ℝ} (hsr : 16 * s ≤ r) :
    ENNReal.ofReal (r / 4) * ∫⁻ x in boundaryLayer U s, ‖w.toFun x‖ₑ ^ (2 : ℝ) ≤
      (((2 * 13 + 1) ^ d : ℕ) : ℝ≥0∞) *
        (2 * ENNReal.ofReal (((d : ℝ) + (1 + d) * M₁) * s) * (∫⁻ z in U, ‖w.toFun z‖ₑ ^ (2 : ℝ)) +
          2 * ENNReal.ofReal (r / 4) * ENNReal.ofReal (r / 2) *
            ENNReal.ofReal (((d : ℝ) + (1 + d) * M₁) * s) *
            ∫⁻ z in U, ‖(d : ℝ) * ‖w.grad z‖‖ₑ ^ (2 : ℝ)) := by
  classical
  have hU : IsOpen U := h.1
  have hUm : MeasurableSet U := hU.measurableSet
  have hr : 0 < r := h.2.1
  set κ : ℝ := (d : ℝ) + (1 + d) * M₁ with hκ
  set t : ℝ := r / 16 with htdef
  have ht : 0 < t := by positivity
  have hst : s ≤ t := by rw [htdef]; linarith only [hsr]
  set L : Set (Vec d) := boundaryLayer U s with hL
  have hLo : IsOpen L := layerPoincare_isOpen_boundaryLayer hU s
  have hLm : MeasurableSet L := hLo.measurableSet
  set cell : (Fin d → ℤ) → Set (Vec d) := fun k => {y | ∀ i, ⌊y i / t⌋ = k i} with hcell
  set A : (Fin d → ℤ) → Set (Vec d) := fun k => L ∩ cell k with hA
  have hcellm : ∀ k, MeasurableSet (cell k) := by
    intro k
    have : cell k = ⋂ i, (fun y : Vec d => ⌊y i / t⌋) ⁻¹' {k i} := by
      ext y; simp [hcell]
    rw [this]
    exact MeasurableSet.iInter fun i => by
      have hd : Measurable fun y : Vec d => y i / t := by fun_prop
      have hm : Measurable fun y : Vec d => ⌊y i / t⌋ := Int.measurable_floor.comp hd
      exact hm (measurableSet_singleton _)
  have hAm : ∀ k, MeasurableSet (A k) := fun k => hLm.inter (hcellm k)
  have hcover : L ⊆ ⋃ k, A k := fun y hy =>
    Set.mem_iUnion.2 ⟨fun i => ⌊y i / t⌋, hy, fun i => rfl⟩
  by_cases hU0 : U = ∅
  · have : L = ∅ := Set.eq_empty_of_forall_notMem fun x hx => by
      have := hx.1
      rw [hU0] at this
      exact this
    rw [this]
    simp
  have hne : (frontier U).Nonempty := layerPoincare_frontier_nonempty h.2.2.1 hU0
  have hanch : ∀ k, ∃ c : Vec d, (A k).Nonempty →
      c ∈ frontier U ∧ ∃ y₀ ∈ A k, ‖y₀ - c‖ < t := by
    intro k
    by_cases hk : (A k).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hk
      obtain ⟨c, hc, hcd⟩ := isClosed_frontier.exists_infDist_eq_dist hne y₀
      refine ⟨c, fun _ => ⟨hc, y₀, hy₀, ?_⟩⟩
      have := hy₀.1.2
      rw [hcd, dist_eq_norm] at this
      linarith only [this, hst]
    · exact ⟨0, fun h => absurd h hk⟩
  choose c hc using hanch
  set F1 : Vec d → ℝ≥0∞ := fun z => ‖w.toFun z‖ₑ ^ (2 : ℝ) with hF1
  set F2 : Vec d → ℝ≥0∞ := fun z => ‖(d : ℝ) * ‖w.grad z‖‖ₑ ^ (2 : ℝ) with hF2
  have hmeasw : AEStronglyMeasurable w.toFun (volume.restrict U) := w.memL2.aestronglyMeasurable
  have hmeasg : AEStronglyMeasurable w.grad (volume.restrict U) :=
    (aemeasurable_pi_iff.2 fun i =>
      (w.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hF1m : AEMeasurable F1 (volume.restrict U) := hmeasw.enorm.pow_const _
  have hF2m : AEMeasurable F2 (volume.restrict U) :=
    (hmeasg.norm.const_mul (d : ℝ)).enorm.pow_const _
  set Q1 : (Fin d → ℤ) → ℝ≥0∞ := fun k =>
    if (A k).Nonempty then ∫⁻ z in U ∩ Metric.closedBall (c k) (3 * r / 4), F1 z else 0 with hQ1
  set Q2 : (Fin d → ℤ) → ℝ≥0∞ := fun k =>
    if (A k).Nonempty then ∫⁻ z in U ∩ Metric.closedBall (c k) (3 * r / 4), F2 z else 0 with hQ2
  have hper : ∀ k, ENNReal.ofReal (r / 4) * ∫⁻ y in A k, F1 y ≤
      2 * ENNReal.ofReal (κ * s) * Q1 k +
        2 * ENNReal.ofReal (r / 4) * ENNReal.ofReal (r / 2) * ENNReal.ofReal (κ * s) * Q2 k := by
    intro k
    by_cases hk : (A k).Nonempty
    · obtain ⟨hcF, y₀, hy₀, hy₀c⟩ := hc k hk
      obtain ⟨e, γ, he, hγ, hb, -, hch⟩ := h.2.2.2 (c k) hcF
      have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
      have hκ0 : 0 ≤ κ := by positivity
      have hAU : A k ⊆ U := fun y hy => hy.1.1
      have hAb : A k ⊆ Metric.ball (c k) (2 * t) := by
        intro y hy
        have hyy : ‖y - y₀‖ < t := by
          refine (pi_norm_lt_iff ht).2 fun i => ?_
          rw [Real.norm_eq_abs]
          exact abs_sub_lt_of_floor_eq ht ((hy.2 i).trans (hy₀.2 i).symm)
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖y - c k‖ = ‖(y - y₀) + (y₀ - c k)‖ := by congr 1; abel
          _ ≤ ‖y - y₀‖ + ‖y₀ - c k‖ := norm_add_le _ _
          _ < 2 * t := by linarith only [hyy, hy₀c]
      have hAℓ : ∀ y ∈ A k, γ (y - vecDot e y • e) - vecDot e y ≤ κ * s := by
        intro y hy
        have hyb : y ∈ Metric.ball (c k) r := by
          have := hAb hy
          rw [Metric.mem_ball] at this ⊢
          linarith only [this, htdef, hr]
        obtain ⟨x'', hx'', hxd⟩ := isClosed_frontier.exists_infDist_eq_dist hne y
        have hdy : dist y x'' < s := by rw [← hxd]; exact hy.1.2
        have hx''b : x'' ∈ Metric.ball (c k) r := by
          have h1 := hAb hy
          rw [Metric.mem_ball, dist_eq_norm] at h1 ⊢
          have h2 : ‖x'' - c k‖ ≤ ‖y - x''‖ + ‖y - c k‖ := by
            calc ‖x'' - c k‖ = ‖-(y - x'') + (y - c k)‖ := by congr 1; abel
              _ ≤ ‖-(y - x'')‖ + ‖y - c k‖ := norm_add_le _ _
              _ = ‖y - x''‖ + ‖y - c k‖ := by rw [norm_neg]
          rw [dist_eq_norm] at hdy
          linarith only [h1, h2, hdy, hst, htdef, hr]
        have := (vertical_dist_le hU he hγ hb hch hy.1.1 hyb hx'' hx''b).2
        rw [dist_eq_norm] at hdy
        calc _ ≤ _ := this
          _ ≤ κ * s := mul_le_mul_of_nonneg_left hdy.le hκ0
      have hchart := hl_chart_h1 hU w he hγ hb hch (ρ := 2 * t) (σ₀ := r / 4) (σ₁ := r / 2)
        (ℓ := κ * s) (R' := 3 * r / 4) (by positivity) (by linarith only [hr])
        (by rw [htdef]; linarith only [hr]) (by linarith only [hr]) (hAm k) hAU hAb hAℓ
      have h4 : r / 2 - r / 4 = r / 4 := by ring
      rw [h4] at hchart
      simp only [hQ1, hQ2, hk, ↓reduceIte]
      exact hchart
    · have : A k = ∅ := Set.not_nonempty_iff_eq_empty.1 hk
      rw [this]
      simp
  have hBn : (3 * r / 4 + t) / t ≤ ((13 : ℕ) : ℝ) := by
    rw [htdef]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    linarith only [hr]
  have hcellprop : ∀ k, ∀ y ∈ A k, ∀ i, ⌊y i / t⌋ = k i := fun k y hy => hy.2
  have hs1 := hl_cell_sum (U := U) (R' := 3 * r / 4) ht hBn A c hcellprop
    (fun k hk => (hc k hk).2) hF1m
  have hs2 := hl_cell_sum (U := U) (R' := 3 * r / 4) ht hBn A c hcellprop
    (fun k hk => (hc k hk).2) hF2m
  calc ENNReal.ofReal (r / 4) * ∫⁻ x in L, F1 x
      ≤ ENNReal.ofReal (r / 4) * ∫⁻ x in ⋃ k, A k, F1 x :=
        mul_le_mul_right (lintegral_mono_set hcover) _
    _ ≤ ENNReal.ofReal (r / 4) * ∑' k, ∫⁻ x in A k, F1 x :=
        mul_le_mul_right (lintegral_iUnion_le _ _) _
    _ = ∑' k, ENNReal.ofReal (r / 4) * ∫⁻ x in A k, F1 x := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' k, (2 * ENNReal.ofReal (κ * s) * Q1 k +
        2 * ENNReal.ofReal (r / 4) * ENNReal.ofReal (r / 2) * ENNReal.ofReal (κ * s) * Q2 k) :=
        ENNReal.tsum_le_tsum hper
    _ = 2 * ENNReal.ofReal (κ * s) * ∑' k, Q1 k +
        2 * ENNReal.ofReal (r / 4) * ENNReal.ofReal (r / 2) * ENNReal.ofReal (κ * s) *
          ∑' k, Q2 k := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ 2 * ENNReal.ofReal (κ * s) * ((((2 * 13 + 1) ^ d : ℕ) : ℝ≥0∞) * ∫⁻ z in U, F1 z) +
        2 * ENNReal.ofReal (r / 4) * ENNReal.ofReal (r / 2) * ENNReal.ofReal (κ * s) *
          ((((2 * 13 + 1) ^ d : ℕ) : ℝ≥0∞) * ∫⁻ z in U, F2 z) := by
        gcongr
    _ = _ := by ring

theorem hl_lintegral_gradMajorant (U : Set (Vec d)) (w : H1Function U) :
    ∫⁻ z in U, ‖(d : ℝ) * ‖w.grad z‖‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal ((d : ℝ) ^ 2) * ∫⁻ z in U, ‖w.grad z‖ₑ ^ (2 : ℝ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  have h1 : ‖(d : ℝ) * ‖w.grad z‖‖ₑ = ENNReal.ofReal (d : ℝ) * ‖w.grad z‖ₑ := by
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg d),
      ofReal_norm]
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg
    (Nat.cast_nonneg d) (by norm_num), Real.rpow_two]

/-- **Boundary-layer inequality for `H¹` functions.** For `V` uniformly `C^{1,1}` with chart radius
`r` and slope bound `M₁`, every `w ∈ H¹(V)` and every `s > 0`,
`∫_{layer_s} w² ≤ C (s / r) ∫_V w² + C s r ∫_V |∇w|²`, with `C` depending only on `(d, M₁)`. -/
theorem exists_layerH1 [NeZero d] (M₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U : Set (Vec d)} {r M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
      ∀ (w : H1Function U) {s : ℝ}, 0 < s →
        ∫⁻ x in boundaryLayer U s, ‖w.toFun x‖ₑ ^ (2 : ℝ) ≤
          ENNReal.ofReal (C * (s / r)) * (∫⁻ x in U, ‖w.toFun x‖ₑ ^ (2 : ℝ)) +
            ENNReal.ofReal (C * (s * r)) * ∫⁻ x in U, ‖w.grad x‖ₑ ^ (2 : ℝ) := by
  set κ₀ : ℝ := (d : ℝ) + (1 + d) * max M₁ 0 with hκ₀
  have hκ₀0 : 0 ≤ κ₀ := by
    have : 0 ≤ max M₁ 0 := le_max_right _ _
    positivity
  set Nn : ℕ := (2 * 13 + 1) ^ d with hNn
  set Nr : ℝ := (Nn : ℝ) with hNr
  have hNr0 : 0 ≤ Nr := Nat.cast_nonneg _
  set C : ℝ := max 16 (max (8 * Nr * κ₀) (Nr * κ₀ * (d : ℝ) ^ 2)) with hC
  have hC16 : 16 ≤ C := le_max_left _ _
  have hC1 : 8 * Nr * κ₀ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC2 : Nr * κ₀ * (d : ℝ) ^ 2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, by linarith only [hC16], ?_⟩
  intro U r M₂ D h w s hs
  have hr : 0 < r := h.2.1
  set I1 : ℝ≥0∞ := ∫⁻ x in U, ‖w.toFun x‖ₑ ^ (2 : ℝ) with hI1
  set I2 : ℝ≥0∞ := ∫⁻ x in U, ‖w.grad x‖ₑ ^ (2 : ℝ) with hI2
  by_cases hsr : 16 * s ≤ r
  · have hsmall := hl_layer_small h w hsr
    rw [hl_lintegral_gradMajorant] at hsmall
    have hκle : (d : ℝ) + (1 + d) * M₁ ≤ κ₀ := by
      have : M₁ ≤ max M₁ 0 := le_max_left _ _
      have h1 : (1 + (d : ℝ)) * M₁ ≤ (1 + d) * max M₁ 0 :=
        mul_le_mul_of_nonneg_left this (by positivity)
      linarith only [h1]
    have hk : ENNReal.ofReal (((d : ℝ) + (1 + d) * M₁) * s) ≤ ENNReal.ofReal (κ₀ * s) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hκle hs.le)
    set X : ℝ≥0∞ := ∫⁻ x in boundaryLayer U s, ‖w.toFun x‖ₑ ^ (2 : ℝ) with hX
    have h4r : ENNReal.ofReal (4 / r) * ENNReal.ofReal (r / 4) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have : 4 / r * (r / 4) = 1 := by field_simp
      rw [this, ENNReal.ofReal_one]
    have hX1 : X ≤ ENNReal.ofReal (4 / r) * (ENNReal.ofReal (r / 4) * X) := by
      rw [← mul_assoc, h4r, one_mul]
    have hstep : X ≤ ENNReal.ofReal (4 / r) * ((Nn : ℝ≥0∞) *
        (2 * ENNReal.ofReal (κ₀ * s) * I1 + 2 * ENNReal.ofReal (r / 4) * ENNReal.ofReal (r / 2) *
          ENNReal.ofReal (κ₀ * s) * (ENNReal.ofReal ((d : ℝ) ^ 2) * I2))) := by
      refine hX1.trans ?_
      refine mul_le_mul_right (hsmall.trans ?_) _
      gcongr
    have c1 : ENNReal.ofReal (4 / r) * ((Nn : ℝ≥0∞) * (2 * ENNReal.ofReal (κ₀ * s))) =
        ENNReal.ofReal (8 * Nr * κ₀ * (s / r)) := by
      have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      have eN : (Nn : ℝ≥0∞) = ENNReal.ofReal Nr := by rw [hNr, ENNReal.ofReal_natCast]
      rw [e2, eN, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hNr0,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring
    have c2 : ENNReal.ofReal (4 / r) * ((Nn : ℝ≥0∞) * (2 * ENNReal.ofReal (r / 4) *
        ENNReal.ofReal (r / 2) * ENNReal.ofReal (κ₀ * s) * ENNReal.ofReal ((d : ℝ) ^ 2))) =
        ENNReal.ofReal (Nr * κ₀ * (d : ℝ) ^ 2 * (s * r)) := by
      have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
      have eN : (Nn : ℝ≥0∞) = ENNReal.ofReal Nr := by rw [hNr, ENNReal.ofReal_natCast]
      rw [e2, eN, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul hNr0, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hexp : ENNReal.ofReal (4 / r) * ((Nn : ℝ≥0∞) *
        (2 * ENNReal.ofReal (κ₀ * s) * I1 + 2 * ENNReal.ofReal (r / 4) * ENNReal.ofReal (r / 2) *
          ENNReal.ofReal (κ₀ * s) * (ENNReal.ofReal ((d : ℝ) ^ 2) * I2))) =
        ENNReal.ofReal (8 * Nr * κ₀ * (s / r)) * I1 +
          ENNReal.ofReal (Nr * κ₀ * (d : ℝ) ^ 2 * (s * r)) * I2 := by
      rw [← c1, ← c2]
      ring
    rw [hexp] at hstep
    have hA1 : ENNReal.ofReal (8 * Nr * κ₀ * (s / r)) * I1 ≤ ENNReal.ofReal (C * (s / r)) * I1 :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hC1 (by positivity))) _
    have hA2 : ENNReal.ofReal (Nr * κ₀ * (d : ℝ) ^ 2 * (s * r)) * I2 ≤
        ENNReal.ofReal (C * (s * r)) * I2 :=
      mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hC2 (by positivity))) _
    exact hstep.trans (add_le_add hA1 hA2)
  · have hsr' : r < 16 * s := not_le.1 hsr
    have hX : ∫⁻ x in boundaryLayer U s, ‖w.toFun x‖ₑ ^ (2 : ℝ) ≤ I1 :=
      lintegral_mono_set (fun x hx => hx.1)
    have h1 : 1 ≤ ENNReal.ofReal (C * (s / r)) := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : 1 / 16 ≤ s / r := by
        rw [div_le_div_iff₀ (by norm_num) hr]
        linarith only [hsr']
      have h3 : 16 * (1 / 16) ≤ C * (s / r) :=
        mul_le_mul hC16 h2 (by norm_num) (by linarith only [hC16])
      linarith only [h3]
    calc _ ≤ I1 := hX
      _ = 1 * I1 := (one_mul _).symm
      _ ≤ ENNReal.ofReal (C * (s / r)) * I1 := mul_le_mul_left h1 _
      _ ≤ _ := le_self_add

/-! ### The real form and the corollary for the Whitney Poincare lemma -/

theorem hl_enorm_rpow_two (x : ℝ) : ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two,
    Real.norm_eq_abs, sq_abs]

theorem hl_enorm_vec_rpow_two (v : Vec d) : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

theorem hl_integrable_sq {U : Set (Vec d)} (w : H1Function U) :
    Integrable (fun x => (w.toFun x) ^ 2) (volume.restrict U) :=
  w.memL2.integrable_sq

theorem hl_isFiniteMeasure [NeZero d] {U : Set (Vec d)} {D : ℝ}
    (hD : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D) : IsFiniteMeasure (volume.restrict U) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  exact ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (volume_le_of_uniform hD) ENNReal.ofReal_lt_top⟩

theorem hl_sub_const_toFun {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (w : H1Function U) (c : ℝ) (x : Vec d) :
    (w - H1Function.const (U := U) c).toFun x = w.toFun x - c := by
  change (w + -(H1Function.const (U := U) c)).toFun x = _
  simp [H1Function.const, sub_eq_add_neg]

theorem hl_sub_const_grad {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (w : H1Function U) (c : ℝ) (x : Vec d) :
    (w - H1Function.const (U := U) c).grad x = w.grad x := by
  change (w + -(H1Function.const (U := U) c)).grad x = _
  simp [H1Function.const]

end SuperdiffusionCLT.Section7
