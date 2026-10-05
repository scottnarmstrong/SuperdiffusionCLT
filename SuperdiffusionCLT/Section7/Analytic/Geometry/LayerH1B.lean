/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ConvolutionLp
public import Homogenization.Sobolev.W1p.GlobalMollifierLp
public import SuperdiffusionCLT.Section7.Analytic.Morrey.ZeroTrace
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerPoincare

/-!
# Boundary-layer inequality for `H¹` functions: approximate identities and local derivatives

* `hl_tendsto_conv_sub`: a family of nonnegative, continuous, compactly supported kernels of
  integral one with supports shrinking to the origin is an approximate identity in `L²`;
* `hl_kernel`: the mollifier translated by `l e`, the "inward" mollifier;
* `hl_fderiv_conv_basisVec`, `hl_norm_fderiv_conv_le`: the derivative of the convolution of the zero
  extension of an `H¹(U)` function, at a point whose kernel support lies in `U`;
* `hl_young_closedBall`: the localized Young inequality for a general kernel.
-/

@[expose] public section

open MeasureTheory Homogenization Convolution Filter Topology
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-! ### The `L²` approximate identity -/

/-- A continuous compactly supported function is approximated uniformly, hence in `L²`, by its
convolutions with kernels of integral one concentrating at the origin. -/
theorem hl_tendsto_conv_sub_continuous {K : ℕ → Vec d → ℝ} {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hK0 : ∀ n y, 0 ≤ K n y)
    (hK1 : ∀ n, ∫ y, K n y = 1) (hKs : ∀ n y, K n y ≠ 0 → ‖y‖ < δ n)
    (hKcont : ∀ n, Continuous (K n)) (hKc : ∀ n, HasCompactSupport (K n))
    {f : Vec d → ℝ} (hf_cont : Continuous f) (hf_supp : HasCompactSupport f) :
    Tendsto (fun n => eLpNorm (fun x =>
      (K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2 volume) atTop (𝓝 0) := by
  let S : Set (Vec d) := Metric.closedBall 0 1 + tsupport f
  have hS_compact : IsCompact S := (isCompact_closedBall (0 : Vec d) 1).add hf_supp.isCompact
  have hS_meas : MeasurableSet S := hS_compact.measurableSet
  have hS_ne_top : volume S ≠ ⊤ := hS_compact.measure_lt_top.ne
  have hpow_ne_top : volume S ^ (1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hS_ne_top).ne
  let cS : ℝ := (volume S ^ (1 / (2 : ℝ≥0∞).toReal)).toReal
  have hcS : 0 ≤ cS := ENNReal.toReal_nonneg
  have hpow_eq : ENNReal.ofReal cS = volume S ^ (1 / (2 : ℝ≥0∞).toReal) :=
    ENNReal.ofReal_toReal hpow_ne_top
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hη_top : η = ⊤
  · exact Eventually.of_forall (fun n => by simp only [hη_top, le_top])
  let ε : ℝ := η.toReal / (cS + 1)
  have hη_real : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hη_top
  have hε_pos : 0 < ε := by positivity
  obtain ⟨γ, hγ_pos, hγ⟩ :=
    Metric.uniformContinuous_iff.mp (hf_supp.uniformContinuous_of_continuous hf_cont) ε hε_pos
  have h_small : ∀ᶠ n in atTop, δ n < γ := (tendsto_order.1 hδ).2 _ hγ_pos
  have h_le_one : ∀ᶠ n in atTop, δ n ≤ 1 :=
    ((tendsto_order.1 hδ).2 _ zero_lt_one).mono (fun _ hn => le_of_lt hn)
  filter_upwards [h_small, h_le_one] with n hn_small hn_one
  have hker_supp : Function.support (K n) ⊆ Metric.ball 0 (δ n) := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    exact hKs n y hy
  have hdist : ∀ x, dist ((K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x) (f x) ≤ ε := by
    intro x
    refine MeasureTheory.dist_convolution_le hε_pos.le hker_supp (hK0 n) (hK1 n)
      hf_cont.aestronglyMeasurable ?_
    intro y hy
    rw [Metric.mem_ball] at hy
    exact (hγ (hy.trans hn_small)).le
  have hconv_support : Function.support (K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) ⊆ S := by
    refine (support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
    refine Set.add_subset_add ?_ (subset_tsupport _)
    intro y hy
    have := hker_supp hy
    rw [Metric.mem_ball, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (this.trans_le hn_one).le
  have hf_support : Function.support f ⊆ S := by
    intro x hx
    refine ⟨0, ?_, x, subset_tsupport f hx, by simp only [zero_add]⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact zero_le_one
  have hmeas : AEStronglyMeasurable ((K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) volume :=
    (((hKc n).continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) (hKcont n)
      hf_cont.locallyIntegrable).sub hf_cont).aestronglyMeasurable
  have hbound := eLpNorm_sub_le_of_dist_bdd (volume : Measure (Vec d)) (p := 2)
    (by norm_num) hS_meas.nullMeasurableSet hε_pos.le hmeas hdist hconv_support hf_support
  have hεcS : ε * cS ≤ η.toReal := by
    have hfrac : cS / (cS + 1) ≤ 1 := div_le_one_of_le₀ (by linarith only) (by linarith only [hcS])
    calc ε * cS = η.toReal * (cS / (cS + 1)) := by
          dsimp only [ε]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ ≤ η.toReal * 1 := mul_le_mul_of_nonneg_left hfrac hη_real.le
      _ = η.toReal := mul_one _
  calc eLpNorm (fun x => (K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2 volume
      ≤ ENNReal.ofReal ε * volume S ^ (1 / (2 : ℝ≥0∞).toReal) := hbound
    _ = ENNReal.ofReal (ε * cS) := by
        rw [← hpow_eq, ← ENNReal.ofReal_mul hε_pos.le]
    _ ≤ η := by
        rw [← ENNReal.ofReal_toReal hη_top]
        exact ENNReal.ofReal_le_ofReal hεcS

/-- Convolution with a nonnegative kernel of integral one does not increase the `L²` norm. -/
theorem hl_eLpNorm_conv_le {K f : Vec d → ℝ} (hK0 : ∀ y, 0 ≤ K y) (hKi : Integrable K volume)
    (hK1 : ∫ y, K y = 1) (hKm : Measurable K) (hf : AEMeasurable f volume) :
    eLpNorm (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) 2 volume ≤ eLpNorm f 2 volume :=
  young_convolution_nonneg_integral_one_of_aemeasurable (by norm_num) (by norm_num) hK0 hKi hK1
    hKm hf

/-- **`L²` approximate identity.** -/
theorem hl_tendsto_conv_sub {K : ℕ → Vec d → ℝ} {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hK0 : ∀ n y, 0 ≤ K n y) (hKi : ∀ n, Integrable (K n) volume)
    (hK1 : ∀ n, ∫ y, K n y = 1) (hKs : ∀ n y, K n y ≠ 0 → ‖y‖ < δ n)
    (hKcont : ∀ n, Continuous (K n)) (hKc : ∀ n, HasCompactSupport (K n))
    {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm (fun x =>
      (K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2 volume) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hη_top : η = ⊤
  · exact Eventually.of_forall (fun n => by simp only [hη_top, le_top])
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec d))) (ε := ℝ) (p := 2) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec d))) (ε := ℝ) (p := 2) hη₁_pos.ne'
  let δ' : ℝ≥0∞ := min η₁ η₂
  have hδ'_pos : 0 < δ' := lt_min hη₁_pos hη₂_pos
  obtain ⟨g, hg_supp, happrox, hg_cont, hg_mem⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hδ'_pos.ne'
  have hthird : eLpNorm (fun x => g x - f x) 2 volume ≤ η₁ := by
    have hneg : (fun x => g x - f x) = -(fun x => f x - g x) := by
      ext x
      change g x - f x = -(f x - g x)
      ring
    rw [hneg, eLpNorm_neg]
    exact happrox.trans (min_le_left _ _)
  have hmid_tendsto := hl_tendsto_conv_sub_continuous hδ hK0 hK1 hKs hKcont hKc hg_cont hg_supp
  have hmid_ev : ∀ᶠ n in atTop, eLpNorm (fun x =>
      (K n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) 2 volume ≤ η₂ :=
    ENNReal.tendsto_nhds_zero.1 hmid_tendsto η₂ hη₂_pos
  filter_upwards [hmid_ev] with n hmid
  set k := K n with hk
  have hk_cont : Continuous k := hKcont n
  have hk_compact : HasCompactSupport k := hKc n
  have hf_loc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hg_loc : LocallyIntegrable g volume := hg_mem.locallyIntegrable (by norm_num)
  have hdiff_loc : LocallyIntegrable (fun x => f x - g x) volume := hf_loc.sub hg_loc
  have hconv_g : ConvolutionExists k g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hg_loc
  have hconv_diff : ConvolutionExists k (fun x => f x - g x)
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hk_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hk_cont hdiff_loc
  have hsplit : f = (fun x => f x - g x) + g := by
    ext x
    change f x = (f x - g x) + g x
    ring
  have hconv_split : k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) +
        k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g := by
    calc k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
        = k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((fun x => f x - g x) + g) :=
          congrArg (fun v => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) hsplit
      _ = _ := hconv_diff.distrib_add hconv_g
  have hfirst : eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) 2 volume
      ≤ η₂ := by
    refine (hl_eLpNorm_conv_le (hK0 n) (hKi n) (hK1 n) hk_cont.measurable
      (hf.sub hg_mem).aemeasurable).trans ?_
    exact happrox.trans (min_le_right _ _)
  have hfirst_middle : eLpNorm
      ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) +
        fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) 2 volume < η₁ :=
    hη₂ _ _ hfirst hmid
  have hsum : eLpNorm (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) +
        fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) +
        fun x => g x - f x) 2 volume < η :=
    hη₁ _ _ hfirst_middle.le hthird
  have hdecomp : eLpNorm (fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x - f x) 2
      volume = eLpNorm (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => f x - g x) +
        fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) +
        fun x => g x - f x) 2 volume := by
    rw [hconv_split]
    congr 1
    ext x
    simp only [Pi.add_apply]
    ring
  exact hdecomp.trans_le hsum.le


/-! ### The inward mollifier -/

/-- The mollifier of radius `a`, translated by `l e`. -/
noncomputable def hl_kernel (a l : ℝ) (e : Vec d) : Vec d → ℝ := fun t =>
  scaledConvexApproxKernel unitConvexApproxKernel a (t - l • e)

theorem hl_kernel_contDiff {a : ℝ} (l : ℝ) (e : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (hl_kernel a l e) :=
  (contDiff_scaledConvexApproxKernel (isConvexApproxKernel_unitConvexApproxKernel (d := d)) a).comp
    (contDiff_id.sub contDiff_const)

theorem hl_kernel_hasCompactSupport {a : ℝ} (ha : 0 < a) (l : ℝ) (e : Vec d) :
    HasCompactSupport (hl_kernel a l e) :=
  (hasCompactSupport_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport ha).comp_isClosedEmbedding
    (Homeomorph.subRight (l • e)).isClosedEmbedding

theorem hl_kernel_nonneg {a : ℝ} (ha : 0 < a) (l : ℝ) (e : Vec d) (t : Vec d) :
    0 ≤ hl_kernel a l e t :=
  scaledConvexApproxKernel_nonneg (isConvexApproxKernel_unitConvexApproxKernel (d := d)) ha _

theorem hl_kernel_integrable {a : ℝ} (ha : 0 < a) (l : ℝ) (e : Vec d) :
    Integrable (hl_kernel a l e) volume :=
  (integrable_scaledConvexApproxKernel (isConvexApproxKernel_unitConvexApproxKernel (d := d))
    ha).comp_sub_right (l • e)

theorem hl_kernel_integral {a : ℝ} (ha : 0 < a) (l : ℝ) (e : Vec d) :
    ∫ t, hl_kernel a l e t = 1 := by
  unfold hl_kernel
  rw [integral_sub_right_eq_self (fun t => scaledConvexApproxKernel unitConvexApproxKernel a t)
    (l • e)]
  exact integral_scaledConvexApproxKernel (isConvexApproxKernel_unitConvexApproxKernel (d := d)) ha

theorem hl_kernel_norm_le {a : ℝ} (ha : 0 < a) {l : ℝ} (hl : 0 ≤ l) {e : Vec d} (he : ‖e‖ ≤ 1)
    {t : Vec d} (ht : hl_kernel a l e t ≠ 0) : ‖t‖ ≤ l + a := by
  have h1 := scaledKernel_ne_zero_norm_le (isConvexApproxKernel_unitConvexApproxKernel (d := d))
    ha ht
  calc ‖t‖ = ‖(t - l • e) + l • e‖ := by congr 1; abel
    _ ≤ ‖t - l • e‖ + ‖l • e‖ := norm_add_le _ _
    _ ≤ a + l := by
        have : ‖l • e‖ ≤ l := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl]
          exact mul_le_of_le_one_right hl he
        linarith only [h1, this]
    _ = l + a := add_comm _ _

/-- The kernel of `hl_kernel` reflected at `p` is supported in the ball of radius `a` about the
inward point `p - l e`. -/
theorem hl_kernel_reflect_subset {a : ℝ} (ha : 0 < a) (l : ℝ) (e : Vec d) (p : Vec d) :
    tsupport (fun z => hl_kernel a l e (p - z)) ⊆ Metric.closedBall (p - l • e) a := by
  apply closure_minimal
  · intro z hz
    have h1 := scaledKernel_ne_zero_norm_le (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      ha (t := p - z - l • e) hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖z - (p - l • e)‖ = ‖-(p - z - l • e)‖ := by congr 1; abel
      _ = ‖p - z - l • e‖ := norm_neg _
      _ ≤ a := h1
  · exact Metric.isClosed_closedBall

/-! ### The derivative of the convolution with the zero extension -/

theorem hl_fderiv_conv_basisVec {U : Set (Vec d)} (hUm : MeasurableSet U) {K w gi : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (hf : LocallyIntegrable (U.indicator w) volume) {i : Fin d}
    (hi : HasWeakPartialDerivOn U i w gi) (p : Vec d)
    (hp : tsupport (fun z => K (p - z)) ⊆ U) :
    fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U.indicator w) p (basisVec i) =
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U.indicator gi) p := by
  have hk1 : ContDiff ℝ 1 K := hK.of_le (by norm_num)
  rw [hasFDerivAt_convolution_apply_basisVec hk1 hKc hf, convolution_def]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => K (p - y)) :=
    hK.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun y : Vec d => K (p - y)) :=
    hKc.comp_isClosedEmbedding (Homeomorph.subLeft p).isClosedEmbedding
  have hw := hi _ hφ hφc hp
  simp only [fderiv_reflect_apply hk1, mul_neg, integral_neg] at hw
  have e1 : ∫ t, (fderiv ℝ K t) (basisVec i) * U.indicator w (p - t) ∂volume =
      ∫ s, (fderiv ℝ K (p - s)) (basisVec i) * U.indicator w s ∂volume := by
    rw [← integral_sub_left_eq_self
      (fun s => (fderiv ℝ K (p - s)) (basisVec i) * U.indicator w s) volume p]
    simp
  have e2 : ∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (K t) (U.indicator gi (p - t)) ∂volume =
      ∫ s, U.indicator gi s * K (p - s) ∂volume := by
    rw [← integral_sub_left_eq_self (fun s => U.indicator gi s * K (p - s)) volume p]
    simp [mul_comm]
  rw [e1, e2]
  have hU : ∀ (F G : Vec d → ℝ),
      ∫ s, U.indicator F s * G s ∂volume = ∫ s in U, F s * G s ∂volume := by
    intro F G
    rw [← integral_indicator hUm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    by_cases hs : s ∈ U <;> simp [Set.indicator_of_mem, hs]
  have e3 : ∫ s, (fderiv ℝ K (p - s)) (basisVec i) * U.indicator w s ∂volume =
      ∫ s in U, w s * (fderiv ℝ K (p - s)) (basisVec i) ∂volume := by
    rw [← hU]
    congr 1
    ext s
    ring
  rw [e3, hU]
  linarith only [hw]


/-- The operator norm of the derivative of `K ⋆ (zero extension of w)` is bounded by the
convolution of `K` with the zero extension of `d ‖∇w‖`, at a point whose kernel support lies in
`U`. -/
theorem hl_norm_fderiv_conv_le {U : Set (Vec d)} (hUm : MeasurableSet U) {K w : Vec d → ℝ}
    {Du : Vec d → Vec d} (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (hK0 : ∀ y, 0 ≤ K y) (hf : LocallyIntegrable (U.indicator w) volume)
    (hi : ∀ i, HasWeakPartialDerivOn U i w (fun x => Du x i))
    (hDuLoc : ∀ i, LocallyIntegrable (U.indicator fun x => Du x i) volume)
    (hG : LocallyIntegrable (U.indicator fun x => (d : ℝ) * ‖Du x‖) volume) (p : Vec d)
    (hp : tsupport (fun z => K (p - z)) ⊆ U) :
    ‖fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U.indicator w) p‖ ≤
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (U.indicator fun x => (d : ℝ) * ‖Du x‖)) p := by
  have hkcont : Continuous K := hK.continuous
  set G : Vec d → ℝ := U.indicator fun x => (d : ℝ) * ‖Du x‖ with hGdef
  have hG0 : ∀ y, 0 ≤ G y := fun y => by
    by_cases hy : y ∈ U
    · simp only [hGdef, Set.indicator_of_mem hy]; positivity
    · simp [hGdef, Set.indicator_of_notMem hy]
  have hGint : Integrable (fun t => K t * G (p - t)) volume :=
    (hKc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hkcont hG) p
  have hRHS : (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) p =
      ∫ t, K t * G (p - t) ∂volume := by
    rw [convolution_def]; rfl
  have hnn : 0 ≤ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) p := by
    rw [hRHS]
    exact integral_nonneg fun t => mul_nonneg (hK0 t) (hG0 _)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun v => ?_
  have hdecomp : fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] U.indicator w) p v =
      ∫ t, K t * (∑ i, v i * U.indicator (fun x => Du x i) (p - t)) ∂volume := by
    have hv : v = ∑ i, v i • basisVec i := by
      ext j; simp [Finset.sum_apply, basisVec_apply]
    have hli : ∀ i, Integrable (fun t => K t * U.indicator (fun x => Du x i) (p - t)) volume :=
      fun i => (hKc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hkcont
        (hDuLoc i)) p
    conv_lhs => rw [hv]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    simp only [hl_fderiv_conv_basisVec hUm hK hKc hf (hi _) p hp, convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hli i).const_mul (v i))]
    congr 1; ext t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hpt : ∀ t, ‖K t * (∑ i, v i * U.indicator (fun x => Du x i) (p - t))‖ ≤
      ‖v‖ * (K t * G (p - t)) := by
    intro t
    rw [norm_mul, Real.norm_of_nonneg (hK0 t)]
    have hsum : ‖∑ i, v i * U.indicator (fun x => Du x i) (p - t)‖ ≤ ‖v‖ * G (p - t) := by
      by_cases hU : p - t ∈ U
      · simp only [hGdef, Set.indicator_of_mem hU]
        calc ‖∑ i, v i * Du (p - t) i‖ ≤ ∑ i, ‖v i * Du (p - t) i‖ := norm_sum_le _ _
          _ ≤ ∑ _i : Fin d, ‖v‖ * ‖Du (p - t)‖ := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul]
            exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm (Du (p - t)) i)
              (norm_nonneg _) (norm_nonneg _)
          _ = ‖v‖ * ((d : ℝ) * ‖Du (p - t)‖) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      · simp [Set.indicator_of_notMem hU, hGdef]
    calc K t * ‖∑ i, v i * U.indicator (fun x => Du x i) (p - t)‖
        ≤ K t * (‖v‖ * G (p - t)) := mul_le_mul_of_nonneg_left hsum (hK0 t)
      _ = _ := by ring
  rw [hdecomp, hRHS, Real.norm_eq_abs, mul_comm, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hGint.const_mul ‖v‖) (Filter.Eventually.of_forall hpt)

/-! ### Localized Young inequality for a general kernel -/

theorem hl_young_closedBall {K G : Vec d → ℝ} (hK0 : ∀ y, 0 ≤ K y) (hKi : Integrable K volume)
    (hK1 : ∫ y, K y = 1) (hKm : Measurable K) (hKcont : Continuous K)
    (hKc : HasCompactSupport K) {δ : ℝ} (hKs : ∀ y, K y ≠ 0 → ‖y‖ ≤ δ)
    (hG : LocallyIntegrable G volume) (c : Vec d) (R : ℝ) :
    ∫⁻ x in Metric.closedBall c R,
        ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x‖ₑ ^ (2 : ℝ) ≤
      ∫⁻ x in Metric.closedBall c (R + δ), ‖G x‖ₑ ^ (2 : ℝ) := by
  set S := Metric.closedBall c (R + δ) with hS
  have hSm : MeasurableSet S := Metric.isClosed_closedBall.measurableSet
  have hG'loc : LocallyIntegrable (S.indicator G) volume := hG.indicator hSm
  have hG' : AEMeasurable (S.indicator G) volume := hG'loc.aestronglyMeasurable.aemeasurable
  have heq : ∀ x ∈ Metric.closedBall c R,
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x =
        (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G)) x := by
    intro x hx
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    by_cases hkt : K t = 0
    · simp [hkt]
    · have ht : ‖t‖ ≤ δ := hKs t hkt
      have hxc : ‖x - c‖ ≤ R := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.1 hx
      have hmem : x - t ∈ S := by
        rw [hS, Metric.mem_closedBall, dist_eq_norm]
        calc ‖x - t - c‖ = ‖(x - c) - t‖ := by congr 1; abel
          _ ≤ ‖x - c‖ + ‖t‖ := norm_sub_le _ _
          _ ≤ R + δ := add_le_add hxc ht
      simp only [Set.indicator_of_mem hmem]
  have hp1 : 1 ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hyoung := young_convolution_nonneg_integral_one_of_aemeasurable (p := ENNReal.ofReal 2) hp1
    ENNReal.ofReal_ne_top hK0 hKi hK1 hKm hG'
  have hq0 : (0 : ℝ) < 2 := by norm_num
  calc ∫⁻ x in Metric.closedBall c R,
        ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x‖ₑ ^ (2 : ℝ)
      = ∫⁻ x in Metric.closedBall c R,
        ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G)) x‖ₑ ^ (2 : ℝ) :=
        setLIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
          (fun x hx => by rw [heq x hx])
    _ ≤ ∫⁻ x, ‖(K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G)) x‖ₑ ^ (2 : ℝ) :=
        setLIntegral_le_lintegral _ _
    _ = eLpNorm (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (S.indicator G))
          (ENNReal.ofReal 2) volume ^ (2 : ℝ) :=
        layerPoincare_lintegral_enorm_rpow_eq hq0
          ((hKc.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
            hKcont hG'loc).aestronglyMeasurable)
    _ ≤ eLpNorm (S.indicator G) (ENNReal.ofReal 2) volume ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hyoung hq0.le
    _ = ∫⁻ x, ‖S.indicator G x‖ₑ ^ (2 : ℝ) :=
        (layerPoincare_lintegral_enorm_rpow_eq hq0 hG'loc.aestronglyMeasurable).symm
    _ = ∫⁻ x in S, ‖G x‖ₑ ^ (2 : ℝ) := by
        rw [← lintegral_indicator hSm]
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ S
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hq0]

end SuperdiffusionCLT.Section7
