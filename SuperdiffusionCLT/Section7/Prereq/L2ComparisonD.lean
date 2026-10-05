/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonC

/-!
# The mollified flux solves the mollified equation in the interior

Display `e.Dir.new.convolution.identity`.
If `-∇·F = f` weakly in an open set `W` (tested against `H¹₀(W)`), then for every `H¹(W)`
function `Θ` vanishing outside a compact set `K` whose `h`-thickening stays in `W`,
`∫_W (η_h ∗ F)·∇Θ = ∫_W (η_h ∗ f) Θ`:
the mollified flux solves the mollified equation where the mollifier ball stays inside `W`.
The proof tests the equation with the reflected mollification of the zero extension of `Θ`
(a smooth function compactly supported in `W`) and exchanges the order of integration.

## Main results

* `Section7.l2a_pairing`: the Fubini exchange `∫ (k ∗ F) G = ∫ F (k̃ ∗ G)`.
* `Section7.l2a_convolution_identity`.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Convolution

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Mollification is self-adjoint against the reflected kernel (Fubini). -/
theorem l2a_pairing {k : Vec d → ℝ} (hk : Continuous k) {B : ℝ} (hkb : ∀ z, |k z| ≤ B)
    {F G : Vec d → ℝ} (hF : Integrable F volume) (hG : Integrable G volume) :
    ∫ x, (∫ y, k (x - y) * F y) * G x = ∫ y, F y * ∫ x, k (x - y) * G x := by
  have hint : Integrable (Function.uncurry fun x y : Vec d => k (x - y) * F y * G x)
      (volume.prod volume) := by
    refine Integrable.mono' ((hG.mul_prod hF).norm.const_mul B) ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : Vec d × Vec d => k (p.1 - p.2)) (volume.prod volume) :=
        (hk.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
      exact ((h1.mul (hF.aestronglyMeasurable.comp_snd)).mul hG.aestronglyMeasurable.comp_fst)
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
      calc |k (p.1 - p.2)| * |F p.2| * |G p.1| ≤ B * |F p.2| * |G p.1| := by
            gcongr; exact hkb _
        _ = B * (|G p.1| * |F p.2|) := by ring
  have e1 : ∀ x, (∫ y, k (x - y) * F y) * G x = ∫ y, k (x - y) * F y * G x := fun x =>
    (integral_mul_const _ _).symm
  have e2 : ∀ y, F y * ∫ x, k (x - y) * G x = ∫ x, k (x - y) * F y * G x := fun y => by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  simp only [e1, e2]
  exact integral_integral_swap hint

/-- The convolution with the reflected kernel, written as an integral. -/
theorem l2a_convr_apply (k g : Vec d → ℝ) (y : Vec d) :
    ((fun z => k (-z)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) y =
      ∫ x, k (x - y) * g x := by
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have := integral_sub_left_eq_self (fun t => k (-t) * g (y - t)) volume y
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [neg_sub, sub_sub_cancel]

/-- A continuous compactly supported multiplier of an integrable function is integrable. -/
theorem l2a_integrable_mul {c g : Vec d → ℝ} (hc : Continuous c) (hcc : HasCompactSupport c)
    (hg : Integrable g volume) : Integrable (fun x => c x * g x) volume := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcc
  exact hg.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hC)


/-- The zero extension of a function that is zero off a compact `K ⊆ W` has an a.e. zero
gradient off `K`. -/
theorem l2a_grad_ae_zero_off {W K : Set (Vec d)} (hW : IsOpen W) (hK : IsCompact K)
    (Θ : H1Function W) (hΘ : ∀ x ∈ W, x ∉ K → Θ.toFun x = 0) (i : Fin d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∈ W → x ∉ K → Θ.grad x i = 0 := by
  have hV : IsOpen (W ∩ Kᶜ) := hW.inter hK.isClosed.isOpen_compl
  have hgrad : ∀ᵐ y ∂(volume.restrict (W ∩ Kᶜ)), Θ.grad y i = 0 := by
    refine grad_ae_zero_of_zero hV i (fun y hy => hΘ y hy.1 hy.2)
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Θ.gradMemL2 i).locallyIntegrable (by norm_num)) |>.mono_set inter_subset_left)
      ((Θ.hasWeakPartialDerivOn i).restrict hV inter_subset_left)
  have := (ae_restrict_iff' hV.measurableSet).1 hgrad
  filter_upwards [this] with x hx hxW hxK
  exact hx ⟨hxW, hxK⟩

/-- A kernel integral against a function supported in `K` vanishes off the `h`-thickening. -/
theorem l2a_kernel_integral_eq_zero {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {K : Set (Vec d)} {g : Vec d → ℝ}
    (hg : ∀ x, x ∉ K → g x = 0) {y : Vec d} (hy : y ∉ Metric.cthickening h K) :
    ∫ x, a16_kernel d h η (x - y) * g x = 0 := by
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ K
  · have hd : h < ‖x - y‖ := by
      by_contra hle
      exact hy (Metric.mem_cthickening_of_dist_le y x h K hx (by rw [dist_comm, dist_eq_norm]; exact not_lt.1 hle))
    simp [l2a_kernel_eq_zero_of_norm hh hη0 hd]
  · simp [hg x hx]

/-- **The reflected mollification of a compactly supported test function** is an `H¹₀(W)`
function with the explicit value and gradient. -/
theorem l2a_reflected_test {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {K : Set (Vec d)} (hK : IsCompact K)
    (hKW : Metric.cthickening h K ⊆ W) (Θ : H1Function W)
    (hΘ : ∀ x ∈ W, x ∉ K → Θ.toFun x = 0) :
    ∃ ψ : H10Function W,
      (∀ y, ψ.toH1Function.toFun y = ∫ x, a16_kernel d h η (x - y) * (W.indicator Θ.toFun) x) ∧
      (∀ y i, ψ.toH1Function.grad y i =
        ∫ x, a16_kernel d h η (x - y) * (K.indicator (fun x => Θ.grad x i)) x) ∧
      ∀ i, Continuous fun y => ψ.toH1Function.grad y i := by
  have hK' : IsCompact (Metric.cthickening h K) := hK.cthickening
  have hKK' : K ⊆ Metric.cthickening h K := Metric.self_subset_cthickening K
  have hKW0 : K ⊆ W := hKK'.trans hKW
  set k := a16_kernel d h η with hkdef
  set T : Vec d → ℝ := W.indicator Θ.toFun with hT
  set G : Fin d → Vec d → ℝ := fun i => K.indicator (fun x => Θ.grad x i) with hG
  have hT0 : ∀ x, x ∉ K → T x = 0 := fun x hx => by
    by_cases hxW : x ∈ W
    · simp [hT, Set.indicator_of_mem hxW, hΘ x hxW hx]
    · simp [hT, Set.indicator_of_notMem hxW]
  have hG0 : ∀ i x, x ∉ K → G i x = 0 := fun i x hx => by simp [hG, Set.indicator_of_notMem hx]
  have hTloc : LocallyIntegrable T volume :=
    ((memLp_indicator_iff_restrict hW.measurableSet).2 Θ.memL2).locallyIntegrable (by norm_num)
  have hGae : ∀ i, (W.indicator fun x => Θ.grad x i) =ᵐ[volume] G i := fun i => by
    filter_upwards [l2a_grad_ae_zero_off hW hK Θ hΘ i] with x hx
    by_cases hxK : x ∈ K
    · simp [hG, Set.indicator_of_mem hxK, Set.indicator_of_mem (hKW0 hxK)]
    · by_cases hxW : x ∈ W
      · simp [hG, Set.indicator_of_notMem hxK, Set.indicator_of_mem hxW, hx hxW hxK]
      · simp [hG, Set.indicator_of_notMem hxK, Set.indicator_of_notMem hxW]
  have hweakG : ∀ i, HasWeakPartialDerivOn Set.univ i T (G i) := fun i =>
    hasWeakPartialDerivOn_congr_ae
      (hasWeakPartialDerivOn_univ_zeroExtend hW Θ hKW0 hK hΘ i) (by
        rw [Measure.restrict_univ]; exact hGae i)
  have hGloc : ∀ i, LocallyIntegrable (G i) volume := fun i => by
    have h1 : LocallyIntegrable (W.indicator fun x => Θ.grad x i) volume :=
      ((memLp_indicator_iff_restrict hW.measurableSet).2 (Θ.gradMemL2 i)).locallyIntegrable
        (by norm_num)
    exact h1.congr (hGae i)
  have hkr_c := l2a_kernel_neg_compact hh hη0
  have hkr_s := l2a_kernel_neg_contDiff (h := h) hη
  set Φ := (fun z => k (-z)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] T with hΦ
  set P : Fin d → Vec d → ℝ := fun i => (fun z => k (-z)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G i
    with hP
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞) Φ := hkr_c.contDiff_convolution_left _ hkr_s hTloc
  have hPcont : ∀ i, Continuous (P i) := fun i =>
    hkr_c.continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hkr_s.continuous (hGloc i)
  have hderiv : ∀ i x, fderiv ℝ Φ x (basisVec i) = P i x := fun i x =>
    fderiv_convolution_eq_of_hasWeakPartialDerivOn hkr_c hkr_s hTloc (hweakG i) x
  have hΦval : ∀ y, Φ y = ∫ x, k (x - y) * T x := fun y => l2a_convr_apply k T y
  have hPval : ∀ i y, P i y = ∫ x, k (x - y) * G i x := fun i y => l2a_convr_apply k (G i) y
  let H1 : H1Function W :=
    { toFun := Φ
      grad := fun y i => P i y
      memL2 := l2a_memL2_of_continuous hW.measurableSet hWb hΦcd.continuous
      gradMemL2 := fun i => l2a_memL2_of_continuous hW.measurableSet hWb (hPcont i)
      hasWeakGradient := fun i => by
        have := HasWeakPartialDerivOn.of_contDiff (U := W) (i := i)
          (hΦcd.of_le (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by exact_mod_cast le_top))
        have e : (fun x => fderiv ℝ Φ x (basisVec i)) = fun x => P i x := funext (hderiv i)
        rwa [e] at this }
  have hf0 : ∀ x ∈ W, x ∉ Metric.cthickening h K → H1.toFun x = 0 := fun x _ hx => by
    show Φ x = 0
    rw [hΦval]
    exact l2a_kernel_integral_eq_zero hh hη0 hT0 hx
  refine ⟨toH10OfCompact hW H1 hKW hK' hf0, fun y => ?_, fun y i => ?_, fun i => ?_⟩
  · rw [toH10OfCompact_toH1Function]
    exact hΦval y
  · rw [toH10OfCompact_toH1Function]
    exact hPval i y
  · rw [toH10OfCompact_toH1Function]
    exact hPcont i


/-- A mollification of a compactly supported integrable function is continuous with compact
support. -/
theorem l2a_moll_cont_compact {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {u : Vec d → ℝ}
    (hu : Integrable u volume) (huc : HasCompactSupport u) :
    Continuous (l2a_moll d h η u) ∧ HasCompactSupport (l2a_moll d h η u) := by
  rw [l2a_moll_eq_conv]
  exact ⟨(l2a_kernel_compact hh hη0).continuous_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (l2a_kernel_contDiff hη).continuous hu.locallyIntegrable,
    HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (l2a_kernel_compact hh hη0) huc⟩

/-- Locality of the mollification for a function cut off to the `h`-thickening of `K`. -/
theorem l2a_moll_indicator_eq {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {K : Set (Vec d)} {u : Vec d → ℝ} {x : Vec d}
    (hx : x ∈ K) : l2a_moll d h η ((Metric.cthickening h K).indicator u) x = l2a_moll d h η u x :=
  l2a_moll_congr hh hη0 fun y hy => by
    rw [Set.indicator_of_mem (Metric.mem_cthickening_of_dist_le y x h K hx hy)]

/-- **The mollified flux solves the mollified equation in the interior**
(`e.Dir.new.convolution.identity`).  If `-∇·F = f` weakly in `W` and `Θ ∈ H¹(W)` vanishes off a
compact `K` with `cthickening h K ⊆ W`, then `∫_W (η_h ∗ F)·∇Θ = ∫_W (η_h ∗ f) Θ`.  Only the
values of `F` and `f` on `W` enter. -/
theorem l2a_convolution_identity {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {K : Set (Vec d)}
    (hK : IsCompact K) (hKW : Metric.cthickening h K ⊆ W) {F : Vec d → Vec d} {f : Vec d → ℝ}
    (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) W volume)
    (hf : LocallyIntegrableOn f W volume)
    (hweak : ∀ φ : H10Function W,
      ∫ x in W, vecDot (F x) (φ.toH1Function.grad x) = ∫ x in W, f x * φ.toH1Function.toFun x)
    (Θ : H1Function W) (hΘ : ∀ x ∈ W, x ∉ K → Θ.toFun x = 0) :
    ∫ x in W, vecDot (a16_mollify d h η F x) (Θ.grad x) =
      ∫ x in W, l2a_moll d h η f x * Θ.toFun x := by
  obtain ⟨ψ, hψ, hψg, hψc⟩ := l2a_reflected_test hW hWb hh hη hη0 hK hKW Θ hΘ
  have hK' : IsCompact (Metric.cthickening h K) := hK.cthickening
  have hKK' : K ⊆ Metric.cthickening h K := Metric.self_subset_cthickening K
  have hKW0 : K ⊆ W := hKK'.trans hKW
  set K' := Metric.cthickening h K with hK'def
  set k := a16_kernel d h η with hkdef
  set T : Vec d → ℝ := W.indicator Θ.toFun with hT
  set G : Fin d → Vec d → ℝ := fun i => K.indicator (fun x => Θ.grad x i) with hG
  have hT0 : ∀ x, x ∉ K → T x = 0 := fun x hx => by
    by_cases hxW : x ∈ W
    · simp [hT, Set.indicator_of_mem hxW, hΘ x hxW hx]
    · simp [hT, Set.indicator_of_notMem hxW]
  have hG0 : ∀ i x, x ∉ K → G i x = 0 := fun i x hx => by simp [hG, Set.indicator_of_notMem hx]
  have hTloc : LocallyIntegrable T volume :=
    ((memLp_indicator_iff_restrict hW.measurableSet).2 Θ.memL2).locallyIntegrable (by norm_num)
  have hTint : Integrable T volume :=
    (integrableOn_iff_integrable_of_support_subset (s := K) fun x hx => by
      by_contra hxK; exact hx (hT0 x hxK)).1 (hTloc.integrableOn_isCompact hK)
  have hGae : ∀ i, (W.indicator fun x => Θ.grad x i) =ᵐ[volume] G i := fun i => by
    filter_upwards [l2a_grad_ae_zero_off hW hK Θ hΘ i] with x hx
    by_cases hxK : x ∈ K
    · simp [hG, Set.indicator_of_mem hxK, Set.indicator_of_mem (hKW0 hxK)]
    · by_cases hxW : x ∈ W
      · simp [hG, Set.indicator_of_notMem hxK, Set.indicator_of_mem hxW, hx hxW hxK]
      · simp [hG, Set.indicator_of_notMem hxK, Set.indicator_of_notMem hxW]
  have hGint : ∀ i, Integrable (G i) volume := fun i => by
    have h1 : LocallyIntegrable (W.indicator fun x => Θ.grad x i) volume :=
      ((memLp_indicator_iff_restrict hW.measurableSet).2 (Θ.gradMemL2 i)).locallyIntegrable
        (by norm_num)
    exact (integrableOn_iff_integrable_of_support_subset (s := K) fun x hx => by
      by_contra hxK; exact hx (hG0 i x hxK)).1 ((h1.congr (hGae i)).integrableOn_isCompact hK)
  -- the cut-off data
  set F' : Fin d → Vec d → ℝ := fun i => K'.indicator (fun x => F x i) with hF'
  set f' : Vec d → ℝ := K'.indicator f with hf'
  have hF'int : ∀ i, Integrable (F' i) volume := fun i =>
    (integrable_indicator_iff hK'.measurableSet).2 ((hF i).integrableOn_compact_subset hKW hK')
  have hf'int : Integrable f' volume :=
    (integrable_indicator_iff hK'.measurableSet).2 (hf.integrableOn_compact_subset hKW hK')
  have hF'c : ∀ i, HasCompactSupport (F' i) := fun i =>
    HasCompactSupport.of_support_subset_isCompact hK' fun x hx => by
      by_contra hxK; exact hx (by simp [hF', Set.indicator_of_notMem hxK])
  obtain ⟨Bk, hBk⟩ := (l2a_kernel_contDiff hη).continuous.bounded_above_of_compact_support
    (l2a_kernel_compact hh hη0)
  have hkb : ∀ z, |k z| ≤ Bk := fun z => by simpa [Real.norm_eq_abs] using hBk z
  have hkcont : Continuous k := (l2a_kernel_contDiff hη).continuous
  set Pf : Fin d → Vec d → ℝ := fun i y => ∫ x, k (x - y) * G i x with hPf
  have hPfoff : ∀ i y, y ∉ K' → Pf i y = 0 := fun i y hy =>
    l2a_kernel_integral_eq_zero hh hη0 (hG0 i) hy
  have hPfcont : ∀ i, Continuous (Pf i) := fun i => by
    have : Pf i = fun y => ψ.toH1Function.grad y i := funext fun y => (hψg y i).symm
    rw [this]; exact hψc i
  have hPfc : ∀ i, HasCompactSupport (Pf i) := fun i =>
    HasCompactSupport.of_support_subset_isCompact hK' fun y hy => by
      by_contra hyK; exact hy (hPfoff i y hyK)
  -- left-hand side
  have hL1 : ∫ x in W, vecDot (F x) (ψ.toH1Function.grad x) = ∫ x, ∑ i, F' i x * Pf i x := by
    have hz : ∀ x, x ∉ W → ∑ i, F' i x * Pf i x = 0 := fun x hx => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hPfoff i x (fun hxK => hx (hKW hxK)), mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hW.measurableSet fun x _ => ?_
    simp only [vecDot]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hψg x i]
    change F x i * Pf i x = F' i x * Pf i x
    by_cases hxK : x ∈ K'
    · simp [hF', Set.indicator_of_mem hxK]
    · rw [hPfoff i x hxK]; simp
  have hL2 : ∫ x, ∑ i, F' i x * Pf i x = ∑ i, ∫ x, F' i x * Pf i x :=
    integral_finsetSum _ fun i _ => by
      have := l2a_integrable_mul (hPfcont i) (hPfc i) (hF'int i)
      simpa [mul_comm] using this
  have hL3 : ∀ i, ∫ x, F' i x * Pf i x = ∫ x, l2a_moll d h η (F' i) x * G i x := fun i =>
    (l2a_pairing hkcont hkb (hF'int i) (hGint i)).symm
  have hmollF : ∀ i x, l2a_moll d h η (F' i) x * G i x =
      a16_mollify d h η F x i * G i x := fun i x => by
    by_cases hxK : x ∈ K
    · rw [l2a_mollify_apply]
      congr 1
      exact l2a_moll_indicator_eq hh hη0 hxK
    · simp [hG0 i x hxK]
  -- the target left-hand side
  have hT1 : ∫ x in W, vecDot (a16_mollify d h η F x) (Θ.grad x) =
      ∫ x, ∑ i, a16_mollify d h η F x i * G i x := by
    have hz : ∀ x, x ∉ W → ∑ i, a16_mollify d h η F x i * G i x = 0 := fun x hx => by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hG0 i x (fun hxK => hx (hKW0 hxK)), mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ i, x ∈ W → Θ.grad x i = G i x := by
      rw [ae_all_iff]
      intro i
      filter_upwards [l2a_grad_ae_zero_off hW hK Θ hΘ i] with x hx hxW
      by_cases hxK : x ∈ K
      · simp [hG, Set.indicator_of_mem hxK]
      · rw [hx hxW hxK, hG0 i x hxK]
    refine setIntegral_congr_ae hW.measurableSet ?_
    filter_upwards [hae] with x hx hxW
    simp only [vecDot]
    exact Finset.sum_congr rfl fun i _ => by rw [hx i hxW]
  have hT2 : ∫ x, ∑ i, a16_mollify d h η F x i * G i x =
      ∑ i, ∫ x, l2a_moll d h η (F' i) x * G i x := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact (hmollF i x).symm
    · intro i _
      obtain ⟨hc, hcc⟩ := l2a_moll_cont_compact hh hη hη0 (hF'int i) (hF'c i)
      exact (l2a_integrable_mul hc hcc (hGint i)).congr
        (Filter.Eventually.of_forall fun x => hmollF i x)
  have hLHS : ∫ x in W, vecDot (a16_mollify d h η F x) (Θ.grad x) =
      ∫ x in W, vecDot (F x) (ψ.toH1Function.grad x) := by
    rw [hT1, hT2, hL1, hL2]
    exact Finset.sum_congr rfl fun i _ => (hL3 i).symm
  -- right-hand side
  have hR1 : ∫ x in W, f x * ψ.toH1Function.toFun x = ∫ x, f' x * ∫ y, k (y - x) * T y := by
    have hz : ∀ x, x ∉ W → f' x * ∫ y, k (y - x) * T y = 0 := fun x hx => by
      rw [l2a_kernel_integral_eq_zero hh hη0 hT0 (fun hxK => hx (hKW hxK)), mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hW.measurableSet fun x _ => ?_
    rw [hψ x]
    by_cases hxK : x ∈ K'
    · simp [hf', Set.indicator_of_mem hxK]
    · rw [l2a_kernel_integral_eq_zero hh hη0 hT0 hxK]; simp
  have hR2 : ∫ x, f' x * ∫ y, k (y - x) * T y = ∫ x, l2a_moll d h η f' x * T x :=
    (l2a_pairing hkcont hkb hf'int hTint).symm
  have hR3 : ∫ x, l2a_moll d h η f' x * T x = ∫ x in W, l2a_moll d h η f x * Θ.toFun x := by
    rw [← integral_indicator hW.measurableSet]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hxK : x ∈ K
    · have e : l2a_moll d h η f' x = l2a_moll d h η f x := l2a_moll_indicator_eq hh hη0 hxK
      show l2a_moll d h η f' x * T x = _
      rw [e]
      simp [hT, Set.indicator_of_mem (hKW0 hxK)]
    · show l2a_moll d h η f' x * T x = _
      by_cases hxW : x ∈ W
      · rw [hT0 x hxK, Set.indicator_of_mem hxW, hΘ x hxW hxK]; simp
      · rw [hT0 x hxK, Set.indicator_of_notMem hxW]; simp
  rw [hLHS, hweak ψ, hR1, hR2, hR3]

/-- Cutting a field off to the thickening of a compact set preserves integrability. -/
theorem l2a_cut_integrable {W K : Set (Vec d)} {h : ℝ} (hK : IsCompact K)
    (hKW : Metric.cthickening h K ⊆ W) {u : Vec d → ℝ} (hu : LocallyIntegrableOn u W volume) :
    Integrable ((Metric.cthickening h K).indicator u) volume ∧
      HasCompactSupport ((Metric.cthickening h K).indicator u) :=
  ⟨(integrable_indicator_iff hK.cthickening.measurableSet).2
      (hu.integrableOn_compact_subset hKW hK.cthickening),
    HasCompactSupport.of_support_subset_isCompact hK.cthickening fun x hx => by
      by_contra hxK; exact hx (Set.indicator_of_notMem hxK _)⟩

/-- **Splitting of the mollified flux.**  At points of `K`, `η ∗ F = s η ∗ ∇ũ + η ∗ (F - s ∇ũ)`. -/
theorem l2a_flux_split {W : Set (Vec d)} {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {K : Set (Vec d)}
    (hK : IsCompact K) (hKW : Metric.cthickening h K ⊆ W) {F : Vec d → Vec d}
    (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) W volume) (u : H1Function (Set.univ : Set (Vec d)))
    (s : ℝ) {x : Vec d} (hx : x ∈ K) (i : Fin d) :
    a16_mollify d h η F x i = s * a16_mollify d h η u.grad x i +
      a16_mollify d h η (fun y => F y - s • u.grad y) x i := by
  obtain ⟨hFi, _⟩ := l2a_cut_integrable hK hKW (hF i)
  have hg : LocallyIntegrable (fun y => u.grad y i) volume :=
    l2a_locInt_of_memL2_univ (u.gradMemL2 i)
  have hg' : LocallyIntegrable (fun y => -s * u.grad y i) volume := hg.smul (-s)
  have e1 : l2a_moll d h η (fun y => F y i) x =
      l2a_moll d h η ((Metric.cthickening h K).indicator fun y => F y i) x :=
    (l2a_moll_indicator_eq hh hη0 hx).symm
  have e2 : l2a_moll d h η (fun y => (F y - s • u.grad y) i) x =
      l2a_moll d h η (fun y => (Metric.cthickening h K).indicator (fun y => F y i) y +
        (-s) * u.grad y i) x := by
    refine l2a_moll_congr hh hη0 fun y hy => ?_
    rw [Set.indicator_of_mem (Metric.mem_cthickening_of_dist_le y x h K hx hy)]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [l2a_mollify_apply, l2a_mollify_apply, l2a_mollify_apply]
  rw [e1]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 ⊢
  rw [e2, l2a_moll_add hh hη hη0 hFi.locallyIntegrable hg',
    l2a_moll_const_mul (-s)]
  ring


theorem l2a_integrableOn_sum {W : Set (Vec d)} {f : Fin d → Vec d → ℝ}
    (hf : ∀ i, IntegrableOn (f i) W) : IntegrableOn (fun x => ∑ i, f i x) W :=
  integrable_finsetSum _ fun i _ => hf i

/-- **The identity for the comparison function** (tested form of
`e.Dir.new.convolution.identity`).  Let `-∇·F = f` weakly in `W`, `ũ ∈ H¹(ℝᵈ)`, `g ∈ H¹(W)`,
`ζ` a Lipschitz cutoff vanishing off a compact `K` with `cthickening h K ⊆ W`, and
`w = ζ (η_h ∗ ũ) + (1 - ζ) g`.  For every `φ ∈ H¹₀(W)` and every constant `s`,
`s ∫ ∇w·∇φ` equals the sum of the five error pairings below
(`(a−k)∇u` is the flux `F`, `F - s ∇ũ` the flux defect). -/
theorem l2a_comparison_identity {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {K : Set (Vec d)} (hK : IsCompact K)
    (hKW : Metric.cthickening h K ⊆ W) {Kz : ℝ≥0} {ζ : Vec d → ℝ} (hζ : LipschitzWith Kz ζ)
    (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) (hζK : ∀ x, x ∉ K → ζ x = 0)
    (u : H1Function (Set.univ : Set (Vec d))) (g : H1Function W) {F : Vec d → Vec d}
    {f : Vec d → ℝ} (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) W volume)
    (hf : LocallyIntegrableOn f W volume)
    (hweak : ∀ φ : H10Function W,
      ∫ x in W, vecDot (F x) (φ.toH1Function.grad x) = ∫ x in W, f x * φ.toH1Function.toFun x)
    (s : ℝ) (φ : H10Function W) :
    s * ∫ x in W, vecDot ((l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1).grad x)
        (φ.toH1Function.grad x) =
      (∫ x in W, (ζ x * l2a_moll d h η f x) * φ.toH1Function.toFun x)
        - (∫ x in W, φ.toH1Function.toFun x *
            vecDot (lipGradient ζ x) (a16_mollify d h η F x))
        - (∫ x in W, ζ x * vecDot (a16_mollify d h η (fun y => F y - s • u.grad y) x)
            (φ.toH1Function.grad x))
        + s * (∫ x in W, (1 - ζ x) * vecDot (g.grad x) (φ.toH1Function.grad x))
        + s * (∫ x in W, (l2a_moll d h η u.toFun x - g.toFun x) *
            vecDot (lipGradient ζ x) (φ.toH1Function.grad x)) := by
  have hK' : IsCompact (Metric.cthickening h K) := hK.cthickening
  have hKW0 : K ⊆ W := (Metric.self_subset_cthickening K).trans hKW
  have hKc : IsClosed K := hK.isClosed
  have hzg : ∀ x, x ∉ K → lipGradient ζ x = 0 := fun x hx =>
    l2a_lipGradient_eq_zero_off hKc hζK hx
  have hζc : HasCompactSupport ζ := HasCompactSupport.of_support_subset_isCompact hK fun x hx => by
    by_contra hxK; exact hx (hζK x hxK)
  have hζs : tsupport ζ ⊆ W := (closure_minimal (fun x hx => by
    by_contra hxK; exact hx (hζK x hxK)) hKc).trans hKW0
  have hM1 : ∀ x, |ζ x| ≤ 1 := fun x => by rw [abs_of_nonneg (hζ0 x)]; exact hζ1 x
  have hζcont : Continuous ζ := hζ.continuous
  -- shorthand
  set φf : Vec d → ℝ := φ.toH1Function.toFun with hφf
  set φg : Vec d → Vec d := φ.toH1Function.grad with hφg
  set M : Vec d → Vec d := fun x => a16_mollify d h η F x with hMdef
  set MD : Vec d → Vec d := fun x => a16_mollify d h η (fun y => F y - s • u.grad y) x with hMD
  set Mu : Vec d → Vec d := fun x => a16_mollify d h η u.grad x with hMu
  set mu : Vec d → ℝ := l2a_moll d h η u.toFun with hmu
  -- the mollified fields are continuous with compact support after cutting
  have hFp : ∀ i, Integrable ((Metric.cthickening h K).indicator fun x => F x i) volume ∧
      HasCompactSupport ((Metric.cthickening h K).indicator fun x => F x i) := fun i =>
    l2a_cut_integrable hK hKW (hF i)
  have hFpm : ∀ i, Continuous (l2a_moll d h η ((Metric.cthickening h K).indicator fun x => F x i))
      ∧ HasCompactSupport (l2a_moll d h η ((Metric.cthickening h K).indicator fun x => F x i)) :=
    fun i => l2a_moll_cont_compact hh hη hη0 (hFp i).1 (hFp i).2
  have hMeq : ∀ x, x ∈ K → ∀ i, M x i =
      l2a_moll d h η ((Metric.cthickening h K).indicator fun x => F x i) x := fun x hx i =>
    (l2a_moll_indicator_eq hh hη0 hx).symm
  have hMbd : ∀ i, ∃ B, ∀ x, ‖l2a_moll d h η ((Metric.cthickening h K).indicator fun x => F x i) x‖
      ≤ B := fun i => (hFpm i).1.bounded_above_of_compact_support (hFpm i).2
  have hMucont : ∀ i, Continuous (l2a_moll d h η (fun y => u.grad y i)) := fun i =>
    (l2a_moll_contDiff hh hη hη0 (l2a_locInt_of_memL2_univ (u.gradMemL2 i))).continuous
  have hmucont : Continuous mu :=
    (l2a_moll_contDiff hh hη hη0 (l2a_locInt_of_memL2_univ u.memL2)).continuous
  have hgradL2 : ∀ i, IntegrableOn (fun x => φg x i) W := fun i =>
    l2a_integrableOn_of_memL2 hWb (φ.toH1Function.gradMemL2 i)
  have hφL2 : IntegrableOn φf W := l2a_integrableOn_of_memL2 hWb φ.toH1Function.memL2
  -- integrability of the pairings
  have hJ1i : ∀ i, IntegrableOn (fun x => ζ x * (M x i * φg x i)) W := fun i => by
    obtain ⟨B, hB⟩ := hMbd i
    have := l2a_integrableOn_bdd (W := W)
      (c := fun x => ζ x * l2a_moll d h η ((Metric.cthickening h K).indicator fun x => F x i) x)
      (hζcont.mul (hFpm i).1).aestronglyMeasurable (C := B) (fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        calc |ζ x| * ‖_‖ ≤ 1 * B := mul_le_mul (hM1 x) (hB x) (norm_nonneg _) zero_le_one
          _ = B := one_mul B) (hgradL2 i)
    refine this.congr_fun (fun x _ => ?_) hW.measurableSet
    by_cases hxK : x ∈ K
    · simp only [hMeq x hxK i]; ring
    · simp [hζK x hxK]
  have hJ1 : IntegrableOn (fun x => ζ x * vecDot (M x) (φg x)) W :=
    (l2a_integrableOn_sum hJ1i).congr_fun (fun x _ => by simp [vecDot, Finset.mul_sum]) hW.measurableSet
  have hJ2i : ∀ i, IntegrableOn (fun x => (M x i * lipGradient ζ x i) * φf x) W := fun i => by
    obtain ⟨B, hB⟩ := hMbd i
    have := l2a_integrableOn_bdd (W := W)
      (c := fun x => l2a_moll d h η ((Metric.cthickening h K).indicator fun x => F x i) x *
        lipGradient ζ x i)
      ((hFpm i).1.aestronglyMeasurable.mul (aestronglyMeasurable_partialDeriv ζ i)) (C := B * Kz)
      (fun x => by
        rw [norm_mul, Real.norm_eq_abs (lipGradient ζ x i)]
        exact mul_le_mul (hB x) (l2a_lipGradient_abs_le hζ x i) (abs_nonneg _)
          ((norm_nonneg _).trans (hB x))) hφL2
    refine this.congr_fun (fun x _ => ?_) hW.measurableSet
    by_cases hxK : x ∈ K
    · simp only [hMeq x hxK i]
    · simp [hzg x hxK]
  have hJ2 : IntegrableOn (fun x => φf x * vecDot (M x) (lipGradient ζ x)) W :=
    (l2a_integrableOn_sum hJ2i).congr_fun (fun x _ => by
      simp only [vecDot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring) hW.measurableSet
  have hJ6i : ∀ i, IntegrableOn (fun x => ζ x * (Mu x i * φg x i)) W := fun i => by
    have hc : Continuous fun x => ζ x * l2a_moll d h η (fun y => u.grad y i) x :=
      hζcont.mul (hMucont i)
    have hcc : HasCompactSupport fun x => ζ x * l2a_moll d h η (fun y => u.grad y i) x :=
      HasCompactSupport.of_support_subset_isCompact hK fun x hx => by
        by_contra hxK; exact hx (by simp [hζK x hxK])
    obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hcc
    have := l2a_integrableOn_bdd (W := W) hc.aestronglyMeasurable hB (hgradL2 i)
    refine this.congr_fun (fun x _ => ?_) hW.measurableSet
    simp only [hMu, l2a_mollify_apply]; ring
  have hJ3i : ∀ i, IntegrableOn (fun x => ζ x * (MD x i * φg x i)) W := fun i => by
    refine ((hJ1i i).sub ((hJ6i i).const_mul s)).congr_fun (fun x _ => ?_) hW.measurableSet
    by_cases hxK : x ∈ K
    · have e : M x i = s * Mu x i + MD x i := l2a_flux_split hh hη hη0 hK hKW hF u s hxK i
      show ζ x * (M x i * φg x i) - s * (ζ x * (Mu x i * φg x i)) = ζ x * (MD x i * φg x i)
      rw [e]; ring
    · simp [hζK x hxK]
  have hJ3 : IntegrableOn (fun x => ζ x * vecDot (MD x) (φg x)) W :=
    (l2a_integrableOn_sum hJ3i).congr_fun (fun x _ => by simp [vecDot, Finset.mul_sum]) hW.measurableSet
  have hJ4i : ∀ i, IntegrableOn (fun x => (1 - ζ x) * (g.grad x i * φg x i)) W := fun i =>
    l2a_integrableOn_bdd (W := W) (continuous_const.sub hζcont).aestronglyMeasurable (C := 1)
      (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hζ1 x])]
        linarith only [hζ0 x])
      (l2a_integrableOn_mul_memL2 (g.gradMemL2 i) (φ.toH1Function.gradMemL2 i))
  have hJ4 : IntegrableOn (fun x => (1 - ζ x) * vecDot (g.grad x) (φg x)) W :=
    (l2a_integrableOn_sum hJ4i).congr_fun (fun x _ => by simp [vecDot, Finset.mul_sum]) hW.measurableSet
  have hdiffL2 : MemL2On W (fun x => mu x - g.toFun x) :=
    (l2a_memL2_of_continuous hW.measurableSet hWb hmucont).sub g.memL2
  have hJ5i : ∀ i, IntegrableOn (fun x => lipGradient ζ x i * ((mu x - g.toFun x) * φg x i)) W :=
    fun i => l2a_integrableOn_bdd (W := W) (aestronglyMeasurable_partialDeriv ζ i) (C := Kz)
      (fun x => by rw [Real.norm_eq_abs]; exact l2a_lipGradient_abs_le hζ x i)
      (l2a_integrableOn_mul_memL2 hdiffL2 (φ.toH1Function.gradMemL2 i))
  have hJ5 : IntegrableOn (fun x => (mu x - g.toFun x) * vecDot (lipGradient ζ x) (φg x)) W :=
    (l2a_integrableOn_sum hJ5i).congr_fun (fun x _ => by
      simp only [vecDot, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring) hW.measurableSet
  -- the equation tested with ζ φ
  set Θ : H1Function W := mulLip hW φ.toH1Function hζ (M := 1) hM1 with hΘ
  have hΘ0 : ∀ x ∈ W, x ∉ K → Θ.toFun x = 0 := fun x _ hx => by
    simp [hΘ, hζK x hx]
  have hconv := l2a_convolution_identity hW hWb hh hη hη0 hK hKW hF hf hweak Θ hΘ0
  have hconv' : ∫ x in W, (ζ x * vecDot (M x) (φg x) + φf x * vecDot (M x) (lipGradient ζ x)) =
      ∫ x in W, l2a_moll d h η f x * (ζ x * φf x) :=
    (setIntegral_congr_fun hW.measurableSet fun x _ =>
      (l2a_vecDot_two (ζ x) (φf x) (M x) (lipGradient ζ x) (φg x)).symm).trans hconv
  rw [integral_add hJ1 hJ2] at hconv'
  have hpt : ∀ x, s * vecDot ((l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1).grad x) (φg x) =
      ζ x * vecDot (M x) (φg x) - ζ x * vecDot (MD x) (φg x) +
        s * ((1 - ζ x) * vecDot (g.grad x) (φg x)) +
        s * ((mu x - g.toFun x) * vecDot (lipGradient ζ x) (φg x)) := fun x => by
    rw [l2a_wH1_grad hW hWb hh hη hη0 u g hζ hζ0 hζ1 x, l2a_vecDot_three]
    have key : ζ x * (s * vecDot (Mu x) (φg x)) =
        ζ x * vecDot (M x) (φg x) - ζ x * vecDot (MD x) (φg x) := by
      by_cases hxK : x ∈ K
      · simp only [vecDot, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have e : M x i = s * Mu x i + MD x i := l2a_flux_split hh hη hη0 hK hKW hF u s hxK i
        rw [e]; ring
      · simp [hζK x hxK]
    show s * (ζ x * vecDot (Mu x) (φg x) + (1 - ζ x) * vecDot (g.grad x) (φg x) +
        (mu x - g.toFun x) * vecDot (lipGradient ζ x) (φg x)) = _
    linarith only [key]
  have hmain : s * ∫ x in W, vecDot ((l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1).grad x) (φg x) =
      (∫ x in W, ζ x * vecDot (M x) (φg x)) - (∫ x in W, ζ x * vecDot (MD x) (φg x)) +
        s * (∫ x in W, (1 - ζ x) * vecDot (g.grad x) (φg x)) +
        s * (∫ x in W, (mu x - g.toFun x) * vecDot (lipGradient ζ x) (φg x)) := by
    rw [← integral_const_mul]
    rw [setIntegral_congr_fun hW.measurableSet fun x _ => hpt x]
    have hS1 : IntegrableOn (fun x => ζ x * vecDot (M x) (φg x) - ζ x * vecDot (MD x) (φg x)) W :=
      hJ1.sub hJ3
    have hS4 : IntegrableOn (fun x => s * ((1 - ζ x) * vecDot (g.grad x) (φg x))) W :=
      hJ4.const_mul s
    have hS5 : IntegrableOn
        (fun x => s * ((mu x - g.toFun x) * vecDot (lipGradient ζ x) (φg x))) W :=
      hJ5.const_mul s
    have hS14 : IntegrableOn (fun x => ζ x * vecDot (M x) (φg x) - ζ x * vecDot (MD x) (φg x) +
        s * ((1 - ζ x) * vecDot (g.grad x) (φg x))) W := hS1.add hS4
    rw [integral_add hS14 hS5, integral_add hS1 hS4, integral_sub hJ1 hJ3, integral_const_mul,
      integral_const_mul]
  have hf1 : ∫ x in W, (ζ x * l2a_moll d h η f x) * φf x =
      ∫ x in W, l2a_moll d h η f x * (ζ x * φf x) :=
    setIntegral_congr_fun hW.measurableSet fun x _ => by ring
  have hf2 : ∫ x in W, φf x * vecDot (lipGradient ζ x) (M x) =
      ∫ x in W, φf x * vecDot (M x) (lipGradient ζ x) :=
    setIntegral_congr_fun hW.measurableSet fun x _ => by rw [vecDot_comm]
  rw [hmain, hf1, hf2]
  linarith only [hconv']

/-- **The equation for `w - uhom`** (against the constant coefficient problem).
If moreover `-s Δ uhom = f` weakly in `W` (and `f φ` is integrable for test functions `φ`), then
for every `φ ∈ H¹₀(W)`,
`s ∫ ∇(w - uhom)·∇φ = ∫ (ζ η∗f - f) φ - ∫ φ ∇ζ·η∗F - ∫ ζ (η∗(F - s∇ũ))·∇φ
  + s ∫ (1-ζ) ∇g·∇φ + s ∫ (η∗ũ - g) ∇ζ·∇φ`. -/
theorem l2a_comparison_identity_hom {W : Set (Vec d)} (hW : IsOpen W)
    (hWb : Bornology.IsBounded W) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {K : Set (Vec d)}
    (hK : IsCompact K) (hKW : Metric.cthickening h K ⊆ W) {Kz : ℝ≥0} {ζ : Vec d → ℝ}
    (hζ : LipschitzWith Kz ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1)
    (hζK : ∀ x, x ∉ K → ζ x = 0) (u : H1Function (Set.univ : Set (Vec d))) (g uhom : H1Function W)
    {F : Vec d → Vec d} {f : Vec d → ℝ} (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) W volume)
    (hf : LocallyIntegrableOn f W volume)
    (hweak : ∀ φ : H10Function W,
      ∫ x in W, vecDot (F x) (φ.toH1Function.grad x) = ∫ x in W, f x * φ.toH1Function.toFun x)
    (s : ℝ)
    (hhom : ∀ φ : H10Function W,
      s * ∫ x in W, vecDot (uhom.grad x) (φ.toH1Function.grad x) =
        ∫ x in W, f x * φ.toH1Function.toFun x)
    (hfφ : ∀ φ : H10Function W, IntegrableOn (fun x => f x * φ.toH1Function.toFun x) W)
    (φ : H10Function W) :
    s * ∫ x in W, vecDot ((l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1).grad x - uhom.grad x)
        (φ.toH1Function.grad x) =
      (∫ x in W, (ζ x * l2a_moll d h η f x - f x) * φ.toH1Function.toFun x)
        - (∫ x in W, φ.toH1Function.toFun x *
            vecDot (lipGradient ζ x) (a16_mollify d h η F x))
        - (∫ x in W, ζ x * vecDot (a16_mollify d h η (fun y => F y - s • u.grad y) x)
            (φ.toH1Function.grad x))
        + s * (∫ x in W, (1 - ζ x) * vecDot (g.grad x) (φ.toH1Function.grad x))
        + s * (∫ x in W, (l2a_moll d h η u.toFun x - g.toFun x) *
            vecDot (lipGradient ζ x) (φ.toH1Function.grad x)) := by
  have hmain := l2a_comparison_identity hW hWb hh hη hη0 hK hKW hζ hζ0 hζ1 hζK u g hF hf hweak s φ
  set w := l2a_wH1 hW hWb hh hη hη0 u g hζ hζ0 hζ1 with hw
  have hgi : ∀ (v : H1Function W) (i : Fin d),
      IntegrableOn (fun x => v.grad x i * φ.toH1Function.grad x i) W := fun v i =>
    l2a_integrableOn_mul_memL2 (v.gradMemL2 i) (φ.toH1Function.gradMemL2 i)
  have hdot : ∀ v : H1Function W, IntegrableOn
      (fun x => vecDot (v.grad x) (φ.toH1Function.grad x)) W := fun v =>
    l2a_integrableOn_sum (f := fun i x => v.grad x i * φ.toH1Function.grad x i) (hgi v)
  have hsub : ∫ x in W, vecDot (w.grad x - uhom.grad x) (φ.toH1Function.grad x) =
      (∫ x in W, vecDot (w.grad x) (φ.toH1Function.grad x)) -
        ∫ x in W, vecDot (uhom.grad x) (φ.toH1Function.grad x) := by
    rw [← integral_sub (hdot w) (hdot uhom)]
    refine setIntegral_congr_fun hW.measurableSet fun x _ => ?_
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  -- the integrability of `ζ η∗f φ`
  have hKW0 : K ⊆ W := (Metric.self_subset_cthickening K).trans hKW
  obtain ⟨hfp, hfpc⟩ := l2a_cut_integrable hK hKW hf
  obtain ⟨hmc, hmcc⟩ := l2a_moll_cont_compact hh hη hη0 hfp hfpc
  have hζcont : Continuous ζ := hζ.continuous
  have hc : Continuous fun x => ζ x * l2a_moll d h η ((Metric.cthickening h K).indicator f) x :=
    hζcont.mul hmc
  have hcc : HasCompactSupport fun x =>
      ζ x * l2a_moll d h η ((Metric.cthickening h K).indicator f) x :=
    HasCompactSupport.of_support_subset_isCompact hK fun x hx => by
      by_contra hxK; exact hx (by simp [hζK x hxK])
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hcc
  have hint : IntegrableOn (fun x => (ζ x * l2a_moll d h η f x) * φ.toH1Function.toFun x) W := by
    have := l2a_integrableOn_bdd (W := W) hc.aestronglyMeasurable hB
      (l2a_integrableOn_of_memL2 hWb φ.toH1Function.memL2)
    refine this.congr_fun (fun x _ => ?_) hW.measurableSet
    by_cases hxK : x ∈ K
    · simp only [l2a_moll_indicator_eq hh hη0 hxK]
    · simp [hζK x hxK]
  have hsplit : ∫ x in W, (ζ x * l2a_moll d h η f x - f x) * φ.toH1Function.toFun x =
      (∫ x in W, (ζ x * l2a_moll d h η f x) * φ.toH1Function.toFun x) -
        ∫ x in W, f x * φ.toH1Function.toFun x := by
    rw [← integral_sub hint (hfφ φ)]
    exact setIntegral_congr_fun hW.measurableSet fun x _ => by ring
  rw [hsub, mul_sub, hmain, hhom φ, hsplit]
  ring

/-- Satisfiability witness for the cutoff: the unit Euclidean ball, with margin `r₀ / 2`. -/
example [NeZero d] : True := by
  obtain ⟨r₀, M₁, M₂, D, hdom⟩ := isUniformC11Domain_euclidBall (d := d)
  obtain ⟨C, _, H⟩ := l2a_exists_cutoff (d := d) r₀ M₁ D hdom.2.1
  have := H hdom (r := r₀ / 2) (by linarith only [hdom.2.1]) (by linarith only)
  trivial

/-- Satisfiability witness for the comparison identities: zero data on the unit ball of `ℝ`,
margin `1/2`, mollification scale `1/4`, the cutoff of `l2a_cutoff`, a smooth profile. -/
example (φ : H10Function (Metric.ball (0 : Vec 1) 1)) : True := by
  have hW : IsOpen (Metric.ball (0 : Vec 1) 1) := Metric.isOpen_ball
  have hWb : Bornology.IsBounded (Metric.ball (0 : Vec 1) 1) := Metric.isBounded_ball
  obtain ⟨η, hη, hη0⟩ := l2a_exists_smooth_profile 1
  obtain ⟨K, hK, hKW, hζK⟩ := l2a_cutoff_margin_data (W := Metric.ball (0 : Vec 1) 1) hWb
    (r := 1 / 2) (h := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
  have _ := l2a_comparison_identity_hom hW hWb (h := 1 / 4) (by norm_num) hη hη0 hK hKW
    (l2a_cutoff_lipschitz _ (r := 1 / 2) (by norm_num)) (l2a_cutoff_nonneg _ _)
    (l2a_cutoff_le_one _ _) hζK 0 0 0 (F := fun _ => 0) (f := fun _ => 0)
    (fun _ => locallyIntegrableOn_const _) (locallyIntegrableOn_const _)
    (fun φ => by simp [vecDot]) 1 (fun φ => by simp [vecDot]) (fun φ => by simp) φ
  trivial

end SuperdiffusionCLT.Section7
