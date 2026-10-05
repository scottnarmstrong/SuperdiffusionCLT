/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import SuperdiffusionCLT.Section7.Prereq.MollifiedFluxC
public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonD
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.ZeroExtension
public import SuperdiffusionCLT.Section7.Root.InteriorApprox

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A measurable version of the zero extension of an `H¹₀(V)` function and of its gradient. -/
theorem ia_measurable_zero_ext {V : Set (Vec d)} (hV : IsOpen V) (φ : H10Function V) :
    ∃ (ψ : Vec d → ℝ) (G : Vec d → Vec d), Measurable ψ ∧ (∀ i, Measurable fun x => G x i) ∧
      (∀ x, x ∉ V → ψ x = 0) ∧ (∀ x, x ∉ V → G x = 0) ∧
      (∀ᵐ x ∂(volume.restrict V), ψ x = φ.toH1Function.toFun x) ∧
      (∀ᵐ x ∂(volume.restrict V), G x = φ.toH1Function.grad x) ∧
      HasWeakGradientOn Set.univ ψ G ∧ LocallyIntegrable ψ volume ∧
      ∀ i, LocallyIntegrable (fun x => G x i) volume := by
  have hm := hV.measurableSet
  have hg := φ.hasWeakGradientOn_univ_zeroExtension hm
  have hu0 : MemLp φ.zeroExtension 2 volume := φ.memLp_zeroExtension hm φ.toH1Function.memL2
  have hDu : ∀ i, MemLp (fun x => φ.zeroExtensionGrad x i) 2 volume := fun i => by
    have := φ.gradMemLp_zeroExtensionGrad hm φ.toH1Function.gradMemL2 i
    simpa only [MemLpOn, Measure.restrict_univ] using this
  set ψ0 := hu0.aestronglyMeasurable.mk φ.zeroExtension with hψ0
  have hψ0m : StronglyMeasurable ψ0 := hu0.aestronglyMeasurable.stronglyMeasurable_mk
  have hψ0e : φ.zeroExtension =ᵐ[volume] ψ0 := hu0.aestronglyMeasurable.ae_eq_mk
  set G0 : Fin d → Vec d → ℝ := fun i => (hDu i).aestronglyMeasurable.mk
    (fun x => φ.zeroExtensionGrad x i) with hG0
  have hG0m : ∀ i, StronglyMeasurable (G0 i) := fun i =>
    (hDu i).aestronglyMeasurable.stronglyMeasurable_mk
  have hG0e : ∀ i, (fun x => φ.zeroExtensionGrad x i) =ᵐ[volume] G0 i := fun i =>
    (hDu i).aestronglyMeasurable.ae_eq_mk
  have hψe : (V.indicator ψ0) =ᵐ[volume] φ.zeroExtension := by
    filter_upwards [hψ0e] with x hx
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV, ← hx]
    · rw [Set.indicator_of_notMem hxV, φ.zeroExtension_apply_of_not_mem hxV]
  have hGe : ∀ i, (fun x => V.indicator (G0 i) x) =ᵐ[volume]
      (fun x => φ.zeroExtensionGrad x i) := fun i => by
    filter_upwards [hG0e i] with x hx
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV, ← hx]
    · rw [Set.indicator_of_notMem hxV, φ.zeroExtensionGrad_apply_of_not_mem hxV]; rfl
  refine ⟨V.indicator ψ0, fun x i => V.indicator (G0 i) x, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hψ0m.measurable.indicator hm
  · intro i
    exact (hG0m i).measurable.indicator hm
  · intro x hx; simp [Set.indicator_of_notMem hx]
  · intro x hx; funext i; simp [Set.indicator_of_notMem hx]
  · filter_upwards [ae_restrict_of_ae hψe, ae_restrict_mem hm] with x hx hxV
    rw [hx, φ.zeroExtension_apply_of_mem hxV]
  · have : ∀ᵐ x ∂(volume.restrict V), ∀ i, V.indicator (G0 i) x = φ.toH1Function.grad x i := by
      rw [ae_all_iff]
      intro i
      filter_upwards [ae_restrict_of_ae (hGe i), ae_restrict_mem hm] with x hx hxV
      rw [hx, φ.zeroExtensionGrad_apply_of_mem hxV]
    filter_upwards [this] with x hx
    funext i
    exact hx i
  · intro i φ' hφ hφc hφU
    have h1 := hg i φ' hφ hφc hφU
    have e1 : ∫ x in (Set.univ : Set (Vec d)), V.indicator ψ0 x * (fderiv ℝ φ' x) (basisVec i)
        = ∫ x in (Set.univ : Set (Vec d)), φ.zeroExtension x * (fderiv ℝ φ' x) (basisVec i) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hψe] with x hx
      rw [hx]
    have e2 : ∫ x in (Set.univ : Set (Vec d)), V.indicator (G0 i) x * φ' x
        = ∫ x in (Set.univ : Set (Vec d)), φ.zeroExtensionGrad x i * φ' x := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (hGe i)] with x hx
      rw [hx]
    rw [e1, e2]
    exact h1
  · exact (MemLp.ae_eq hψe.symm hu0).locallyIntegrable (by norm_num)
  · intro i
    exact (MemLp.ae_eq (hGe i).symm (hDu i)).locallyIntegrable (by norm_num)

/-- The reflected profile has the reflected kernel. -/
theorem ia_kernel_neg (h : ℝ) (η : Vec d → ℝ) (w : Vec d) :
    a16_kernel d h (fun v => η (-v)) w = a16_kernel d h η (-w) := by
  unfold a16_kernel
  rw [smul_neg]

/-- **The pairing estimate behind the `W^{-1,p}` bound of `f - η_h ∗ f`.** -/
theorem ia_pairing_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    {V : Set (Vec d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V) {ψ : Vec d → ℝ}
    {G : Vec d → Vec d} (hψm : Measurable ψ) (hGm : ∀ i, Measurable fun x => G x i)
    (hψ0 : ∀ x, x ∉ V → ψ x = 0) (hG0 : ∀ x, x ∉ V → G x = 0)
    (hgrad : HasWeakGradientOn Set.univ ψ G) (hψl : LocallyIntegrable ψ volume)
    (hGl : ∀ i, LocallyIntegrable (fun x => G x i) volume)
    {f : Vec d → ℝ} (hfm : Measurable f) {Fs : ℝ} (hFs : 0 ≤ Fs)
    (hfb : ∀ x ∈ Metric.cthickening h V, |f x| ≤ Fs) :
    ENNReal.ofReal |∫ x in V, (f x - l2a_moll d h η f x) * ψ x| ≤
      ENNReal.ofReal (Fs * (Real.sqrt d * h)) * ∫⁻ x in V, ENNReal.ofReal (eucNorm (G x)) := by
  set T := Metric.cthickening h V with hTdef
  have hTc : IsClosed T := Metric.isClosed_cthickening
  have hTm : MeasurableSet T := hTc.measurableSet
  have hTb : Bornology.IsBounded T := hVb.cthickening
  have hTcpt : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTc hTb
  have hVT : V ⊆ T := Metric.self_subset_cthickening V
  set f1 : Vec d → ℝ := T.indicator f with hf1
  have hf1b : ∀ x, |f1 x| ≤ Fs := by
    intro x
    by_cases hx : x ∈ T
    · rw [hf1, Set.indicator_of_mem hx]; exact hfb x hx
    · rw [hf1, Set.indicator_of_notMem hx]; simpa using hFs
  have hf1int : Integrable f1 volume := by
    refine (integrable_indicator_iff hTm).2 ?_
    refine Measure.integrableOn_of_bounded (M := Fs) hTb.measure_lt_top.ne
      hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hTm] with x hx
    rw [Real.norm_eq_abs]; exact hfb x hx
  have hf1c : HasCompactSupport f1 :=
    HasCompactSupport.of_support_subset_isCompact hTcpt fun x hx => by
      by_contra hxT; exact hx (Set.indicator_of_notMem hxT _)
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact hTcpt fun x hx => by
      by_contra hxT; exact hx (hψ0 x fun hxV => hxT (hVT hxV))
  have hψint : Integrable ψ volume := (integrableOn_iff_integrable_of_support_subset (s := T) (fun x hx => by
      by_contra hxT; exact hx (hψ0 x fun hxV => hxT (hVT hxV)))).1
      (hψl.integrableOn_isCompact hTcpt)
  -- the reflected profile
  set ηt : Vec d → ℝ := fun v => η (-v) with hηt
  have hηtd : ContDiff ℝ (⊤ : ℕ∞) ηt := hη.comp contDiff_neg
  have hηt0 : ∀ w, 0 ≤ ηt w := fun w => hη0 _
  have hηt1 : ∫ w, ηt w = 1 := by
    rw [hηt]; simp only [integral_neg_eq_self (fun v => η v) volume]; exact hη1
  have hηts : ∀ w, (∃ i, 1 < |w i|) → ηt w = 0 := by
    rintro w ⟨i, hi⟩
    apply hηs
    exact ⟨i, by simpa using hi⟩
  set Pt : Vec d → ℝ := fun y => ∫ x, a16_kernel d h η (x - y) * ψ x with hPt
  have hPteq : Pt = l2a_moll d h ηt ψ := by
    funext y
    simp only [hPt, l2a_moll]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show a16_kernel d h η (x - y) * ψ x = a16_kernel d h (fun v => η (-v)) (y - x) * ψ x
    rw [ia_kernel_neg, neg_sub]
  obtain ⟨hPtc, hPtcc⟩ := l2a_moll_cont_compact hh hηtd hηts hψint hψc
  rw [← hPteq] at hPtc hPtcc
  have hPt0 : ∀ y, y ∉ T → Pt y = 0 := fun y hy =>
    l2a_kernel_integral_eq_zero hh hηs (K := V) hψ0 hy
  have hkc : Continuous (a16_kernel d h η) := (l2a_kernel_contDiff hη).continuous
  obtain ⟨B, hB⟩ := hkc.bounded_above_of_compact_support (l2a_kernel_compact hh hηs)
  have hkB : ∀ z, |a16_kernel d h η z| ≤ B := fun z => by simpa using hB z
  have hpair := l2a_pairing hkc hkB hf1int hψint
  obtain ⟨hMc, hMcc⟩ := l2a_moll_cont_compact hh hη hηs hf1int hf1c
  have hi1 : Integrable (fun x => f1 x * ψ x) volume :=
    hψint.bdd_mul (c := Fs) hf1int.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hf1b x) |>.congr
      (Filter.Eventually.of_forall fun x => by simp [mul_comm])
  have hi2 : Integrable (fun x => l2a_moll d h η f1 x * ψ x) volume :=
    l2a_integrable_mul hMc hMcc hψint
  have hi3 : Integrable (fun y => f1 y * Pt y) volume := by
    have := l2a_integrable_mul hPtc hPtcc hf1int
    exact this.congr (Filter.Eventually.of_forall fun x => by simp [mul_comm])
  have hIeq : ∫ x in V, (f x - l2a_moll d h η f x) * ψ x =
      ∫ y, f1 y * (ψ y - Pt y) := by
    have e1 : ∫ x in V, (f x - l2a_moll d h η f x) * ψ x =
        ∫ x, (f1 x - l2a_moll d h η f1 x) * ψ x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := V) (f := fun x =>
        (f1 x - l2a_moll d h η f1 x) * ψ x) (fun x hx => by rw [hψ0 x hx, mul_zero])]
      refine setIntegral_congr_fun hV.measurableSet fun x hx => ?_
      simp only [hf1, Set.indicator_of_mem (hVT hx)]
      rw [l2a_moll_indicator_eq hh hηs hx]
    rw [e1]
    have e2 : ∫ x, (f1 x - l2a_moll d h η f1 x) * ψ x =
        (∫ x, f1 x * ψ x) - ∫ x, l2a_moll d h η f1 x * ψ x := by
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    have e3 : ∫ x, l2a_moll d h η f1 x * ψ x = ∫ y, f1 y * Pt y := by
      rw [← hpair]
      rfl
    rw [e2, e3, ← integral_sub hi1 hi3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hPtm : Measurable Pt := hPtc.measurable
  have hdiff0 : ∀ y, y ∉ T → ψ y - Pt y = 0 := fun y hy => by
    rw [hψ0 y fun hyV => hy (hVT hyV), hPt0 y hy, sub_zero]
  have hsupp : Function.support (fun y => ‖ψ y - Pt y‖ₑ) ⊆ T := fun y hy => by
    by_contra hyT
    apply hy
    simp [hdiff0 y hyT]
  have hW : IsOpen (Metric.thickening (3 * h) V) := Metric.isOpen_thickening
  have hVW : ∀ x ∈ T, ∀ y, dist y x ≤ h → y ∈ Metric.thickening (3 * h) V := by
    intro x hx y hy
    have hx' : x ∈ Metric.thickening (2 * h) V :=
      Metric.cthickening_subset_thickening' (by linarith only [hh]) (by linarith only [hh]) V hx
    obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.1 hx'
    exact Metric.mem_thickening_iff.2 ⟨z, hz, by
      linarith only [dist_triangle y x z, hy, hxz]⟩
  have hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.thickening (3 * h) V →
      ∫ x, ψ x * fderiv ℝ φ x (basisVec i) = -∫ x, G x i * φ x := by
    intro i φ hφ hφc _
    have := hgrad i φ hφ hφc (Set.subset_univ _)
    simpa only [Measure.restrict_univ] using this
  have hm1 := m1_sub_conv_lintegral_le hh (η := ηt) (by exact hηtd.continuous) hηt0 hηt1 hηts hW
    hTm hVW hψm hGm hψl hGl hweak (q := 1) le_rfl
  have hPtl : ∀ x, l2a_moll d h ηt ψ x = Pt x := fun x => by rw [hPteq]
  simp only [ENNReal.rpow_one] at hm1
  have hGsupp : ∫⁻ y in Metric.thickening (3 * h) V, ENNReal.ofReal (eucNorm (G y)) =
      ∫⁻ y in V, ENNReal.ofReal (eucNorm (G y)) := by
    have hs : Function.support (fun y => ENNReal.ofReal (eucNorm (G y))) ⊆ V := fun y hy => by
      by_contra hyV
      apply hy
      simp [hG0 y hyV, eucNorm, vecNormSq, vecDot]
    rw [setLIntegral_eq_of_support_subset (hs.trans (fun x hx =>
      Metric.self_subset_thickening (by linarith only [hh]) V hx)),
      setLIntegral_eq_of_support_subset hs]
  have hm1' : ∫⁻ y, ‖ψ y - Pt y‖ₑ ≤
      ENNReal.ofReal (Real.sqrt d * h) * ∫⁻ y in V, ENNReal.ofReal (eucNorm (G y)) := by
    rw [← setLIntegral_eq_of_support_subset hsupp, ← hGsupp]
    refine le_trans (le_of_eq ?_) hm1
    refine lintegral_congr fun x => ?_
    show ‖ψ x - Pt x‖ₑ = ‖ψ x - ∫ y, a16_kernel d h (fun v => η (-v)) (x - y) * ψ y‖ₑ
    rw [← hηt]
    show ‖ψ x - Pt x‖ₑ = ‖ψ x - l2a_moll d h ηt ψ x‖ₑ
    rw [hPtl]
  rw [hIeq, ← Real.enorm_eq_ofReal_abs]
  calc ‖∫ y, f1 y * (ψ y - Pt y)‖ₑ ≤ ∫⁻ y, ‖f1 y * (ψ y - Pt y)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ENNReal.ofReal Fs * ‖ψ y - Pt y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [enorm_mul]
        refine mul_le_mul' ?_ le_rfl
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hf1b y)
    _ = ENNReal.ofReal Fs * ∫⁻ y, ‖ψ y - Pt y‖ₑ := by
        rw [lintegral_const_mul]
        exact (hψm.sub hPtm).enorm
    _ ≤ ENNReal.ofReal Fs * (ENNReal.ofReal (Real.sqrt d * h) *
          ∫⁻ y in V, ENNReal.ofReal (eucNorm (G y))) := by gcongr
    _ = ENNReal.ofReal (Fs * (Real.sqrt d * h)) * ∫⁻ x in V, ENNReal.ofReal (eucNorm (G x)) := by
        rw [← mul_assoc, ENNReal.ofReal_mul hFs]

/-- Normalized norms increase with the exponent. -/
theorem ia_lpBar_mono {V : Set (Vec d)} (h0 : volume V ≠ 0) (ht : volume V ≠ ⊤) {p q : ℝ≥0∞}
    (hpq : p ≤ q) {E : Type*} [NormedAddCommGroup E] {g : Vec d → E} :
    lpBar V p g ≤ lpBar V q g := by
  unfold lpBar
  have : IsProbabilityMeasure (((volume V)⁻¹) • volume.restrict V) := by
    refine ⟨?_⟩
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 ht
  exact eLpNorm_le_eLpNorm_of_exponent_le hpq

/-- **The `W^{-1,p}` norm of `f - η_h ∗ f`** is at most `d √d h ‖f‖_∞`. -/
theorem ia_wMinusOne_moll [NeZero d] {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    {V : Set (Vec d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V) {f : Vec d → ℝ}
    (hfm : Measurable f) {Fs : ℝ} (hFs : 0 ≤ Fs)
    (hfb : ∀ x ∈ Metric.cthickening h V, |f x| ≤ Fs) {p : ℝ≥0∞} (hp : 1 ≤ p.conjExponent) :
    wMinusOneBar V p (fun x => f x - l2a_moll d h η f x) ≤
      ENNReal.ofReal (Fs * (Real.sqrt d * h) * d) := by
  unfold wMinusOneBar
  refine iSup₂_le fun φ hφ => ?_
  by_cases h0 : volume V = 0
  · have : ∫ x in V, (f x - l2a_moll d h η f x) * φ.toH1Function.toFun x = 0 := by
      rw [Measure.restrict_eq_zero.2 h0]; simp
    simp [this]
  have ht : volume V ≠ ⊤ := hVb.measure_lt_top.ne
  obtain ⟨ψ, G, hψm, hGm, hψ0, hG0, hψe, hGe, hgrad, hψl, hGl⟩ := ia_measurable_zero_ext hV φ
  have hI : ∫ x in V, (f x - l2a_moll d h η f x) * φ.toH1Function.toFun x =
      ∫ x in V, (f x - l2a_moll d h η f x) * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hψe] with x hx
    rw [hx]
  have hpair := ia_pairing_le hh hη hη0 hη1 hηs hV hVb hψm hGm hψ0 hG0 hgrad hψl hGl hfm hFs hfb
  rw [← hI] at hpair
  -- the gradient integral
  have hgm : AEStronglyMeasurable φ.toH1Function.grad (volume.restrict V) := li1_grad_aesm φ
  have hG1 : ∫⁻ x in V, ENNReal.ofReal (eucNorm (G x)) ≤
      ENNReal.ofReal d * (volume V) := by
    have e1 : ∫⁻ x in V, ENNReal.ofReal (eucNorm (G x)) ≤
        ∫⁻ x in V, ENNReal.ofReal d * ‖φ.toH1Function.grad x‖ₑ := by
      refine lintegral_mono_ae ?_
      filter_upwards [hGe] with x hx
      rw [hx, ← ofReal_norm]
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      exact ENNReal.ofReal_le_ofReal (r1_eucNorm_le_mul_norm _)
    refine e1.trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl ?_
    have e2 : ∫⁻ x in V, ‖φ.toH1Function.grad x‖ₑ ≤ volume V := by
      rw [← eLpNorm_one_eq_lintegral_enorm hgm, ia_lpBar_eq_mul (U := V) one_ne_zero ENNReal.one_ne_top
        ht _ hgm]
      simp only [ENNReal.toReal_one, div_one, ENNReal.rpow_one]
      calc volume V * lpBar V 1 φ.toH1Function.grad ≤ volume V * 1 :=
            mul_le_mul' le_rfl ((ia_lpBar_mono h0 ht hp).trans hφ)
        _ = volume V := mul_one _
    exact e2
  set a : ℝ := (volume V).toReal with ha
  have hapos : 0 < a := ENNReal.toReal_pos h0 ht
  have hvol : volume V = ENNReal.ofReal a := (ENNReal.ofReal_toReal ht).symm
  have hc1 : 0 ≤ Fs * (Real.sqrt d * h) := by positivity
  have hI2 : ENNReal.ofReal |∫ x in V, (f x - l2a_moll d h η f x) * ψ x| ≤
      ENNReal.ofReal (Fs * (Real.sqrt d * h) * d * a) := by
    refine le_trans (le_of_eq (by rw [hI])) (hpair.trans ?_)
    calc ENNReal.ofReal (Fs * (Real.sqrt d * h)) * ∫⁻ x in V, ENNReal.ofReal (eucNorm (G x))
        ≤ ENNReal.ofReal (Fs * (Real.sqrt d * h)) * (ENNReal.ofReal d * volume V) :=
          mul_le_mul' le_rfl hG1
      _ = ENNReal.ofReal (Fs * (Real.sqrt d * h) * d * a) := by
          rw [hvol, ← ENNReal.ofReal_mul (Nat.cast_nonneg d), ← ENNReal.ofReal_mul hc1]
          ring_nf
  have hI3 : |∫ x in V, (f x - l2a_moll d h η f x) * ψ x| ≤ Fs * (Real.sqrt d * h) * d * a :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hI2
  rw [hI, abs_mul, abs_of_pos (inv_pos.2 hapos)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc a⁻¹ * |∫ x in V, (f x - l2a_moll d h η f x) * ψ x|
      ≤ a⁻¹ * (Fs * (Real.sqrt d * h) * d * a) := mul_le_mul_of_nonneg_left hI3 (inv_nonneg.2 hapos.le)
    _ = Fs * (Real.sqrt d * h) * d := by field_simp

/-- A smooth nonnegative normalized profile supported in the unit sup-ball. -/
theorem ia_exists_profile (d : ℕ) :
    ∃ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ (∀ w, 0 ≤ η w) ∧ ∫ w, η w = 1 ∧
      ∀ w, (∃ i, 1 < |w i|) → η w = 0 := by
  refine ⟨li1_bump d, li1_bump_contDiff d, li1_bump_nonneg d, li1_bump_integral d, ?_⟩
  rintro w ⟨i, hi⟩
  by_contra hne
  have h1 := li1_bump_norm_lt hne
  have h2 : |w i| ≤ ‖w‖ := by simpa using norm_le_pi_norm w i
  linarith only [h1, h2, hi]

/-- Satisfiability of `ia_wMinusOne_moll`: the zero function on the unit ball. -/
example : ∃ (η : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) η ∧ ∫ w, η w = 1 ∧
    wMinusOneBar (Metric.ball (0 : Vec 2) 1) 2
      (fun x => (fun _ : Vec 2 => (0 : ℝ)) x - l2a_moll 2 1 η (fun _ => (0 : ℝ)) x) ≤
      ENNReal.ofReal (0 * (Real.sqrt (2 : ℕ) * 1) * (2 : ℕ)) := by
  obtain ⟨η, hη, hη0, hη1, hηs⟩ := ia_exists_profile 2
  refine ⟨η, hη, hη1, ?_⟩
  have := ia_wMinusOne_moll (d := 2) (h := 1) (V := Metric.ball (0 : Vec 2) 1) one_pos hη hη0 hη1 hηs Metric.isOpen_ball
    Metric.isBounded_ball (f := fun _ => 0) measurable_const (Fs := 0) le_rfl
    (fun x _ => by simp) (p := 2) (by simp [ENNReal.conjExponent])
  exact this

end SuperdiffusionCLT.Section7
