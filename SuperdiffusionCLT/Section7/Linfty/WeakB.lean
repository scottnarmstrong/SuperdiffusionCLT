/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Weak
public import SuperdiffusionCLT.Section7.Prereq.RootCarriers

/-!
# The weak norms of the solution against the comparison function

Displays `e.Dir.new.Linfty.grad.vw` and
`e.Dir.new.Linfty.flux.vw`: componentwise, the difference of the gradient (resp. the rescaled flux)
of the solution and the gradient of the comparison function is a sum of five terms, each bounded
in `W^{-1,2}` by a mollification error, a layer term, or a sup bound.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Locality of the mollified gradient of the extension: where the cutoff is non-zero the
mollification of `∇ũ` equals that of the cleaned gradient of `v`. -/
theorem linf_weak_loc {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hhr : h ≤ r / 4) {η : Vec d → ℝ}
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) (v : H1Function W) (i : Fin d) (x : Vec d) :
    l2a_cutoff W r x * l2a_moll d h η (fun y => (l2c_ext hW hWb hr v).grad y i) x =
      l2a_cutoff W r x * l2a_moll d h η (fun y => l2d_gradc W v y i) x := by
  by_cases hx : l2a_cutoff W r x = 0
  · simp [hx]
  congr 1
  refine l2a_moll_congr hh hηs fun y hy => ?_
  have h1 : r < Metric.infDist x Wᶜ := l2a_cutoff_ne_zero_imp hr hx
  have h2 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := Wᶜ)
  have h3 : dist x y ≤ h := by rw [dist_comm]; exact hy
  have h4 : r / 2 < Metric.infDist y Wᶜ := by linarith only [h1, h2, h3, hhr, hr]
  have hyV : y ∈ W := by
    by_contra hyV
    have : Metric.infDist y Wᶜ = 0 := Metric.infDist_zero_of_mem (show y ∈ Wᶜ from hyV)
    linarith only [this, h4, hr]
  simp only [l2d_gradc, l2d_indicator_apply, Set.indicator_of_mem hyV]
  rw [l2c_ext_grad hW hWb hr v hyV h4]

/-- The components of the gradient of the comparison function. -/
theorem linf_weak_wgrad {W : Set (Vec d)} (hW : IsOpen W) (hWb : Bornology.IsBounded W) {r h : ℝ}
    (hr : 0 < r) (hh : 0 < h) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) (ũ : H1Function (Set.univ : Set (Vec d)))
    {gt : Vec d → ℝ} (hgt : ContDiff ℝ 1 gt) (hb : IsBoundedDomain W) (x : Vec d) (i : Fin d) :
    (l2d_w hW hWb hr hh hη hηs ũ (li1_h1 hW hb hgt)).grad x i =
      l2a_cutoff W r x * l2a_moll d h η (fun y => ũ.grad y i) x +
        (1 - l2a_cutoff W r x) * fderiv ℝ gt x (basisVec i) +
        (l2a_moll d h η ũ.toFun x - gt x) * lipGradient (l2a_cutoff W r) x i := by
  have := congrFun (l2a_wH1_grad hW hWb hh hη hηs ũ (li1_h1 hW hb hgt)
    (l2a_cutoff_lipschitz W hr) (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r) x) i
  simpa [l2d_w, li1_h1_grad, li1_h1_toFun] using this

theorem linf_weak_abs_fderiv (f : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    |fderiv ℝ f x (basisVec i)| ≤ ‖fderiv ℝ f x‖ := by
  have h2 : ‖basisVec (d := d) i‖ = 1 := by simp [basisVec, Pi.norm_single]
  have := (fderiv ℝ f x).le_opNorm (basisVec i)
  rw [h2, mul_one] at this
  simpa using this

theorem linf_weak_comp_memLp {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp F 2 (volume.restrict U)) (i : Fin d) :
    MemLp (fun x => F x i) 2 (volume.restrict U) :=
  hF.of_le ((continuous_apply i).comp_aestronglyMeasurable hF.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => by
      simpa using norm_le_pi_norm (F x) i)


theorem linf_weak_sum {f : Fin d → ℝ≥0∞} {X : ℝ} (h : ∀ i, f i ≤ ENNReal.ofReal X) :
    ∑ i, f i ≤ ENNReal.ofReal (d * X) := by
  refine (Finset.sum_le_sum fun i _ => h i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]

/-- **The two weak norms of `v` against the comparison function** (`e.Dir.new.Linfty.grad.vw`,
`e.Dir.new.Linfty.flux.vw`), by commuting the mollifier onto the test function;
the energies `Ev`, `Ea` are the crude ones. -/
theorem linf_weak [NeZero d] (M₁ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {n : ℕ} {r : ℝ} (hr : 0 < r),
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → 2 * (3 : ℝ) ^ n < r →
      (3 : ℝ) ^ n ≤ r / 4 → volume W ≠ 0 → ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L →
      ∀ {η : Vec d → ℝ} {Bη : ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η), (∀ w, |η w| ≤ Bη) →
        (∀ w, 0 ≤ η w) → ∫ w, η w = 1 → ∀ (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0),
      ∀ (a : CoeffField d) {s : ℝ}, 0 < s → ∀ (v : H1Function W) {gt : Vec d → ℝ}
        (hgt : ContDiff ℝ 1 gt),
        MemVectorL2 W (fun x => matVecMul (a x) (v.grad x)) →
        MemH10 W (fun x => v.toFun x - gt x) →
      ∀ {B1 B2 G Ev Ea : ℝ}, 0 ≤ B1 → 0 ≤ B2 → 0 ≤ G → 0 ≤ Ev → 0 ≤ Ea →
        (∀ x ∈ W, ‖fderiv ℝ gt x‖ ≤ G) →
        lpBar W 2 (fun x => eucNorm (v.grad x)) ≤ ENNReal.ofReal Ev →
        lpBar W 2 (fun x => eucNorm (matVecMul (a x) (v.grad x))) ≤ ENNReal.ofReal Ea →
        (∀ x ∈ W, l2a_cutoff W r x ≠ 0 →
          ‖a16_mollify d ((3 : ℝ) ^ n) η
            (fun y => l2d_flux a W v y - s • l2d_gradc W v y) x‖ ≤ B1) →
        (∀ x ∈ W, lipGradient (l2a_cutoff W r) x ≠ 0 →
          |l2a_moll d ((3 : ℝ) ^ n) η (l2c_ext hU.1 (l2c_bounded hU) hr v).toFun x - gt x| ≤ B2) →
        hMinusOneVec W (fun x => v.grad x -
            (l2d_w hU.1 (l2c_bounded hU) hr (pow_pos (by norm_num : (0 : ℝ) < 3) n) hη hηs
              (l2c_ext hU.1 (l2c_bounded hU) hr v)
              (li1_h1 hU.1 (p14g_isBoundedDomain hU) hgt)).grad x) ≤
            ENNReal.ofReal (C * (r * (Ev + G) + B2)) ∧
          hMinusOneVec W (fun x => s⁻¹ • matVecMul (a x) (v.grad x) -
            (l2d_w hU.1 (l2c_bounded hU) hr (pow_pos (by norm_num : (0 : ℝ) < 3) n) hη hηs
              (l2c_ext hU.1 (l2c_bounded hU) hr v)
              (li1_h1 hU.1 (p14g_isBoundedDomain hU) hgt)).grad x) ≤
            ENNReal.ofReal (C * (L * (s⁻¹ * B1) + r * (s⁻¹ * Ea + Ev + G) + B2)) := by
  obtain ⟨K1, hK1, E1⟩ := linf_weak_E1 (d := d) M₁
  obtain ⟨K2, hK2, LB⟩ := linf_weak_layer_bound (d := d) M₁
  obtain ⟨c, hc, SU⟩ := linf_weak_sup (d := d)
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  set Kb : ℝ := 2 * ((d : ℝ) + K1 + K2 + c + 1) with hKb
  have hKb1 : 1 ≤ Kb := by linarith only [hKb, hd, hK1, hK2, hc]
  refine ⟨d * Kb, by positivity, ?_⟩
  intro r₀ W M₂ D hU n r hr h3r hn hhr hW0 z L hL hsub η Bη hη hηA hη0 hη1 hηs a s hs v gt hgt
    hflux _hMH B1 B2 G Ev Ea hB1 hB2 hG0 hEv0 hEa0 hG hEv hEa hB1' hB2'
  have hWo : IsOpen W := hU.1
  have hVb := l2c_bounded hU
  have hbd := p14g_isBoundedDomain hU
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWT : volume W ≠ ⊤ := hVb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hfin : IsFiniteMeasure (volume.restrict W) := ⟨by simpa using hVb.measure_lt_top⟩
  set h : ℝ := (3 : ℝ) ^ n with hhdef
  set ζ := l2a_cutoff W r with hζdef
  set ũ := l2c_ext hWo hVb hr v with hũ
  set w := l2d_w hWo hVb hr h3 hη hηs ũ (li1_h1 hWo hbd hgt) with hwdef
  have hζc : Continuous ζ := l2a_cutoff_continuous W hr
  have hζ0 := l2a_cutoff_nonneg W r
  have hζ1 := l2a_cutoff_le_one W r
  have hdgt : Continuous (fderiv ℝ gt) := hgt.continuous_fderiv (by norm_num)
  have hgtc : Continuous gt := hgt.continuous
  have hrinv : 0 < 1 / r := by positivity
  -- the cleaned components
  set Gf : Fin d → Vec d → ℝ := fun i y => l2d_gradc W v y i with hGf
  set Pf : Fin d → Vec d → ℝ := fun i y => (l2d_flux a W v y - s • l2d_gradc W v y) i with hPf
  set fl : Fin d → Vec d → ℝ := fun i x => matVecMul (a x) (v.grad x) i with hfl
  have hflm : ∀ i, MemLp (fl i) 2 (volume.restrict W) := fun i =>
    linf_weak_comp_memLp hflux i
  have hvm : ∀ i, MemLp (fun x => v.grad x i) 2 (volume.restrict W) := fun i => v.gradMemL2 i
  have hGeq : ∀ i, Gf i = W.indicator (fun x => v.grad x i) := fun i => by
    funext y
    exact l2d_indicator_apply W v.grad y i
  have hPeq : ∀ i, Pf i = W.indicator (fun x => fl i x - s * v.grad x i) := fun i => by
    funext y
    by_cases hy : y ∈ W
    · simp [hPf, hfl, l2d_flux, l2d_gradc, Set.indicator_of_mem hy]
    · simp [hPf, hfl, l2d_flux, l2d_gradc, Set.indicator_of_notMem hy]
  have hGval : ∀ i, ∀ x ∈ W, Gf i x = v.grad x i := fun i x hx => by
    rw [hGeq, Set.indicator_of_mem hx]
  have hPval : ∀ i, ∀ x ∈ W, Pf i x = fl i x - s * v.grad x i := fun i x hx => by
    rw [hPeq, Set.indicator_of_mem hx]
  have hGmem : ∀ i, MemLp (Gf i) 2 (volume.restrict W) := fun i => by
    rw [hGeq]
    exact ((memLp_indicator_iff_restrict hWm).2 (hvm i)).mono_measure Measure.restrict_le_self
  have hPmem : ∀ i, MemLp (Pf i) 2 (volume.restrict W) := fun i => by
    rw [hPeq]
    exact ((memLp_indicator_iff_restrict hWm).2 ((hflm i).sub ((hvm i).const_mul s))).mono_measure
      Measure.restrict_le_self
  have hGloc : ∀ i, LocallyIntegrable (Gf i) volume := fun i => by
    rw [hGeq]; exact linf_weak_locInt hWm (hvm i)
  have hPloc : ∀ i, LocallyIntegrable (Pf i) volume := fun i => by
    rw [hPeq]; exact linf_weak_locInt hWm ((hflm i).sub ((hvm i).const_mul s))
  -- mollifications
  have hmG : ∀ i, Continuous (l2a_moll d h η (Gf i)) := fun i =>
    (l2a_moll_contDiff h3 hη hηs (hGloc i)).continuous
  have hmP : ∀ i, Continuous (l2a_moll d h η (Pf i)) := fun i =>
    (l2a_moll_contDiff h3 hη hηs (hPloc i)).continuous
  have hmU : Continuous (l2a_moll d h η ũ.toFun) :=
    (l2a_moll_contDiff h3 hη hηs (l2a_locInt_of_memL2_univ ũ.memL2)).continuous
  -- the normalized norms
  have hGlp : ∀ i, lpBar W 2 (Gf i) ≤ ENNReal.ofReal Ev := fun i =>
    (linf_weak_lpBar_mono hWm (hGmem i).aestronglyMeasurable
      (g := fun x => eucNorm (v.grad x)) (fun x hx => by
        rw [hGval i x hx, Real.norm_eq_abs,
          Real.norm_of_nonneg (show 0 ≤ eucNorm (v.grad x) from Real.sqrt_nonneg _)]
        exact abs_le_eucNorm _ i)).trans hEv
  have hPlp : ∀ i, lpBar W 2 (Pf i) ≤ ENNReal.ofReal (Ea + s * Ev) := fun i => by
    have h1 : lpBar W 2 (Pf i) ≤ lpBar W 2 (fun x =>
        eucNorm (matVecMul (a x) (v.grad x)) + s * eucNorm (v.grad x)) := by
      refine linf_weak_lpBar_mono hWm (hPmem i).aestronglyMeasurable (fun x hx => ?_)
      rw [hPval i x hx, Real.norm_eq_abs, Real.norm_of_nonneg
        (add_nonneg (show 0 ≤ eucNorm (matVecMul (a x) (v.grad x)) from Real.sqrt_nonneg _)
          (mul_nonneg hs.le (show 0 ≤ eucNorm (v.grad x) from Real.sqrt_nonneg _)))]
      calc |fl i x - s * v.grad x i| ≤ |fl i x| + |s * v.grad x i| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul, abs_of_pos hs]
          exact add_le_add (abs_le_eucNorm (matVecMul (a x) (v.grad x)) i)
            (mul_le_mul_of_nonneg_left (abs_le_eucNorm (v.grad x) i) hs.le)
    have h2 : lpBar W 2 (fun x => s * eucNorm (v.grad x)) =
        ENNReal.ofReal |s| * lpBar W 2 (fun x => eucNorm (v.grad x)) :=
      l2d_lpBar_const_smul s (fun x => eucNorm (v.grad x)) 2
    refine h1.trans ((l2d_lpBar_add_le (by norm_num) (fun x => eucNorm (matVecMul (a x) (v.grad x)))
      (fun x => s * eucNorm (v.grad x))).trans ?_)
    rw [h2, abs_of_pos hs, ENNReal.ofReal_add hEa0 (mul_nonneg hs.le hEv0),
      ENNReal.ofReal_mul hs.le]
    exact add_le_add hEa (mul_le_mul' le_rfl hEv)
  -- the five terms
  set Eh : (Vec d → ℝ) → Vec d → ℝ := fun f x => ζ x * l2a_moll d h η f x - f x with hEh
  set T4 : Fin d → Vec d → ℝ := fun i x => (1 - ζ x) * fderiv ℝ gt x (basisVec i) with hT4
  set T5 : Fin d → Vec d → ℝ := fun i x =>
    (l2a_moll d h η ũ.toFun x - gt x) * lipGradient ζ x i with hT5
  have hEmem : ∀ {f : Vec d → ℝ}, MemLp f 2 (volume.restrict W) → Continuous (l2a_moll d h η f) →
      MemLp (Eh f) 2 (volume.restrict W) := fun {f} hf hm =>
    (l2a_memL2_of_continuous hWm hVb (hζc.mul hm)).sub hf
  have hT4mem : ∀ i, MemLp (T4 i) 2 (volume.restrict W) := fun i =>
    l2a_memL2_of_continuous hWm hVb
      ((continuous_const.sub hζc).mul (hdgt.clm_apply continuous_const))
  have hT4lay : ∀ i, ∀ x ∈ W, T4 i x ≠ 0 → x ∈ l2b_layerB W r := fun i x hx hne =>
    l2b_layerB_cover hr x hx (fun h1 => hne (by
      have h1' : ζ x = 1 := h1
      simp [hT4, h1']))
  have hT4b : ∀ i, ∀ x ∈ W, |T4 i x| ≤ G := fun i x hx => by
    simp only [hT4]
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hζ1 x))]
    calc (1 - ζ x) * |fderiv ℝ gt x (basisVec i)| ≤ 1 * G := by
          refine mul_le_mul (by linarith only [hζ0 x]) ((linf_weak_abs_fderiv gt x i).trans (hG x hx))
            (abs_nonneg _) zero_le_one
      _ = G := one_mul G
  have hT5lay : ∀ i, ∀ x ∈ W, T5 i x ≠ 0 → x ∈ l2b_layerB W r := fun i x hx hne => by
    have hz : lipGradient ζ x ≠ 0 := fun h0 => hne (by simp [hT5, h0])
    refine ⟨hx, ?_⟩
    by_contra hc
    exact hz (l2a_lipGradient_cutoff_eq_zero W hr (Or.inr (not_le.1 hc)))
  have hT5b : ∀ i, ∀ x ∈ W, |T5 i x| ≤ B2 * (1 / r) := fun i x hx => by
    by_cases hz : lipGradient ζ x = 0
    · have : T5 i x = 0 := by simp [hT5, hz]
      rw [this, abs_zero]; positivity
    · simp only [hT5]
      rw [abs_mul]
      exact mul_le_mul (hB2' x hx hz) (l2a_lipGradient_cutoff_abs_le W hr x i) (abs_nonneg _) hB2
  have hT5mem : ∀ i, MemLp (T5 i) 2 (volume.restrict W) := fun i => by
    refine MemLp.of_bound ?_ (B2 * (1 / r)) ?_
    · exact ((hmU.sub hgtc).measurable.mul
        ((measurable_pi_apply i).comp (l2b_lipGradient_measurable ζ))).aestronglyMeasurable
    · refine (ae_restrict_iff' hWm).2 (Filter.Eventually.of_forall fun x hx => ?_)
      rw [Real.norm_eq_abs]
      exact hT5b i x hx
  have hhr' : h ≤ r := by linarith only [hhr, hr]
  have hdh : (d : ℝ) * h ≤ d * r := mul_le_mul_of_nonneg_left hhr' hd.le
  have hKbr : Kb * r = 2 * ((d : ℝ) + K1 + K2 + c + 1) * r := by rw [hKb]
  have hKb0 : 0 ≤ Kb := by linarith only [hKb1]
  have hcoef : (d : ℝ) * h + K1 * r ≤ Kb * r := by
    nlinarith only [hdh, mul_nonneg hK2 hr.le, mul_nonneg hc.le hr.le, hr, hKbr,
      mul_nonneg hd.le hr.le, mul_nonneg hK1 hr.le]
  have hcoef2 : (d : ℝ) * h + K1 * r ≤ (Kb / 2) * r := by
    nlinarith only [hdh, mul_nonneg hK2 hr.le, mul_nonneg hc.le hr.le, hr, hKbr,
      mul_nonneg hd.le hr.le, mul_nonneg hK1 hr.le]
  have hcoef0 : 0 ≤ (d : ℝ) * h + K1 * r := by positivity
  have hr5 : K2 * r * (B2 * (1 / r)) = K2 * B2 :=
    calc K2 * r * (B2 * (1 / r)) = K2 * B2 * (r * (1 / r)) := by ring
      _ = K2 * B2 := by rw [mul_one_div_cancel hr.ne', mul_one]
  -- the gradient
  have hcomp1 : ∀ i : Fin d, wMinusOneBar W 2 (fun x => (v.grad x - w.grad x) i) ≤
      ENNReal.ofReal (Kb * (r * (Ev + G) + B2)) := by
    intro i
    have hE := E1 hU n hr h3r hn hW0 hη.continuous hηA hη0 hη1 hηs (hGmem i) hEv0 (hGlp i)
    have hl4 := LB hU hr h3r hW0 (hT4mem i) (hT4lay i) hG0 (hT4b i)
    have hl5 := LB hU hr h3r hW0 (hT5mem i) (hT5lay i) (mul_nonneg hB2 hrinv.le) (hT5b i)
    have hcongr : wMinusOneBar W 2 (fun x => (v.grad x - w.grad x) i) =
        wMinusOneBar W 2 (fun x => -(Eh (Gf i) x) + -(T4 i x) + -(T5 i x)) := by
      refine linf_weak_wm_congr hWm 2 (fun x hx => ?_)
      have e1 := linf_weak_wgrad hWo hVb hr h3 hη hηs ũ hgt hbd x i
      have e2 := linf_weak_loc hWo hVb hr h3 hhr hηs v i x
      have e3 := hGval i x hx
      simp only [Pi.sub_apply, hEh, hT4, hT5]
      rw [e1, e2, e3]
      ring
    rw [hcongr]
    have m1 : MemLp (fun x => -(Eh (Gf i) x)) 2 (volume.restrict W) :=
      (hEmem (hGmem i) (hmG i)).neg
    have m4 : MemLp (fun x => -(T4 i x)) 2 (volume.restrict W) := (hT4mem i).neg
    have m5 : MemLp (fun x => -(T5 i x)) 2 (volume.restrict W) := (hT5mem i).neg
    refine (linf_weak_wm_add3 W m1 m4 m5).trans ?_
    rw [linf_weak_wm_neg W 2 (Eh (Gf i)), linf_weak_wm_neg W 2 (T4 i),
      linf_weak_wm_neg W 2 (T5 i)]
    refine (add_le_add (add_le_add hE hl4) hl5).trans ?_
    rw [← ENNReal.ofReal_add (mul_nonneg hcoef0 hEv0) (mul_nonneg (mul_nonneg hK2 hr.le) hG0),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hcoef0 hEv0) (mul_nonneg (mul_nonneg hK2 hr.le) hG0))
        (mul_nonneg (mul_nonneg hK2 hr.le) (mul_nonneg hB2 hrinv.le))]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hr5]
    nlinarith only [mul_le_mul_of_nonneg_right hcoef hEv0, mul_nonneg hr.le hEv0, mul_nonneg hr.le hG0,
      mul_nonneg hK2 hr.le, mul_nonneg hK2 hB2, hKb, hB2, hG0, hK1, hK2, hc, hd, mul_nonneg hr.le hB2,
      mul_nonneg (mul_nonneg hK2 hr.le) hG0, mul_nonneg hc.le hB2, hKb1,
      mul_le_mul_of_nonneg_right (show K2 ≤ Kb by linarith only [hKb, hd, hK1, hc, hK2]) (mul_nonneg hr.le hG0),
      mul_le_mul_of_nonneg_right (show K2 ≤ Kb by linarith only [hKb, hd, hK1, hc, hK2]) hB2]
  -- the flux
  have hss : s⁻¹ * s = 1 := inv_mul_cancel₀ hs.ne'
  have hcomp2 : ∀ i : Fin d, wMinusOneBar W 2 (fun x => (s⁻¹ • matVecMul (a x) (v.grad x) - w.grad x) i) ≤
      ENNReal.ofReal (Kb * (L * (s⁻¹ * B1) + r * (s⁻¹ * Ea + Ev + G) + B2)) := by
    intro i
    have hEP := E1 hU n hr h3r hn hW0 hη.continuous hηA hη0 hη1 hηs (hPmem i)
      (add_nonneg hEa0 (mul_nonneg hs.le hEv0)) (hPlp i)
    have hEG := E1 hU n hr h3r hn hW0 hη.continuous hηA hη0 hη1 hηs (hGmem i) hEv0 (hGlp i)
    have hl4 := LB hU hr h3r hW0 (hT4mem i) (hT4lay i) hG0 (hT4b i)
    have hl5 := LB hU hr h3r hW0 (hT5mem i) (hT5lay i) (mul_nonneg hB2 hrinv.le) (hT5b i)
    have hA2mem : MemLp (fun x => s⁻¹ * (ζ x * l2a_moll d h η (Pf i) x)) 2 (volume.restrict W) :=
      l2a_memL2_of_continuous hWm hVb (continuous_const.mul (hζc.mul (hmP i)))
    have hA2b : ∀ x ∈ W, |s⁻¹ * (ζ x * l2a_moll d h η (Pf i) x)| ≤ s⁻¹ * B1 := fun x hx => by
      by_cases hz : ζ x = 0
      · rw [hz, zero_mul, mul_zero, abs_zero]; positivity
      · rw [abs_mul, abs_of_pos (inv_pos.2 hs), abs_mul, abs_of_nonneg (hζ0 x)]
        refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hs).le
        have hm : |l2a_moll d h η (Pf i) x| ≤ B1 := by
          have := (norm_le_pi_norm (a16_mollify d h η
            (fun y => l2d_flux a W v y - s • l2d_gradc W v y) x) i).trans (hB1' x hx hz)
          rw [Real.norm_eq_abs] at this
          exact this
        calc ζ x * |l2a_moll d h η (Pf i) x| ≤ 1 * B1 :=
              mul_le_mul (hζ1 x) hm (abs_nonneg _) zero_le_one
          _ = B1 := one_mul B1
    have hl2 := SU hWo z hL hsub hW0 hA2mem hA2b
    have hA1 : wMinusOneBar W 2 (fun x => (-s⁻¹) * Eh (Pf i) x) ≤
        ENNReal.ofReal (s⁻¹ * ((d * h + K1 * r) * (Ea + s * Ev))) := by
      rw [s12_wMinusOneBar_const_mul, abs_neg, abs_of_pos (inv_pos.2 hs),
        ENNReal.ofReal_mul (inv_pos.2 hs).le]
      exact mul_le_mul' le_rfl hEP
    have hcongr : wMinusOneBar W 2 (fun x => (s⁻¹ • matVecMul (a x) (v.grad x) - w.grad x) i) =
        wMinusOneBar W 2 (fun x => (-s⁻¹) * Eh (Pf i) x + s⁻¹ * (ζ x * l2a_moll d h η (Pf i) x) +
          -(Eh (Gf i) x) + -(T4 i x) + -(T5 i x)) := by
      refine linf_weak_wm_congr hWm 2 (fun x hx => ?_)
      have e1 := linf_weak_wgrad hWo hVb hr h3 hη hηs ũ hgt hbd x i
      have e2 := linf_weak_loc hWo hVb hr h3 hhr hηs v i x
      have e3 := hGval i x hx
      have e4 := hPval i x hx
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hEh, hT4, hT5]
      rw [e1, e2, e3, e4]
      linear_combination (v.grad x i) * hss
    rw [hcongr]
    have m1 : MemLp (fun x => (-s⁻¹) * Eh (Pf i) x) 2 (volume.restrict W) :=
      (hEmem (hPmem i) (hmP i)).const_mul _
    have m3 : MemLp (fun x => -(Eh (Gf i) x)) 2 (volume.restrict W) :=
      (hEmem (hGmem i) (hmG i)).neg
    have m4 : MemLp (fun x => -(T4 i x)) 2 (volume.restrict W) := (hT4mem i).neg
    have m5 : MemLp (fun x => -(T5 i x)) 2 (volume.restrict W) := (hT5mem i).neg
    refine (linf_weak_wm_add5 W m1 hA2mem m3 m4 m5).trans ?_
    rw [linf_weak_wm_neg W 2 (Eh (Gf i)), linf_weak_wm_neg W 2 (T4 i),
      linf_weak_wm_neg W 2 (T5 i)]
    refine (add_le_add (add_le_add (add_le_add (add_le_add hA1 hl2) hEG) hl4) hl5).trans ?_
    have hq : 0 ≤ s⁻¹ := (inv_pos.2 hs).le
    have n1 : 0 ≤ s⁻¹ * ((d * h + K1 * r) * (Ea + s * Ev)) :=
      mul_nonneg hq (mul_nonneg hcoef0 (add_nonneg hEa0 (mul_nonneg hs.le hEv0)))
    have n2 : 0 ≤ c * L * (s⁻¹ * B1) := mul_nonneg (mul_nonneg hc.le hL.le) (mul_nonneg hq hB1)
    have n3 : 0 ≤ (d * h + K1 * r) * Ev := mul_nonneg hcoef0 hEv0
    have n4 : 0 ≤ K2 * r * G := mul_nonneg (mul_nonneg hK2 hr.le) hG0
    have n5 : 0 ≤ K2 * r * (B2 * (1 / r)) :=
      mul_nonneg (mul_nonneg hK2 hr.le) (mul_nonneg hB2 hrinv.le)
    rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) n3,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg n1 n2) n3) n4,
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg n1 n2) n3) n4) n5]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : s⁻¹ * ((d * h + K1 * r) * (Ea + s * Ev)) =
        (d * h + K1 * r) * (s⁻¹ * Ea + Ev) :=
      calc s⁻¹ * ((d * h + K1 * r) * (Ea + s * Ev))
          = (d * h + K1 * r) * (s⁻¹ * Ea + (s⁻¹ * s) * Ev) := by ring
        _ = (d * h + K1 * r) * (s⁻¹ * Ea + Ev) := by rw [hss, one_mul]
    have hqE : 0 ≤ s⁻¹ * Ea + Ev := add_nonneg (mul_nonneg hq hEa0) hEv0
    have hK2Kb : K2 ≤ Kb := by linarith only [hKb, hd, hK1, hc, hK2]
    have hcKb : c ≤ Kb := by linarith only [hKb, hd, hK1, hc, hK2]
    rw [e1, hr5]
    nlinarith only [mul_le_mul_of_nonneg_right hcoef2 hqE, mul_le_mul_of_nonneg_right hcoef2 hEv0,
      mul_le_mul_of_nonneg_right hcKb (mul_nonneg hL.le (mul_nonneg hq hB1)),
      mul_le_mul_of_nonneg_right hK2Kb (mul_nonneg hr.le hG0),
      mul_le_mul_of_nonneg_right hK2Kb hB2, mul_nonneg hr.le hEv0, mul_nonneg hr.le hqE,
      mul_nonneg hr.le hG0, hKb, mul_nonneg hr.le hEa0, mul_nonneg hq hEa0,
      mul_nonneg hr.le (mul_nonneg hq hEa0),
      mul_nonneg (mul_nonneg (mul_nonneg hKb0 hr.le) hq) hEa0]
  refine ⟨?_, ?_⟩
  · show ∑ i : Fin d, wMinusOneBar W 2 (fun x => (v.grad x - w.grad x) i) ≤ _
    exact (linf_weak_sum hcomp1).trans (le_of_eq (by congr 1; ring))
  · show ∑ i : Fin d, wMinusOneBar W 2 (fun x => (s⁻¹ • matVecMul (a x) (v.grad x) - w.grad x) i) ≤ _
    exact (linf_weak_sum hcomp2).trans (le_of_eq (by congr 1; ring))

/-- Satisfiability of `linf_weak`: zero data and the identity field on a dilate of the unit ball,
with the standard bump and all sup bounds equal to zero, so that all the hypotheses hold. -/
example : True := by
  obtain ⟨W, r₀, M₁, M₂, D, hU, h3r, hW0⟩ := l2d_witness_domain4 (d := 2)
  obtain ⟨C, hC, H⟩ := linf_weak (d := 2) M₁
  have hWb := l2c_bounded hU
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec 2)).1 hWb
  have hWL : W ⊆ axisCube (fun _ => -(|ρ| + 1)) (2 * (|ρ| + 1)) := by
    intro x hx j _
    have h1 := hρ hx
    rw [mem_closedBall_zero_iff] at h1
    have h2 : |x j| ≤ ‖x‖ := by
      rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x j
    have h3 := abs_le.1 h2
    have h4 := le_abs_self ρ
    simp only [Set.mem_Ioo]
    constructor <;> linarith only [h1, h3.1, h3.2, h4, abs_nonneg ρ]
  obtain ⟨B, hB⟩ := (li1_bump_contDiff 2).continuous.bounded_above_of_compact_support
    (li1_bump_compact 2)
  obtain ⟨hη, hη0, hη1, hηs⟩ := l2c_mollifier_witness 2
  have hext : ∀ y, (l2c_ext hU.1 hWb (show (0 : ℝ) < 4 by norm_num)
      (0 : H1Function W)).toFun y = 0 := by
    intro y
    by_cases hy : y ∈ W
    · simp [l2c_ext, H10Function.zeroExtension_apply_of_mem _ hy]
    · simp [l2c_ext, H10Function.zeroExtension_apply_of_not_mem _ hy]
  have _ := H hU (n := 0) (r := 4) (by norm_num) h3r (by norm_num) (by norm_num) hW0
    (fun _ => -(|ρ| + 1)) (L := 2 * (|ρ| + 1)) (by positivity) hWL
    (η := li1_bump 2) (Bη := B) hη (fun w => by simpa [Real.norm_eq_abs] using hB w) hη0 hη1 hηs
    (fun _ => (1 : Mat 2)) (s := 1) one_pos (0 : H1Function W) (gt := fun _ => 0) contDiff_const
    ((MeasureTheory.memLp_pi_iff).2 fun i => by simp [matVecMul])
    ⟨0, by funext x; simp; rfl⟩
    (B1 := 0) (B2 := 0) (G := 0) (Ev := 0) (Ea := 0) le_rfl le_rfl le_rfl le_rfl le_rfl
    (fun x _ => by simp)
    (by simp [lpBar, eucNorm, vecNormSq, vecDot])
    (by simp [lpBar, eucNorm, vecNormSq, vecDot, matVecMul])
    (fun x _ _ => by
      simp [l2d_flux, l2d_gradc, l2d_matVecMul_zero, Set.indicator_zero', l2d_mollify_zero])
    (fun x _ _ => by simp [hext, l2a_moll])
  trivial

end SuperdiffusionCLT.Section7
