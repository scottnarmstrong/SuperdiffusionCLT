/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.LayerDual
public import SuperdiffusionCLT.Section7.Root.InteriorApproxE
public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyE

/-!
# The comparison function against the homogenized solution: sup norm and `L^{2d}` gradient

The function `φ = w - v̄` solves a constant coefficient Dirichlet problem whose data are the
three flux terms and the two scalar terms of the mollified comparison; Calderon-Zygmund at
`p = 2d` and Morrey give the two norms of the conclusion from sup bounds of the mollified fluxes.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A function bounded almost everywhere has normalized norm at most the bound. -/
theorem linf_lpBar_le_of_ae_bound {V : Set (Vec d)} (ht : volume V ≠ ⊤) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict V)) {C : ℝ}
    (hC : ∀ᵐ x ∂volume.restrict V, |f x| ≤ C) (q : ℝ≥0∞) :
    lpBar V q f ≤ ENNReal.ofReal C := by
  unfold lpBar
  by_cases h0 : volume V = 0
  · rw [Measure.restrict_eq_zero.2 h0, smul_zero, eLpNorm_measure_zero]; exact zero_le
  have hp : IsProbabilityMeasure (((volume V)⁻¹) • volume.restrict V) := by
    refine ⟨?_⟩
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel h0 ht
  have := eLpNorm_le_of_ae_bound (p := q) (hf.smul_measure ((volume V)⁻¹))
    (C := C) (MeasureTheory.Measure.ae_smul_measure (by
      filter_upwards [hC] with x hx
      rwa [Real.norm_eq_abs]) _)
  rwa [measure_univ, ENNReal.one_rpow, one_mul] at this

/-- A bounded vector field supported in a measurable subset `A` of `W` has normalized `L^p(W)`
norm at most `B (|A| / |W|)^{1/p}`. -/
theorem linf_lpBar_supp_le {W A : Set (Vec d)} (hWm : MeasurableSet W) (hAm : MeasurableSet A)
    (hAW : A ⊆ W) {G : Vec d → Vec d} (hGm : AEStronglyMeasurable G (volume.restrict W)) {B : ℝ}
    (hGB : ∀ x ∈ W, ‖G x‖ ≤ B) (hG0 : ∀ x ∈ W, x ∉ A → G x = 0) {p : ℝ} (hp : 0 < p) :
    lpBar W (ENNReal.ofReal p) G ≤ ENNReal.ofReal B * (volume A / volume W) ^ (1 / p) := by
  have hc : lpBar W (ENNReal.ofReal p) G = lpBar W (ENNReal.ofReal p) (A.indicator G) :=
    l2d_lpBar_congr hWm (fun x hx => by
      by_cases hxA : x ∈ A
      · simp [Set.indicator_of_mem hxA]
      · simp [Set.indicator_of_notMem hxA, hG0 x hx hxA]) _
  rw [hc]
  exact linf_lpBar_indicator_le hAm hAW hGm (fun x hx => hGB x (hAW hx)) hp

/-- Elementary combination of the four error terms. -/
theorem linf_comb (a b c e : ℝ≥0∞) {k₁ k₂ : ℝ} (h₁ : 0 ≤ k₁) (h₂ : 0 ≤ k₂) :
    a + b + ENNReal.ofReal k₁ * c + ENNReal.ofReal k₂ * e ≤
      ENNReal.ofReal (1 + k₁ + k₂) * (a + b + c + e) := by
  have hS : ENNReal.ofReal (1 + k₁ + k₂) =
      1 + ENNReal.ofReal k₁ + ENNReal.ofReal k₂ := by
    rw [ENNReal.ofReal_add (by linarith only [h₁]) h₂, ENNReal.ofReal_add (by norm_num) h₁,
      ENNReal.ofReal_one]
  rw [hS]
  set K₁ := ENNReal.ofReal k₁
  set K₂ := ENNReal.ofReal k₂
  have e1 : a ≤ (1 + K₁ + K₂) * a := le_mul_of_one_le_left zero_le (by
    calc (1 : ℝ≥0∞) ≤ 1 + K₁ := le_self_add
      _ ≤ 1 + K₁ + K₂ := le_self_add)
  have e2 : b ≤ (1 + K₁ + K₂) * b := le_mul_of_one_le_left zero_le (by
    calc (1 : ℝ≥0∞) ≤ 1 + K₁ := le_self_add
      _ ≤ 1 + K₁ + K₂ := le_self_add)
  have e3 : K₁ * c ≤ (1 + K₁ + K₂) * c :=
    mul_le_mul' (by
      calc K₁ ≤ 1 + K₁ := le_add_self
        _ ≤ 1 + K₁ + K₂ := le_self_add) le_rfl
  have e4 : K₂ * e ≤ (1 + K₁ + K₂) * e := mul_le_mul' le_add_self le_rfl
  calc a + b + K₁ * c + K₂ * e ≤ (1 + K₁ + K₂) * a + (1 + K₁ + K₂) * b +
        (1 + K₁ + K₂) * c + (1 + K₁ + K₂) * e :=
        add_le_add (add_le_add (add_le_add e1 e2) e3) e4
    _ = _ := by ring


/-- The three flux terms of the equation for `w - v̄`, in `L^{2d}`, from sup bounds: the interior
term by `B1`, the datum term by `G` on the layer, the boundary term by `B2 / r` on the layer. -/
theorem linf_Fv_bound [NeZero d] {r₀ M₁ M₂ D : ℝ} {W : Set (Vec d)}
    (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {n : ℕ} {r : ℝ} (hr : 0 < r)
    (hhr : (3 : ℝ) ^ n ≤ r / 4) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ϑ : ℝ≥0∞}
    (hϑ : (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / (2 * (d : ℝ))) ≤ ϑ)
    (a : CoeffField d) {s : ℝ} (hs : 0 < s) (v : H1Function W) {gt : Vec d → ℝ}
    (hgt : ContDiff ℝ 1 gt)
    (hFi : ∀ i, LocallyIntegrable (fun x => l2d_flux a W v x i) volume)
    {B1 B2 G : ℝ} (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hG : 0 ≤ G)
    (hgtG : ∀ x ∈ W, ‖fderiv ℝ gt x‖ ≤ G)
    (hBm1 : ∀ x ∈ W, l2a_cutoff W r x ≠ 0 →
      ‖a16_mollify d ((3 : ℝ) ^ n) η (fun y => l2d_flux a W v y - s • l2d_gradc W v y) x‖ ≤ B1)
    (hBm2 : ∀ x ∈ W, lipGradient (l2a_cutoff W r) x ≠ 0 →
      |l2a_moll d ((3 : ℝ) ^ n) η (l2c_ext hU.1 (l2c_bounded hU) hr v).toFun x - gt x| ≤ B2) :
    lpBar W (ENNReal.ofReal (2 * d))
        (l2d_Fv W r ((3 : ℝ) ^ n) η s (l2c_ext hU.1 (l2c_bounded hU) hr v)
          (li1_h1 hU.1 (p14g_isBoundedDomain hU) hgt) (l2d_flux a W v)) ≤
      ENNReal.ofReal (s⁻¹ * B1) + ϑ * ENNReal.ofReal (B2 / r + G) := by
  have hWb := l2c_bounded hU
  have hWm : MeasurableSet W := hU.1.measurableSet
  have hWT : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  set h : ℝ := (3 : ℝ) ^ n with hhdef
  set ũ := l2c_ext hU.1 hWb hr v with hũ
  set g := li1_h1 hU.1 (p14g_isBoundedDomain hU) hgt with hg
  set ζ := l2a_cutoff W r with hζ
  have hζc : Continuous ζ := l2a_cutoff_continuous W hr
  have hζ0 := l2a_cutoff_nonneg W r
  have hζ1 := l2a_cutoff_le_one W r
  have hdpos : 0 < (2 * (d : ℝ)) := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * d) := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    linarith only [this]
  -- continuity of the mollified fluxes
  have hGc : ∀ i, Continuous fun x =>
      a16_mollify d h η (fun y => l2d_flux a W v y - s • ũ.grad y) x i := by
    intro i
    have hl : LocallyIntegrable (fun y => l2d_flux a W v y i - s * ũ.grad y i) volume :=
      (hFi i).sub ((l2a_locInt_of_memL2_univ (ũ.gradMemL2 i)).smul s)
    exact (l2a_moll_contDiff h3 hη hηs hl).continuous
  have hGcv : Continuous fun x => a16_mollify d h η (fun y => l2d_flux a W v y - s • ũ.grad y) x :=
    continuous_pi hGc
  have hmu : Continuous (l2a_moll d h η ũ.toFun) :=
    (l2a_moll_contDiff h3 hη hηs (l2a_locInt_of_memL2_univ ũ.memL2)).continuous
  have hlipm : Measurable (lipGradient ζ) := l2b_lipGradient_measurable ζ
  have hLm : MeasurableSet (boundaryLayer W (3 * r)) :=
    (layerPoincare_isOpen_boundaryLayer hU.1 _).measurableSet
  have hLW : boundaryLayer W (3 * r) ⊆ W := fun x hx => hx.1
  have hgrad : ∀ x, ‖g.grad x‖ ≤ ‖fderiv ℝ gt x‖ := fun x => by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have h2 : ‖basisVec (d := d) i‖ = 1 := by simp [basisVec, Pi.norm_single]
    have := (fderiv ℝ gt x).le_opNorm (basisVec i)
    rw [h2, mul_one] at this
    exact this
  have hϑ' : ∀ B : ℝ, ENNReal.ofReal B * (volume (boundaryLayer W (3 * r)) / volume W) ^
      (1 / (2 * (d : ℝ))) ≤ ENNReal.ofReal B * ϑ := fun B => mul_le_mul' le_rfl hϑ
  have hFv : l2d_Fv W r h η s ũ g (l2d_flux a W v) = fun x =>
      (((-s⁻¹) * ζ x) • a16_mollify d h η (fun y => l2d_flux a W v y - s • ũ.grad y) x +
        (1 - ζ x) • g.grad x) + (l2a_moll d h η ũ.toFun x - g.toFun x) • lipGradient ζ x := rfl
  -- term one
  have hT1m : AEStronglyMeasurable (fun x => ((-s⁻¹) * ζ x) •
      a16_mollify d h η (fun y => l2d_flux a W v y - s • ũ.grad y) x) (volume.restrict W) :=
    ((continuous_const.mul hζc).smul hGcv).aestronglyMeasurable
  have hT1 : lpBar W (ENNReal.ofReal (2 * d)) (fun x => ((-s⁻¹) * ζ x) •
      a16_mollify d h η (fun y => l2d_flux a W v y - s • ũ.grad y) x) ≤
        ENNReal.ofReal (s⁻¹ * B1) := by
    refine ia_lpBar_le_of_bound hWT hT1m (fun x hx => ?_) hWm _
    have hc := l2d_claimA hU.1 hWb hr h3 hhr hηs v (l2d_flux a W v) s x
    rw [← smul_smul, hc, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.2 hs)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hs.le)
    by_cases hz : ζ x = 0
    · rw [show l2a_cutoff W r x = 0 from hz, zero_smul, norm_zero]; exact hB1
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ0 x)]
      calc ζ x * ‖a16_mollify d h η (fun y => l2d_flux a W v y - s • l2d_gradc W v y) x‖
          ≤ 1 * B1 := mul_le_mul (hζ1 x) (hBm1 x hx hz) (norm_nonneg _) zero_le_one
        _ = B1 := one_mul _
  -- term two
  have hT2m : AEStronglyMeasurable (fun x => (1 - ζ x) • g.grad x) (volume.restrict W) :=
    ((continuous_const.sub hζc).aestronglyMeasurable).smul (l2c_aesm_grad g)
  have hT2 : lpBar W (ENNReal.ofReal (2 * d)) (fun x => (1 - ζ x) • g.grad x) ≤
      ENNReal.ofReal G * ϑ := by
    refine (linf_lpBar_supp_le hWm hLm hLW hT2m (B := G) (fun x hx => ?_) (fun x hx hxL => ?_)
      hdpos).trans (hϑ' G)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hζ1 x])]
      calc (1 - ζ x) * ‖g.grad x‖ ≤ 1 * G :=
          mul_le_mul (by linarith only [hζ0 x]) ((hgrad x).trans (hgtG x hx)) (norm_nonneg _)
            zero_le_one
        _ = G := one_mul _
    · have : ζ x = 1 := by
        by_contra hne
        have hlt : Metric.infDist x Wᶜ < 2 * r := by
          by_contra hge
          exact hne (l2a_cutoff_eq_one hr (not_lt.1 hge))
        exact hxL (l2b_layer_of_infDist hU.2.2.1 hx (by linarith only [hlt, hr]))
      simp [this]
  -- term three
  have hT3m : AEStronglyMeasurable (fun x => (l2a_moll d h η ũ.toFun x - g.toFun x) •
      lipGradient ζ x) (volume.restrict W) :=
    ((hmu.sub hgt.continuous).measurable.smul hlipm).aestronglyMeasurable
  have hT3 : lpBar W (ENNReal.ofReal (2 * d)) (fun x => (l2a_moll d h η ũ.toFun x - g.toFun x) •
      lipGradient ζ x) ≤ ENNReal.ofReal (B2 / r) * ϑ := by
    refine (linf_lpBar_supp_le hWm hLm hLW hT3m (B := B2 / r) (fun x hx => ?_) (fun x hx hxL => ?_)
      hdpos).trans (hϑ' _)
    · by_cases hz : lipGradient ζ x = 0
      · rw [hz, smul_zero, norm_zero]; positivity
      · rw [norm_smul, Real.norm_eq_abs, div_eq_mul_one_div]
        exact mul_le_mul (hBm2 x hx hz) (l2b_lipGradient_norm_le W hr x) (norm_nonneg _) hB2
    · by_contra hz
      have hAL : x ∈ l2b_layerA W r := by
        by_contra hc
        exact hz (by rw [l2b_lipGradient_zero_off hr x hc, smul_zero])
      exact hxL (l2b_layer_of_infDist hU.2.2.1 hx (by linarith only [hAL.2, hr]))
  rw [hFv]
  refine (l2d_lpBar_add_le hP1 _ _).trans ?_
  refine (add_le_add (l2d_lpBar_add_le hP1 _ _) le_rfl).trans ?_
  have hsum : ENNReal.ofReal G * ϑ + ENNReal.ofReal (B2 / r) * ϑ =
      ϑ * ENNReal.ofReal (B2 / r + G) := by
    rw [ENNReal.ofReal_add (by positivity) hG]; ring
  calc _ ≤ ENNReal.ofReal (s⁻¹ * B1) + ENNReal.ofReal G * ϑ + ENNReal.ofReal (B2 / r) * ϑ :=
        add_le_add (add_le_add hT1 hT2) hT3
    _ = _ := by rw [add_assoc, hsum]


/-- The two scalar terms of the equation for `w - v̄` in `W^{-1,2d}`: the mollification error by
the sup bound of `f`, the layer term by the sup bound `B5` of the mollified flux. -/
theorem linf_h_bound [NeZero d] (M₁ : ℝ) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ}
      (hU : IsUniformC11Domain W r₀ M₁ M₂ D) {n : ℕ} {r : ℝ} (hr : 0 < r),
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → 2 * (3 : ℝ) ^ n < r →
      (3 : ℝ) ^ n ≤ r / 4 → volume W ≠ 0 → ∀ {η : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) η →
      ∀ {Bη : ℝ}, (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) →
      ∀ {ϑ : ℝ≥0∞}, (volume (boundaryLayer W (3 * r)) / volume W) ^ (1 / (2 * (d : ℝ))) ≤ ϑ →
      ∀ {s : ℝ}, 0 < s → ∀ {fc : Vec d → ℝ}, AEStronglyMeasurable fc (volume.restrict W) →
      ∀ {F : ℝ}, 0 ≤ F → (∀ᵐ x ∂volume.restrict W, |fc x| ≤ F) → IntegrableOn fc W volume →
      (∀ φ : H10Function W, IntegrableOn (fun x => fc x * φ.toH1Function.toFun x) W volume) →
      ∀ {F' : Vec d → Vec d}, (∀ i, LocallyIntegrable (fun x => F' x i) volume) →
      (∀ ψ : H10Function W, IntegrableOn
        (fun x => l2d_h1 W r ((3 : ℝ) ^ n) η s fc x * ψ.toH1Function.toFun x) W) →
      (∀ ψ : H10Function W, IntegrableOn
        (fun x => l2d_h2 W r ((3 : ℝ) ^ n) η s F' x * ψ.toH1Function.toFun x) W) →
      ∀ {B5 : ℝ}, 0 ≤ B5 →
      (∀ x ∈ W, lipGradient (l2a_cutoff W r) x ≠ 0 →
        ‖a16_mollify d ((3 : ℝ) ^ n) η F' x‖ ≤ B5) →
      wMinusOneBar W (ENNReal.ofReal (2 * d))
          (fun x => l2d_h1 W r ((3 : ℝ) ^ n) η s fc x + l2d_h2 W r ((3 : ℝ) ^ n) η s F' x) ≤
        ENNReal.ofReal K₁ * ENNReal.ofReal (s⁻¹ * r * F) +
          ENNReal.ofReal K₂ * (ϑ * ENNReal.ofReal (s⁻¹ * B5)) := by
  obtain ⟨CP₁, hCP₁, H1⟩ := l2d_E1_cutoff (d := d) M₁
  obtain ⟨CP, hCP, HL⟩ := linf_layer_dual (d := d) M₁
  refine ⟨d / 4 + CP₁, d * CP, by positivity, by positivity, ?_⟩
  intro r₀ W M₂ D hU n r hr h3r hn hhr hW0 η hη Bη hηB hη0 hη1 hηs ϑ hϑ s hs fc hfcm F hF hfcF hfi hfφ
    F' hFc hI1 hI2 B5 hB5 hBm5
  have hWb := l2c_bounded hU
  have hWm : MeasurableSet W := hU.1.measurableSet
  have hWT : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hp1 : 1 < 2 * (d : ℝ) := by linarith only [hdR]
  have hpq : (2 * (d : ℝ)).HolderConjugate (2 * (d : ℝ)).conjExponent :=
    Real.HolderConjugate.conjExponent hp1
  have hsum := s12_wMinusOneBar_add_le W (ENNReal.ofReal (2 * d)) hI1 hI2
  -- the mollification error
  have e1 : wMinusOneBar W (ENNReal.ofReal (2 * d))
      (fun x => l2d_h1 W r ((3 : ℝ) ^ n) η s fc x) ≤
        ENNReal.ofReal (d / 4 + CP₁) * ENNReal.ofReal (s⁻¹ * r * F) := by
    have h0 := s12_wMinusOneBar_const_mul W (ENNReal.ofReal (2 * d)) s⁻¹
      (fun x => l2a_cutoff W r x * l2a_moll d ((3 : ℝ) ^ n) η fc x - fc x)
    rw [abs_of_pos (inv_pos.2 hs)] at h0
    show wMinusOneBar W _ (fun x => s⁻¹ * _) ≤ _
    rw [h0]
    have hE := H1 hU n hr h3r hn hW0 hWT hη.continuous hηB hη0 hη1 hηs hpq hfi hfφ
    have hlp : lpBar W (ENNReal.ofReal (2 * d)) fc ≤ ENNReal.ofReal F :=
      linf_lpBar_le_of_ae_bound hWT hfcm hfcF _
    have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    refine (mul_le_mul' le_rfl (hE.trans (mul_le_mul' le_rfl hlp))).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (d : ℝ) * 3 ^ n + CP₁ * r ≤ (d / 4 + CP₁) * r := by
      have := mul_le_mul_of_nonneg_left hhr hdn
      linarith only [this]
    have h2 := mul_le_mul_of_nonneg_right h1 hF
    have h3' := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hs.le)
    calc s⁻¹ * (((d : ℝ) * 3 ^ n + CP₁ * r) * F) ≤ s⁻¹ * ((d / 4 + CP₁) * r * F) := h3'
      _ = _ := by ring
  have e2 : wMinusOneBar W (ENNReal.ofReal (2 * d))
      (fun x => l2d_h2 W r ((3 : ℝ) ^ n) η s F' x) ≤
        ENNReal.ofReal (d * CP) * (ϑ * ENNReal.ofReal (s⁻¹ * B5)) := by
    have h0 := s12_wMinusOneBar_const_mul W (ENNReal.ofReal (2 * d)) (-s⁻¹)
      (fun x => vecDot (lipGradient (l2a_cutoff W r) x) (a16_mollify d ((3 : ℝ) ^ n) η F' x))
    rw [abs_neg, abs_of_pos (inv_pos.2 hs)] at h0
    show wMinusOneBar W _ (fun x => (-s⁻¹) * _) ≤ _
    rw [h0]
    have hGc : Continuous fun x => a16_mollify d ((3 : ℝ) ^ n) η F' x :=
      continuous_pi fun i => (l2a_moll_contDiff h3 hη hηs (hFc i)).continuous
    have hL := HL hU hr h3r hW0 hp1 hB5 hGc.aestronglyMeasurable hBm5
    have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    refine (mul_le_mul' le_rfl (hL.trans (mul_le_mul' le_rfl hϑ))).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (d : ℝ) * CP),
      ENNReal.ofReal_mul (inv_nonneg.2 hs.le)]
    ring
  exact hsum.trans (add_le_add e1 e2)

end SuperdiffusionCLT.Section7
