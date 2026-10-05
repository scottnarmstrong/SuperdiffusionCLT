/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2InteriorC
public import SuperdiffusionCLT.Section7.Prereq.MollifiedFluxC
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerPoincareB
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryLayer
public import SuperdiffusionCLT.Section7.Analytic.Geometry.AtlasTransform

/-!
# The mollification error against `f` in `W̲^{-1,p}`

Display `e.Dir.new.f.mollification`: the
duality computation `∫ ψ (f - ζ η ∗ f) = ∫ f (ψ - η̌ ∗ (ζ ψ))`, the splitting
`ψ - η̌ ∗ (ζ ψ) = (ψ - η̌ ∗ ψ) + η̌ ∗ ((1 - ζ) ψ)`, the mollification estimate and the `L^q`
contraction on `ℝ^d` (the test function zero-extended), and the layer Poincaré inequality.

* `Section7.l2b_E1_duality`: the estimate on `ℝ^d` for a measurable `ψ` with weak gradient.
* `Section7.l2b_rep`: measurable representatives of the zero extension of an `H¹₀` function.
* `Section7.l2b_pairing`: the Fubini exchange with integrability.
* `Section7.l2b_E1_identity`: `∫_W (ζ η ∗ f - f) ψ = ∫ f1 (η̌ ∗ (ζ ψ) - ψ)`.
* `Section7.l2b_E1_core`: `‖ζ η ∗ f - f‖_{W̲^{-1,p}(W)} ≤ (d h + CP r) ‖f‖_{L̲^p(W)}`.
* `Section7.l2b_E3_cutoff`, `Section7.l2b_E2_cutoff`, `Section7.l2b_E1_cutoff`: the three interior
  error terms for the margin cutoff `l2a_cutoff W r` of a uniformly `C^{1,1}` domain.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- Hölder for two real functions, in `eLpNorm` form. -/
theorem l2b_holder_enorm {μ : Measure (Vec d)} {p q : ℝ} (hpq : p.HolderConjugate q)
    {F G : Vec d → ℝ} (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    ∫⁻ x, ‖F x * G x‖ₑ ∂μ ≤ eLpNorm F (ENNReal.ofReal p) μ * eLpNorm G (ENNReal.ofReal q) μ := by
  have hH : (ENNReal.ofReal p).HolderConjugate (ENNReal.ofReal q) := hpq.ennrealOfReal
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (μ := μ) (p := ENNReal.ofReal p)
    (q := ENNReal.ofReal q) (r := 1) (fun a b : ℝ => a * b) 1 (by fun_prop) hF hG
    (Filter.Eventually.of_forall fun x => by simp [enorm_mul])
  have e : eLpNorm (fun x => F x * G x) 1 μ = ∫⁻ x, ‖F x * G x‖ₑ ∂μ :=
    eLpNorm_one_eq_lintegral_enorm (hF.mul hG)
  rw [← e]
  simpa using h

/-- **The mollification error against `f`, duality form**: for `ψ` with weak
gradient `g` on `ℝ^d` and a cutoff `0 ≤ ζ ≤ 1`, with `η` the reflected profile,
`|∫ f1 (η ∗ (ζ ψ) - ψ)| ≤ ‖f1‖_{L^p} (√d h ‖g‖_{L^q} + ‖(1 - ζ) ψ‖_{L^q})`. -/
theorem l2b_E1_duality {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ζ : Vec d → ℝ} (hζm : Measurable ζ)
    (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1) {ψ : Vec d → ℝ} {g : Vec d → Vec d}
    (hψm : Measurable ψ) (hgm : ∀ i, Measurable fun x => g x i)
    (hψl : LocallyIntegrable ψ volume) (hgl : ∀ i, LocallyIntegrable (fun x => g x i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (Set.univ : Set (Vec d)) →
        ∫ x, ψ x * fderiv ℝ φ x (basisVec i) = -∫ x, g x i * φ x)
    {f1 : Vec d → ℝ} (hf1 : AEStronglyMeasurable f1 volume) {p q : ℝ} (hpq : p.HolderConjugate q)
    (hq : 1 ≤ q) :
    ENNReal.ofReal |∫ y, f1 y * ((∫ x, a16_kernel d h η (y - x) * (ζ x * ψ x)) - ψ y)| ≤
      eLpNorm f1 (ENNReal.ofReal p) volume *
        (ENNReal.ofReal (Real.sqrt d * h) *
            eLpNorm (fun y => eucNorm (g y)) (ENNReal.ofReal q) volume +
          eLpNorm (fun x => (1 - ζ x) * ψ x) (ENNReal.ofReal q) volume) := by
  set a : Vec d → ℝ := fun y => ψ y - ∫ x, a16_kernel d h η (y - x) * ψ x with ha
  set b : Vec d → ℝ := fun y => ∫ x, a16_kernel d h η (y - x) * ((1 - ζ x) * ψ x) with hb
  have hψ1m : Measurable fun x => (1 - ζ x) * ψ x := (measurable_const.sub hζm).mul hψm
  have hψ1l : LocallyIntegrable (fun x => (1 - ζ x) * ψ x) volume := by
    refine hψl.mono hψ1m.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have h1 : |1 - ζ x| ≤ 1 := by rw [abs_le]; constructor <;> linarith only [hζ0 x, hζ1 x]
    calc |1 - ζ x| * |ψ x| ≤ 1 * |ψ x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |ψ x| := one_mul _
  have ham : Measurable a := hψm.sub (m1_measurable_conv hηc hψm)
  have hbm : Measurable b := m1_measurable_conv hηc hψ1m
  have hlin : ∀ y, (∫ x, a16_kernel d h η (y - x) * (ζ x * ψ x)) - ψ y = -(a y) - b y := by
    intro y
    have k1 := m1_integrable_kernel_mul_loc hh hηc hηs hψl y
    have k2 := m1_integrable_kernel_mul_loc hh hηc hηs hψ1l y
    have : (∫ x, a16_kernel d h η (y - x) * (ζ x * ψ x)) =
        (∫ x, a16_kernel d h η (y - x) * ψ x) - b y := by
      rw [hb, ← integral_sub k1 k2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [this, ha]; ring
  have hpt : ∀ y, ‖f1 y * ((∫ x, a16_kernel d h η (y - x) * (ζ x * ψ x)) - ψ y)‖ₑ ≤
      ‖f1 y * a y‖ₑ + ‖f1 y * b y‖ₑ := by
    intro y
    rw [hlin y, enorm_mul, enorm_mul, enorm_mul, ← mul_add]
    refine mul_le_mul' le_rfl ?_
    calc ‖-(a y) - b y‖ₑ = ‖-(a y + b y)‖ₑ := by congr 1; ring
      _ = ‖a y + b y‖ₑ := enorm_neg _
      _ ≤ ‖a y‖ₑ + ‖b y‖ₑ := enorm_add_le _ _
  have hA := l2b_holder_enorm (μ := volume) hpq hf1 ham.aestronglyMeasurable
  have hB := l2b_holder_enorm (μ := volume) hpq hf1 hbm.aestronglyMeasurable
  have hnorm1 : eLpNorm a (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (Real.sqrt d * h) *
        eLpNorm (fun y => eucNorm (g y)) (ENNReal.ofReal q) volume := by
    have := m1_sub_conv_eLpNorm_le hh hηc hη0 hη1 hηs isOpen_univ MeasurableSet.univ
      (fun x _ y _ => Set.mem_univ y) hψm hgm hψl hgl hweak hq
    simpa only [Measure.restrict_univ] using this
  have hnorm2 : eLpNorm b (ENNReal.ofReal q) volume ≤
      eLpNorm (fun x => (1 - ζ x) * ψ x) (ENNReal.ofReal q) volume := by
    have := m1_conv_eLpNorm_le hh hηc hη0 hη1 hηs hq hψ1m MeasurableSet.univ
      (V := Set.univ) (W := Set.univ) (fun x _ y _ => Set.mem_univ y)
    simpa only [Measure.restrict_univ] using this
  have hfm : AEMeasurable (fun y => ‖f1 y * a y‖ₑ) volume :=
    (hf1.mul ham.aestronglyMeasurable).aemeasurable.enorm
  calc ENNReal.ofReal |∫ y, f1 y * ((∫ x, a16_kernel d h η (y - x) * (ζ x * ψ x)) - ψ y)|
      = ‖∫ y, f1 y * ((∫ x, a16_kernel d h η (y - x) * (ζ x * ψ x)) - ψ y)‖ₑ := by
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ ≤ ∫⁻ y, ‖f1 y * ((∫ x, a16_kernel d h η (y - x) * (ζ x * ψ x)) - ψ y)‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, (‖f1 y * a y‖ₑ + ‖f1 y * b y‖ₑ) := lintegral_mono hpt
    _ = (∫⁻ y, ‖f1 y * a y‖ₑ) + ∫⁻ y, ‖f1 y * b y‖ₑ := lintegral_add_left' hfm _
    _ ≤ eLpNorm f1 (ENNReal.ofReal p) volume * eLpNorm a (ENNReal.ofReal q) volume +
        eLpNorm f1 (ENNReal.ofReal p) volume * eLpNorm b (ENNReal.ofReal q) volume :=
        add_le_add hA hB
    _ ≤ _ := by
        rw [← mul_add]
        exact mul_le_mul' le_rfl (add_le_add hnorm1 hnorm2)

theorem l2b_eucNorm_le (v : Vec d) : eucNorm v ≤ Real.sqrt d * ‖v‖ := by
  unfold eucNorm
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (Nat.cast_nonneg d)]
  refine Real.sqrt_le_sqrt ?_
  unfold vecNormSq vecDot
  calc ∑ i, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_le_pi_norm v i
        rw [Real.norm_eq_abs] at this
        nlinarith only [this, abs_nonneg (v i), sq_abs (v i)]
    _ = d * ‖v‖ ^ 2 := by simp

/-- Measurable representatives of the zero extension of an `H¹₀(W)` function and its gradient,
with the weak-gradient identity on `ℝ^d`. -/
theorem l2b_rep {W : Set (Vec d)} (hWm : MeasurableSet W) (ψ : H10Function W) :
    ∃ (ψ' : Vec d → ℝ) (g' : Vec d → Vec d), Measurable ψ' ∧ (∀ i, Measurable fun x => g' x i) ∧
      ψ.zeroExtension =ᵐ[volume] ψ' ∧ (∀ᵐ x ∂volume, ψ.zeroExtensionGrad x = g' x) ∧
      LocallyIntegrable ψ' volume ∧ (∀ i, LocallyIntegrable (fun x => g' x i) volume) ∧
      (∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ (Set.univ : Set (Vec d)) →
          ∫ x, ψ' x * fderiv ℝ φ x (basisVec i) = -∫ x, g' x i * φ x) := by
  have hψ : MemLp ψ.zeroExtension 2 volume :=
    ψ.memLp_zeroExtension hWm ψ.toH1Function.memL2
  have hg : ∀ i, MemLp (fun x => ψ.zeroExtensionGrad x i) 2 volume := by
    intro i
    have := ψ.gradMemLp_zeroExtensionGrad hWm ψ.toH1Function.gradMemL2 i
    simpa only [MemLpOn, Measure.restrict_univ] using this
  have hgm : ∀ i, AEStronglyMeasurable (fun x => ψ.zeroExtensionGrad x i) volume :=
    fun i => (hg i).aestronglyMeasurable
  set ψ' : Vec d → ℝ := hψ.aestronglyMeasurable.mk _ with hψ'
  set g' : Vec d → Vec d := fun x i => (hgm i).mk _ x with hg'
  have hae : ψ.zeroExtension =ᵐ[volume] ψ' := hψ.aestronglyMeasurable.ae_eq_mk
  have hgae : ∀ i, (fun x => ψ.zeroExtensionGrad x i) =ᵐ[volume] fun x => g' x i :=
    fun i => (hgm i).ae_eq_mk
  have hgae' : ∀ᵐ x ∂volume, ψ.zeroExtensionGrad x = g' x := by
    have := ae_all_iff.2 hgae
    filter_upwards [this] with x hx
    funext i; exact hx i
  have hψ'm : Measurable ψ' := hψ.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hg'm : ∀ i, Measurable fun x => g' x i := fun i => (hgm i).stronglyMeasurable_mk.measurable
  refine ⟨ψ', g', hψ'm, hg'm, hae, hgae', ?_, fun i => ?_, ?_⟩
  · exact (hψ.ae_eq hae).locallyIntegrable (by norm_num)
  · exact ((hg i).ae_eq (hgae i)).locallyIntegrable (by norm_num)
  · intro i φ hφ hφc hts
    have h0 := ψ.hasWeakGradientOn_univ_zeroExtension hWm i φ hφ hφc hts
    simp only [Measure.restrict_univ] at h0
    have e1 : ∫ x, ψ' x * fderiv ℝ φ x (basisVec i) =
        ∫ x, ψ.zeroExtension x * fderiv ℝ φ x (basisVec i) :=
      integral_congr_ae (hae.mono fun x hx => by beta_reduce; rw [hx])
    have e2 : ∫ x, g' x i * φ x = ∫ x, ψ.zeroExtensionGrad x i * φ x :=
      integral_congr_ae ((hgae i).mono fun x hx => by beta_reduce at hx ⊢; rw [hx])
    rw [e1, e2]
    exact h0

/-- Fubini exchange with integrability of both sides. -/
theorem l2b_pairing {k : Vec d → ℝ} (hk : Continuous k) {B : ℝ} (hkb : ∀ z, |k z| ≤ B)
    {F G : Vec d → ℝ} (hF : Integrable F volume) (hG : Integrable G volume) :
    Integrable (fun x => (∫ y, k (x - y) * F y) * G x) volume ∧
      Integrable (fun y => F y * ∫ x, k (x - y) * G x) volume ∧
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
  refine ⟨?_, ?_, ?_⟩
  · have := hint.integral_prod_left
    simpa only [Function.uncurry, e1] using this
  · have := hint.swap.integral_prod_left
    simpa only [Function.comp, Function.uncurry, Prod.swap, e2] using this
  · simp only [e1, e2]
    exact integral_integral_swap hint

theorem l2b_kernel_refl (h : ℝ) (η : Vec d → ℝ) (x y : Vec d) :
    a16_kernel d h η (x - y) = a16_kernel d h (fun w => η (-w)) (y - x) := by
  unfold a16_kernel
  rw [← neg_sub x y, smul_neg]
  simp only [neg_neg]

theorem l2b_refl_integral (η : Vec d → ℝ) : ∫ w, η (-w) = ∫ w, η w :=
  integral_neg_eq_self η volume

/-- **The duality identity**: `∫_W (ζ η ∗ f - f) ψ = ∫ f1 (η̌ ∗ (ζ ψ) - ψ)` for the
zero extension of `ψ` and `f1 = 1_W f`. -/
theorem l2b_E1_identity {W : Set (Vec d)} (hWm : MeasurableSet W) (hWb : Bornology.IsBounded W)
    {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η) {A : ℝ} (hηA : ∀ w, |η w| ≤ A)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ζ : Vec d → ℝ} (hζm : Measurable ζ)
    (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1)
    (hloc : ∀ x, ζ x ≠ 0 → ∀ y, dist y x ≤ h → y ∈ W) {f : Vec d → ℝ}
    (hfi : IntegrableOn f W volume) (ψ : H10Function W)
    (hfψ : IntegrableOn (fun x => f x * ψ.toH1Function.toFun x) W volume)
    {ψ' : Vec d → ℝ} (hae : ψ.zeroExtension =ᵐ[volume] ψ') :
    ∫ x in W, (ζ x * l2a_moll d h η f x - f x) * ψ.toH1Function.toFun x =
      ∫ y, W.indicator f y *
        ((∫ x, a16_kernel d h (fun w => η (-w)) (y - x) * (ζ x * ψ' x)) - ψ' y) := by
  set f1 : Vec d → ℝ := W.indicator f with hf1
  have hf1i : Integrable f1 volume := (integrable_indicator_iff hWm).2 hfi
  have hψi : Integrable ψ.zeroExtension volume :=
    (integrable_indicator_iff hWm).2 (l2a_integrableOn_of_memL2 hWb ψ.toH1Function.memL2)
  have hψm : AEStronglyMeasurable ψ.zeroExtension volume := hψi.aestronglyMeasurable
  have hGi : Integrable (fun x => ζ x * ψ.zeroExtension x) volume := by
    refine hψi.norm.mono' (hζm.aestronglyMeasurable.mul hψm) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hζ0 x)]
    exact mul_le_of_le_one_left (norm_nonneg (ψ.zeroExtension x)) (hζ1 x)
  have hkc : Continuous (a16_kernel d h η) := a16_kernel_continuous hηc
  have hkb : ∀ z, |a16_kernel d h η z| ≤ A * (h⁻¹) ^ d := fun z => a16_kernel_abs_le hh hηA z
  obtain ⟨P1, P2, P3⟩ := l2b_pairing hkc hkb hf1i hGi
  -- the integral over `W` becomes an integral over `ℝ^d`
  have hψ0 : ∀ x, x ∉ W → ψ.zeroExtension x = 0 := fun x hx => ψ.zeroExtension_apply_of_not_mem hx
  have hstep1 : ∫ x in W, (ζ x * l2a_moll d h η f x - f x) * ψ.toH1Function.toFun x =
      ∫ x, (ζ x * l2a_moll d h η f1 x - f1 x) * ψ.zeroExtension x := by
    have hext : ∫ x, (ζ x * l2a_moll d h η f1 x - f1 x) * ψ.zeroExtension x =
        ∫ x in W, (ζ x * l2a_moll d h η f1 x - f1 x) * ψ.zeroExtension x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [hψ0 x hx, mul_zero]).symm
    rw [hext]
    refine setIntegral_congr_fun hWm fun x hx => ?_
    rw [ψ.zeroExtension_apply_of_mem hx, hf1, Set.indicator_of_mem hx]
    by_cases hz : ζ x = 0
    · simp [hz]
    · rw [l2a_moll_congr hh hηs (u' := W.indicator f) fun y hy => by
        rw [Set.indicator_of_mem (hloc x hz y hy)]]
  have hf1ψ : Integrable (fun x => f1 x * ψ.zeroExtension x) volume := by
    have : (fun x => f1 x * ψ.zeroExtension x) = W.indicator (fun x => f x * ψ.toH1Function.toFun x) := by
      funext x
      by_cases hx : x ∈ W
      · simp [hf1, Set.indicator_of_mem hx, ψ.zeroExtension_apply_of_mem hx]
      · simp [hf1, Set.indicator_of_notMem hx, hψ0 x hx]
    rw [this]
    exact (integrable_indicator_iff hWm).2 hfψ
  have hstep2 : ∫ x, (ζ x * l2a_moll d h η f1 x - f1 x) * ψ.zeroExtension x =
      (∫ x, (∫ y, a16_kernel d h η (x - y) * f1 y) * (ζ x * ψ.zeroExtension x)) -
        ∫ x, f1 x * ψ.zeroExtension x := by
    rw [← integral_sub P1 hf1ψ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [l2a_moll]; ring
  rw [hstep1, hstep2, P3, ← integral_sub P2 hf1ψ]
  -- replace the zero extension by its representative
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  have hint : (∫ x, a16_kernel d h η (x - y) * (ζ x * ψ.zeroExtension x)) =
      ∫ x, a16_kernel d h (fun w => η (-w)) (y - x) * (ζ x * ψ' x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, l2b_kernel_refl h η x y]
  rw [hint, hy]
  ring


/-- **The mollification error against `f`** (`e.Dir.new.f.mollification`),
deterministic core: `‖ζ η ∗ f - f‖_{W̲^{-1,p}(W)} ≤ (d h + CP r) ‖f‖_{L̲^p(W)}`, where `h` is the
mollification scale, `ζ = 1` off the layer `A` and the layer Poincaré inequality
`‖ψ‖_{L^q(A)} ≤ CP r ‖∇ψ‖_{L^q(W)}` holds for `ψ ∈ H¹₀(W)`. -/
theorem l2b_E1_core {W : Set (Vec d)} (hWm : MeasurableSet W) (hWb : Bornology.IsBounded W)
    (hW0 : volume W ≠ 0) (hWT : volume W ≠ ⊤) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hηc : Continuous η) {Bη : ℝ} (hηA : ∀ w, |η w| ≤ Bη) (hη0 : ∀ w, 0 ≤ η w)
    (hη1 : ∫ w, η w = 1) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ζ : Vec d → ℝ}
    (hζm : Measurable ζ) (hζ0 : ∀ x, 0 ≤ ζ x) (hζ1 : ∀ x, ζ x ≤ 1)
    (hloc : ∀ x, ζ x ≠ 0 → ∀ y, dist y x ≤ h → y ∈ W) {A : Set (Vec d)} (hAm : MeasurableSet A)
    (hA : ∀ x ∈ W, ζ x ≠ 1 → x ∈ A) {r CP p q : ℝ} (hCP : 0 ≤ CP * r)
    (hpq : p.HolderConjugate q)
    (hPoinc : ∀ ψ : H10Function W,
      eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict A) ≤
        ENNReal.ofReal (CP * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal q) (volume.restrict W))
    {f : Vec d → ℝ} (hfi : IntegrableOn f W volume)
    (hfψ : ∀ ψ : H10Function W, IntegrableOn (fun x => f x * ψ.toH1Function.toFun x) W volume) :
    wMinusOneBar W (ENNReal.ofReal p) (fun x => ζ x * l2a_moll d h η f x - f x) ≤
      ENNReal.ofReal (d * h + CP * r) * lpBar W (ENNReal.ofReal p) f := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hq1 : 1 < q := hpq.symm.lt
  have hQ := l2b_conj_exponent hpq
  unfold wMinusOneBar
  refine iSup₂_le fun ψ hψ => ?_
  rw [hQ] at hψ
  obtain ⟨ψ', g', hψ'm, hg'm, hae, hgae, hψ'l, hg'l, hweak⟩ := l2b_rep hWm ψ
  have hI := l2b_E1_identity hWm hWb hh hηc hηA hηs hζm hζ0 hζ1 hloc hfi ψ (hfψ ψ) hae
  have hf1m : AEStronglyMeasurable (W.indicator f) volume :=
    ((integrable_indicator_iff hWm).2 hfi).aestronglyMeasurable
  have hE1 := l2b_E1_duality (η := fun w => η (-w)) hh (hηc.comp continuous_neg)
    (fun w => hη0 _) (by rw [l2b_refl_integral]; exact hη1)
    (fun w hw => by
      obtain ⟨i, hi⟩ := hw
      exact hηs (-w) ⟨i, by simpa only [Pi.neg_apply, abs_neg] using hi⟩)
    hζm hζ0 hζ1 hψ'm hg'm hψ'l hg'l hweak hf1m hpq hq1.le
  -- the three norms
  set E : ℝ≥0∞ := eLpNorm (fun x => ‖ψ.toH1Function.grad x‖) (ENNReal.ofReal q)
    (volume.restrict W) with hEdef
  have hgm : AEStronglyMeasurable ψ.toH1Function.grad (volume.restrict W) :=
    (aemeasurable_pi_iff.2 fun i =>
      (ψ.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have N1 : eLpNorm (W.indicator f) (ENNReal.ofReal p) volume =
      eLpNorm f (ENNReal.ofReal p) (volume.restrict W) :=
    eLpNorm_indicator_eq_eLpNorm_restrict hWm
  have N2 : eLpNorm (fun y => eucNorm (g' y)) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (Real.sqrt d) * E := by
    have h1 : eLpNorm (fun y => eucNorm (g' y)) (ENNReal.ofReal q) volume ≤
        eLpNorm (fun y => Real.sqrt d * ‖g' y‖) (ENNReal.ofReal q) volume := by
      refine eLpNorm_mono_enorm (m1_measurable_eucNorm hg'm).aestronglyMeasurable fun y => ?_
      rw [Real.enorm_of_nonneg (show 0 ≤ eucNorm (g' y) from Real.sqrt_nonneg _),
        Real.enorm_of_nonneg (by positivity)]
      exact ENNReal.ofReal_le_ofReal (l2b_eucNorm_le _)
    refine h1.trans (le_of_eq ?_)
    have h2 : eLpNorm (fun y => Real.sqrt d * ‖g' y‖) (ENNReal.ofReal q) volume =
        ‖Real.sqrt d‖ₑ * eLpNorm (fun y => ‖g' y‖) (ENNReal.ofReal q) volume :=
      eLpNorm_const_smul (Real.sqrt d) (fun y => ‖g' y‖) (ENNReal.ofReal q) volume
    rw [h2, Real.enorm_of_nonneg (Real.sqrt_nonneg _)]
    congr 1
    have h3 : eLpNorm (fun y => ‖g' y‖) (ENNReal.ofReal q) volume =
        eLpNorm (fun y => ‖ψ.zeroExtensionGrad y‖) (ENNReal.ofReal q) volume :=
      eLpNorm_congr_ae (hgae.mono fun y hy => by beta_reduce; rw [hy])
    rw [h3]
    have h4 : (fun y => ‖ψ.zeroExtensionGrad y‖) =
        W.indicator (fun x => ‖ψ.toH1Function.grad x‖) := by
      funext y
      by_cases hy : y ∈ W
      · simp [Set.indicator_of_mem hy, ψ.zeroExtensionGrad_apply_of_mem hy]
      · simp [Set.indicator_of_notMem hy, ψ.zeroExtensionGrad_apply_of_not_mem hy]
    rw [h4, eLpNorm_indicator_eq_eLpNorm_restrict hWm]
  have N3 : eLpNorm (fun x => (1 - ζ x) * ψ' x) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (CP * r) * E := by
    have h0 : eLpNorm (fun x => (1 - ζ x) * ψ' x) (ENNReal.ofReal q) volume =
        eLpNorm (fun x => (1 - ζ x) * ψ.zeroExtension x) (ENNReal.ofReal q) volume :=
      eLpNorm_congr_ae (hae.mono fun x hx => by beta_reduce; rw [hx])
    rw [h0]
    have hψt : AEStronglyMeasurable ψ.zeroExtension volume :=
      (ψ.memLp_zeroExtension hWm ψ.toH1Function.memL2).aestronglyMeasurable
    refine (eLpNorm_mono_enorm
      ((measurable_const.sub hζm).aestronglyMeasurable.mul hψt)
      (g := A.indicator ψ.toH1Function.toFun) fun x => ?_).trans ?_
    · show ‖(1 - ζ x) * ψ.zeroExtension x‖ₑ ≤ ‖A.indicator ψ.toH1Function.toFun x‖ₑ
      by_cases hx : x ∈ W
      · by_cases hz : ζ x = 1
        · simp [hz]
        · rw [Set.indicator_of_mem (hA x hx hz), ψ.zeroExtension_apply_of_mem hx, enorm_mul]
          have : ‖1 - ζ x‖ₑ ≤ 1 := by
            rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_one]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [abs_le]; constructor <;> linarith only [hζ0 x, hζ1 x]
          calc ‖1 - ζ x‖ₑ * ‖ψ.toH1Function.toFun x‖ₑ ≤ 1 * ‖ψ.toH1Function.toFun x‖ₑ :=
                mul_le_mul' this le_rfl
            _ = _ := one_mul _
      · simp [ψ.zeroExtension_apply_of_not_mem hx]
    · rw [eLpNorm_indicator_eq_eLpNorm_restrict hAm]
      exact hPoinc ψ
  -- the assembly
  have hcN : ENNReal.ofReal (Real.sqrt d * h) * (ENNReal.ofReal (Real.sqrt d) * E) +
      ENNReal.ofReal (CP * r) * E = ENNReal.ofReal (d * h + CP * r) * E := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← add_mul,
      ← ENNReal.ofReal_add (by positivity) hCP]
    congr 3
    rw [mul_right_comm, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  have hW0' : (volume W)⁻¹ ≠ 0 := by simpa using hWT
  have hWT' : (volume W)⁻¹ ≠ ⊤ := by simpa using hW0
  have hvv : (volume W)⁻¹ = (volume W)⁻¹ ^ (1 / p) * (volume W)⁻¹ ^ (1 / q) := by
    rw [← ENNReal.rpow_add _ _ hW0' hWT', hpq.one_div_add_one_div]
    simp
  have e2 : ENNReal.ofReal |(volume W).toReal⁻¹ *
        ∫ x in W, (ζ x * l2a_moll d h η f x - f x) * ψ.toH1Function.toFun x| =
      (volume W)⁻¹ * ENNReal.ofReal |∫ x in W, (ζ x * l2a_moll d h η f x - f x) *
        ψ.toH1Function.toFun x| := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ← ENNReal.toReal_inv,
      ENNReal.ofReal_toReal hWT']
  have hfm : AEStronglyMeasurable f (volume.restrict W) := hfi.aestronglyMeasurable
  have hlf := l2b_lpBar_eq_eLpNorm hp0 hfm
  have hlg := l2b_lpBar_eq_eLpNorm hq0 hgm
  have hn : eLpNorm (fun x => ‖ψ.toH1Function.grad x‖) (ENNReal.ofReal q) (volume.restrict W) =
      eLpNorm ψ.toH1Function.grad (ENNReal.ofReal q) (volume.restrict W) := eLpNorm_norm _ hgm
  show ENNReal.ofReal |(volume W).toReal⁻¹ *
        ∫ x in W, (ζ x * l2a_moll d h η f x - f x) * ψ.toH1Function.toFun x| ≤ _
  rw [e2, hI]
  calc (volume W)⁻¹ * ENNReal.ofReal |∫ y, W.indicator f y *
        ((∫ x, a16_kernel d h (fun w => η (-w)) (y - x) * (ζ x * ψ' x)) - ψ' y)|
      ≤ (volume W)⁻¹ * (eLpNorm f (ENNReal.ofReal p) (volume.restrict W) *
          (ENNReal.ofReal (d * h + CP * r) * E)) := by
        refine mul_le_mul' le_rfl ?_
        rw [← N1, ← hcN]
        exact hE1.trans (mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl N2) N3))
    _ = ENNReal.ofReal (d * h + CP * r) *
          ((volume W)⁻¹ ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) (volume.restrict W)) *
          ((volume W)⁻¹ ^ (1 / q) * E) := by
        conv_lhs => rw [hvv]
        rw [hEdef, hn]
        ring
    _ ≤ ENNReal.ofReal (d * h + CP * r) * lpBar W (ENNReal.ofReal p) f * 1 := by
        rw [hlf]
        refine mul_le_mul' le_rfl ?_
        rw [hEdef, hn, ← hlg]
        exact hψ
    _ = _ := mul_one _

/-- The cutoff is supported where the whole `2·3^n`-neighbourhood lies in `W`. -/
theorem l2b_cutoff_marg {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) {n : ℕ}
    (hn : 2 * (3 : ℝ) ^ n < r) :
    ∀ x, l2a_cutoff W r x ≠ 0 → ∀ y : Vec d, (∀ i, |y i - x i| ≤ 2 * 3 ^ n) → y ∈ W := by
  intro x hx y hy
  have h1 := l2a_cutoff_ne_zero_imp hr hx
  by_contra hyW
  have h2 : Metric.infDist x Wᶜ ≤ dist x y := Metric.infDist_le_dist_of_mem hyW
  have h3 : dist x y ≤ 2 * 3 ^ n := by
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq, abs_sub_comm]
    exact hy i
  linarith only [h1, h2, h3, hn]

/-- The mollifier ball around a point of the support of the cutoff lies in `W`. -/
theorem l2b_cutoff_loc {W : Set (Vec d)} {r h : ℝ} (hr : 0 < r) (hh : h ≤ r) :
    ∀ x, l2a_cutoff W r x ≠ 0 → ∀ y, dist y x ≤ h → y ∈ W := by
  intro x hx y hy
  have h1 := l2a_cutoff_ne_zero_imp hr hx
  by_contra hyW
  have h2 : Metric.infDist x Wᶜ ≤ dist x y := Metric.infDist_le_dist_of_mem hyW
  rw [dist_comm] at h2
  linarith only [h1, h2, hy, hh]

/-- The transition region of the cutoff: `r ≤ dist(x, Wᶜ) ≤ 2 r`. -/
def l2b_layerA (W : Set (Vec d)) (r : ℝ) : Set (Vec d) :=
  {x | r ≤ Metric.infDist x Wᶜ ∧ Metric.infDist x Wᶜ ≤ 2 * r}

theorem l2b_layerA_measurable (W : Set (Vec d)) (r : ℝ) : MeasurableSet (l2b_layerA W r) := by
  have hc : Continuous fun x : Vec d => Metric.infDist x Wᶜ := Metric.continuous_infDist_pt _
  exact (isClosed_le continuous_const hc).measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet

theorem l2b_layerA_subset {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) : l2b_layerA W r ⊆ W := by
  intro x hx
  by_contra hxW
  have := Metric.infDist_zero_of_mem (show x ∈ Wᶜ from hxW)
  linarith only [hx.1, this, hr]

theorem l2b_lipGradient_zero_off {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) :
    ∀ x, x ∉ l2b_layerA W r → lipGradient (l2a_cutoff W r) x = 0 := by
  intro x hx
  refine l2a_lipGradient_cutoff_eq_zero W hr ?_
  by_contra h
  push Not at h
  exact hx ⟨h.1, h.2⟩

theorem l2b_lipGradient_norm_le (W : Set (Vec d)) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    ‖lipGradient (l2a_cutoff W r) x‖ ≤ 1 / r := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact l2a_lipGradient_cutoff_abs_le W hr x i

theorem l2b_layerA_marg {W : Set (Vec d)} {r : ℝ} {n : ℕ} (hn : 2 * (3 : ℝ) ^ n < r) :
    ∀ x ∈ l2b_layerA W r, ∀ y : Vec d, (∀ i, |y i - x i| ≤ 2 * 3 ^ n) → y ∈ W := by
  intro x hx y hy
  by_contra hyW
  have h2 : Metric.infDist x Wᶜ ≤ dist x y := Metric.infDist_le_dist_of_mem hyW
  have h3 : dist x y ≤ 2 * 3 ^ n := by
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq, abs_sub_comm]
    exact hy i
  linarith only [hx.1, h2, h3, hn]

/-- The region where `1 - ζ` can be nonzero, inside `W`. -/
def l2b_layerB (W : Set (Vec d)) (r : ℝ) : Set (Vec d) :=
  {x | x ∈ W ∧ Metric.infDist x Wᶜ ≤ 2 * r}

theorem l2b_layerB_measurable {W : Set (Vec d)} (hW : MeasurableSet W) (r : ℝ) :
    MeasurableSet (l2b_layerB W r) := by
  have hc : Continuous fun x : Vec d => Metric.infDist x Wᶜ := Metric.continuous_infDist_pt _
  exact hW.inter (isClosed_le hc continuous_const).measurableSet

theorem l2b_layerB_cover {W : Set (Vec d)} {r : ℝ} (hr : 0 < r) :
    ∀ x ∈ W, l2a_cutoff W r x ≠ 1 → x ∈ l2b_layerB W r := by
  intro x hx hz
  refine ⟨hx, ?_⟩
  by_contra h
  exact hz (l2a_cutoff_eq_one hr (not_le.1 h).le)

/-- A point of `W` at distance `< t` from `Wᶜ` lies in the boundary layer of thickness `t`. -/
theorem l2b_layer_of_infDist [NeZero d] {W : Set (Vec d)} {D : ℝ}
    (hD : ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ D) {t : ℝ} {x : Vec d} (hx : x ∈ W)
    (hlt : Metric.infDist x Wᶜ < t) : x ∈ boundaryLayer W t := by
  have hne : W ≠ univ := by
    intro hWu
    subst hWu
    have hb : Bornology.IsBounded (univ : Set (Vec d)) := by
      refine (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).2 ⟨D + ‖(0 : Vec d)‖, fun y _ => ?_⟩
      have := hD y (mem_univ _) 0 (mem_univ _)
      rw [mem_closedBall_zero_iff]
      simpa using this
    exact NormedSpace.unbounded_univ ℝ (Vec d) hb
  obtain ⟨y, hy, hxy⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hne
  refine ⟨hx, ?_⟩
  have : Metric.infDist x (frontier W) ≤ dist x y := Metric.infDist_le_dist_of_mem hy
  linarith only [this, hxy, hlt]

/-- The layer Poincaré inequality (`exists_layerPoincare`) with the explicit threshold
`t ≤ r / (3 (d + (1 + d) max(M₁, 0)) + 4)`. -/
theorem l2b_layerPoincare_explicit [NeZero d] (r M₁ : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 1 ≤ K ∧
      ∀ {U : Set (Vec d)} {M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
        ∀ (ψ : H10Function U) {q : ℝ}, 1 ≤ q → ∀ {t : ℝ}, 0 < t →
          t ≤ r / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
          eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q)
              (volume.restrict (boundaryLayer U t)) ≤
            ENNReal.ofReal (C * t) *
              eLpNorm (fun x => ‖ψ.toH1Function.grad x‖) (ENNReal.ofReal q)
                (volume.restrict (boundaryLayer U (K * t))) := by
  set κ₀ : ℝ := (d : ℝ) + (1 + d) * max M₁ 0 with hκ₀
  have hκ0 : 0 ≤ κ₀ := by
    have : 0 ≤ max M₁ 0 := le_max_right _ _
    positivity
  set Bn : ℕ := ⌈3 * κ₀ + 5⌉₊ with hBn
  set Nr : ℝ := (((2 * Bn + 1) ^ d : ℕ) : ℝ) with hNr
  have hNr0 : 0 ≤ Nr := Nat.cast_nonneg _
  refine ⟨3 * κ₀ * d * Nr, 3 * κ₀ + 5, by positivity, by linarith only [hκ0], ?_⟩
  intro U M₂ D h ψ q hq t ht htt
  have hq0 : 0 < q := by linarith only [hq]
  by_cases hU0 : U = ∅
  · have hL : boundaryLayer U t = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => by
        have := hx.1
        rw [hU0] at this
        exact this
    rw [hL, Measure.restrict_empty, eLpNorm_measure_zero]
    exact bot_le
  obtain ⟨x0, hx0⟩ := layerPoincare_frontier_nonempty h.2.2.1 hU0
  obtain ⟨e, γ, he, hγ, hb, -, -⟩ := h.2.2.2 x0 hx0
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  have hκ : κ₀ = (d : ℝ) + (1 + d) * M₁ := by rw [hκ₀, max_eq_left hM]
  have hr' : (3 * ((d : ℝ) + (1 + d) * M₁) + 4) * t ≤ r := by
    have := (le_div_iff₀ (by positivity : 0 < 3 * κ₀ + 4)).1 htt
    rw [hκ] at this
    linarith only [this]
  have hint := layerPoincare_integral h ψ hq ht hr'
  rw [← hκ] at hint
  have hN1 : (1 : ℝ≥0∞) ≤ (((2 * ⌈3 * κ₀ + 5⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) := by
    have : 1 ≤ (2 * ⌈3 * κ₀ + 5⌉₊ + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast this
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq0).ne'
  have hmeasψ : AEStronglyMeasurable ψ.toH1Function.toFun
      (volume.restrict (boundaryLayer U t)) :=
    ψ.toH1Function.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono (fun x hx => hx.1) le_rfl)
  have hmeasg : AEStronglyMeasurable (fun x => ‖ψ.toH1Function.grad x‖)
      (volume.restrict (boundaryLayer U ((3 * κ₀ + 5) * t))) := by
    have : AEStronglyMeasurable ψ.toH1Function.grad (volume.restrict U) :=
      (aemeasurable_pi_iff.2 fun i =>
        (ψ.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    exact (this.mono_measure (Measure.restrict_mono (fun x hx => hx.1) le_rfl)).norm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hmeasψ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hmeasg,
    ENNReal.toReal_ofReal hq0.le]
  simp only [enorm_norm]
  have hfin := layerPoincare_rpow_div hq hN1 hint
  refine hfin.trans ?_
  refine mul_le_mul_left ?_ _
  have hNe : ((((2 * ⌈3 * κ₀ + 5⌉₊ + 1) ^ d : ℕ)) : ℝ≥0∞) = ENNReal.ofReal Nr := by
    rw [hNr, ENNReal.ofReal_natCast]
  rw [hNe, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- **The layer Poincaré inequality in the form used by the layer terms**: for a uniformly
`C^{1,1}` domain, `‖ψ‖_{L^q(A)} ≤ CP r ‖∇ψ‖_{L^q(W)}` for `ψ ∈ H¹₀(W)`, every `A` inside the
boundary layer of thickness `3 r`, `3 r ≤ r₀ / (3 (d + (1 + d) max(M₁, 0)) + 4)`. -/
theorem l2b_hPoinc [NeZero d] (r₀ M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ {q : ℝ}, 1 ≤ q → ∀ {r : ℝ}, 0 < r →
        3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
        ∀ {A : Set (Vec d)}, A ⊆ boundaryLayer W (3 * r) → ∀ ψ : H10Function W,
          eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict A) ≤
            ENNReal.ofReal (CP * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
              (ENNReal.ofReal q) (volume.restrict W) := by
  obtain ⟨C, K, hC, hK, H⟩ := l2b_layerPoincare_explicit (d := d) r₀ M₁
  refine ⟨3 * C, by positivity, ?_⟩
  intro W M₂ D hU q hq r hr h3r A hA ψ
  have h := H hU ψ hq (t := 3 * r) (by positivity) h3r
  calc eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict A)
      ≤ eLpNorm ψ.toH1Function.toFun (ENNReal.ofReal q) (volume.restrict (boundaryLayer W (3 * r))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hA le_rfl)
    _ ≤ ENNReal.ofReal (C * (3 * r)) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal q) (volume.restrict (boundaryLayer W (K * (3 * r)))) := h
    _ ≤ ENNReal.ofReal (3 * C * r) * eLpNorm (fun x => ‖ψ.toH1Function.grad x‖)
          (ENNReal.ofReal q) (volume.restrict W) := by
        have e : C * (3 * r) = 3 * C * r := by ring
        rw [e]
        exact mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono (fun x hx => hx.1) le_rfl))

theorem l2b_bounded_of_uniform {W : Set (Vec d)} {r₀ M₁ M₂ D : ℝ}
    (hU : IsUniformC11Domain W r₀ M₁ M₂ D) : Bornology.IsBounded W := by
  rcases W.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · rw [he]; exact Bornology.isBounded_empty
  · refine (Metric.isBounded_iff_subset_closedBall x₀).2 ⟨D, fun y hy => ?_⟩
    rw [mem_closedBall_iff_norm]
    exact hU.2.2.1 y hy x₀ hx₀

/-- **The interior flux term with the cutoff**. -/
theorem l2b_E3_cutoff (n : ℕ) {W : Set (Vec d)} (hWm : MeasurableSet W) (hW0 : volume W ≠ 0)
    (hWT : volume W ≠ ⊤) {r : ℝ} (hr : 0 < r) (hn : 2 * (3 : ℝ) ^ n < r) {G : Vec d → Vec d}
    (hGm : AEStronglyMeasurable G (volume.restrict W)) {v w : Vec d → ℝ}
    (hvm : AEStronglyMeasurable v (volume.restrict W))
    (hwm : AEStronglyMeasurable w (volume.restrict W)) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p < 2)
    {α β : ℝ≥0∞}
    (hG : ∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
      ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal ‖G x‖ ≤
        α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖v x‖ₑ) 2 +
          β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
            (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖w x‖ₑ) p) :
    lpBar W (ENNReal.ofReal p) (fun x => l2a_cutoff W r x • G x) ≤
      α * lpBar W (ENNReal.ofReal 2) v + β * lpBar W (ENNReal.ofReal p) w :=
  l2b_E3_core n hWm hW0 hWT (fun x => l2a_cutoff_abs_le W r x) (l2b_cutoff_marg hr hn)
    ((l2a_cutoff_continuous W hr).aestronglyMeasurable.smul hGm) hvm hwm hp1 hp2 hG

/-- **The layer term with the cutoff** (`e.Dir.new.boundary.flux.term`). -/
theorem l2b_E2_cutoff [NeZero d] (r₀ M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ (n : ℕ) {r : ℝ}, 0 < r →
        3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
        2 * (3 : ℝ) ^ n < r → volume W ≠ 0 → volume W ≠ ⊤ → ∀ {G : Vec d → Vec d},
        AEStronglyMeasurable G (volume.restrict W) → ∀ {v w : Vec d → ℝ},
        AEStronglyMeasurable v (volume.restrict W) → AEStronglyMeasurable w (volume.restrict W) →
        ∀ {p : ℝ}, 1 < p → p < 2 → ∀ {α β : ℝ≥0∞},
        (∀ k : Fin d → ℤ, l2b_cell (l2b_pt n k) (n + 1) ⊆ W →
          ∀ x ∈ l2b_cell (l2b_pt n k) n, ENNReal.ofReal ‖G x‖ ≤
            α * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖v x‖ₑ) 2 +
              β * l2b_avg (ENNReal.ofReal (cubeVolume (originCube d ((n + 1 : ℕ) : ℤ))))
                (l2b_cell (l2b_pt n k) (n + 1)) (fun x => ‖w x‖ₑ) p) →
        wMinusOneBar W (ENNReal.ofReal p)
            (fun x => vecDot (lipGradient (l2a_cutoff W r) x) (G x)) ≤
          ENNReal.ofReal (d * CP) *
            (α * (volume (boundaryLayer W (3 * r)) * (volume W)⁻¹) ^ (1 / p - 1 / 2) *
                lpBar W (ENNReal.ofReal 2) v +
              β * lpBar W (ENNReal.ofReal p) w) := by
  obtain ⟨CP, hCP, H⟩ := l2b_hPoinc (d := d) r₀ M₁
  refine ⟨CP, hCP, ?_⟩
  intro W M₂ D hU n r hr h3r hn hW0 hWT G hGm v w hvm hwm p hp1 hp2 α β hG
  have hWm : MeasurableSet W := hU.1.measurableSet
  have hAD : l2b_layerA W r ⊆ boundaryLayer W (3 * r) := fun x hx =>
    l2b_layer_of_infDist hU.2.2.1 (l2b_layerA_subset hr hx) (by linarith only [hx.2, hr])
  have hq1 : 1 ≤ p / (p - 1) := by
    rw [le_div_iff₀ (by linarith only [hp1])]; linarith only
  have hmain := l2b_E2_core n (l2b_layerA_measurable W r) (l2b_layerA_subset hr) hW0 hWT hr
    (l2b_lipGradient_norm_le W hr) (l2b_lipGradient_zero_off hr) (l2b_layerA_marg hn) hGm hvm hwm
    hp1 hp2 hG (CP := CP) (fun ψ => H hU hq1 hr h3r hAD ψ)
  refine hmain.trans (mul_le_mul' le_rfl (add_le_add (mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl) le_rfl))
  have hθ : 0 ≤ 1 / p - 1 / 2 := by
    have : 1 / 2 ≤ 1 / p := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith only [hp1])]; linarith only [hp2]
    linarith only [this]
  exact ENNReal.rpow_le_rpow (mul_le_mul' (measure_mono hAD) le_rfl) hθ

/-- **The mollification error against `f` with the cutoff**. -/
theorem l2b_E1_cutoff [NeZero d] (r₀ M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ (n : ℕ) {r : ℝ}, 0 < r →
        3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
        2 * (3 : ℝ) ^ n < r → volume W ≠ 0 → volume W ≠ ⊤ → ∀ {η : Vec d → ℝ}, Continuous η →
        ∀ {Bη : ℝ}, (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
        (∀ w, (∃ i, 1 < |w i|) → η w = 0) → ∀ {p q : ℝ}, p.HolderConjugate q →
        ∀ {f : Vec d → ℝ}, IntegrableOn f W volume →
        (∀ ψ : H10Function W, IntegrableOn (fun x => f x * ψ.toH1Function.toFun x) W volume) →
        wMinusOneBar W (ENNReal.ofReal p)
            (fun x => l2a_cutoff W r x * l2a_moll d ((3 : ℝ) ^ n) η f x - f x) ≤
          ENNReal.ofReal (d * (3 : ℝ) ^ n + CP * r) * lpBar W (ENNReal.ofReal p) f := by
  obtain ⟨CP, hCP, H⟩ := l2b_hPoinc (d := d) r₀ M₁
  refine ⟨CP, hCP, ?_⟩
  intro W M₂ D hU n r hr h3r hn hW0 hWT η hηc Bη hηA hη0 hη1 hηs p q hpq f hfi hfψ
  have hWm : MeasurableSet W := hU.1.measurableSet
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hLB : l2b_layerB W r ⊆ boundaryLayer W (3 * r) := fun x hx =>
    l2b_layer_of_infDist hU.2.2.1 hx.1 (by linarith only [hx.2, hr])
  exact l2b_E1_core hWm (l2b_bounded_of_uniform hU) hW0 hWT h3 hηc hηA hη0 hη1 hηs
    (l2a_cutoff_continuous W hr).measurable (l2a_cutoff_nonneg W r) (l2a_cutoff_le_one W r)
    (l2b_cutoff_loc hr (by linarith only [hn, h3])) (l2b_layerB_measurable hWm r)
    (l2b_layerB_cover hr) (mul_nonneg hCP hr.le) hpq
    (fun ψ => H hU hpq.symm.lt.le hr h3r hLB ψ) hfi hfψ

/-- Witness for the grid bound and the interior term: a large ball, `n = 0`, `r = 3`, zero data. -/
example : True := by
  have hWm : MeasurableSet (Metric.ball (0 : Vec 2) 100) := Metric.isOpen_ball.measurableSet
  have h := l2b_E3_cutoff (d := 2) 0 hWm (Metric.measure_ball_pos _ _ (by norm_num)).ne'
    Metric.isBounded_ball.measure_lt_top.ne (r := 3) (by norm_num) (by norm_num)
    (G := fun _ => 0) aestronglyMeasurable_const (v := fun _ => 0) (w := fun _ => 0)
    aestronglyMeasurable_const aestronglyMeasurable_const (p := 3 / 2) (by norm_num) (by norm_num)
    (α := 0) (β := 0) (fun k _ x _ => by simp)
  trivial

/-- Witness for the layer term and the mollification error: dilates of the unit ball by
`R = (9 (3 κ + 4)) / r + 1`, `n = 0`, `r = 3`, zero data. -/
example : True := by
  obtain ⟨r₁, M₁, M₂, D, hU⟩ := isUniformC11Domain_euclidBall (d := 2)
  have hr1 : 0 < r₁ := hU.2.1
  set κ : ℝ := (2 : ℕ) + (1 + (2 : ℕ)) * max M₁ 0 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set R : ℝ := 9 * (3 * κ + 4) / r₁ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hRU := hU.smul hR0
  have hWo : IsOpen (R • Section6.euclidBall (d := 2) 1) := hRU.1
  have hne : (R • Section6.euclidBall (d := 2) 1).Nonempty :=
    ⟨R • (0 : Vec 2), Set.smul_mem_smul_set (by simp [Section6.euclidBall, vecNormSq, vecDot])⟩
  have hW0 : volume (R • Section6.euclidBall (d := 2) 1) ≠ 0 := (hWo.measure_pos volume hne).ne'
  have hWT : volume (R • Section6.euclidBall (d := 2) 1) ≠ ⊤ :=
    (l2b_bounded_of_uniform hRU).measure_lt_top.ne
  have h3 : 3 * (3 : ℝ) ≤ R * r₁ / (3 * ((2 : ℕ) + (1 + (2 : ℕ)) * max M₁ 0) + 4) := by
    rw [le_div_iff₀ (by positivity)]
    have : 9 * (3 * κ + 4) ≤ R * r₁ := by
      rw [hR, add_mul, div_mul_cancel₀ _ hr1.ne']; linarith only [hr1]
    linarith only [this, hκ]
  obtain ⟨CP, hCP, H⟩ := l2b_E2_cutoff (d := 2) (R * r₁) M₁
  have h2 := H hRU 0 (r := 3) (by norm_num) h3 (by norm_num) hW0 hWT (G := fun _ => 0)
    aestronglyMeasurable_const (v := fun _ => 0) (w := fun _ => 0) aestronglyMeasurable_const
    aestronglyMeasurable_const (p := 3 / 2) (by norm_num) (by norm_num) (α := 0) (β := 0)
    (fun k _ x _ => by simp)
  obtain ⟨CP', hCP', H'⟩ := l2b_E1_cutoff (d := 2) (R * r₁) M₁
  obtain ⟨η, Bη, L, hηc, hη0, hη1, hηA, -, hηs⟩ := m1_exists_profile 2
  have h1 := H' hRU 0 (r := 3) (by norm_num) h3 (by norm_num) hW0 hWT hηc hηA hη0 hη1 hηs
    (p := 2) (q := 2) Real.HolderConjugate.two_two (f := fun _ => 0) (integrableOn_const ..)
    (fun ψ => by simp)
  trivial

end SuperdiffusionCLT.Section7
