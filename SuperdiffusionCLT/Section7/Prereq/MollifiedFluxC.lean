/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.MollifiedFlux
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareB

/-!
# Two elementary convolution estimates

For a nonnegative mollifier
`η` of integral one supported in the unit sup-ball, `η_h = h^{-d} η (·/h)`:

* `m1_conv_eLpNorm_le`, `m1_conv_cubeLpENorm_le`: the `L^q` contraction
  `‖η_h ∗ ψ‖_{L^q(V)} ≤ ‖ψ‖_{L^q(W)}` for `q ∈ [1, ∞)`, `W` containing the sup-balls of radius `h`
  around the points of `V` (Jensen's inequality for the weight `η_h`);
* `m1_sub_conv_eLpNorm_le`, `m1_sub_conv_cubeLpENorm_le`: the standard mollification estimate
  `‖ψ - η_h ∗ ψ‖_{L^q(V)} ≤ √d h ‖∇ψ‖_{L^q(W)}` for `ψ` with weak gradient on the open set `W`
  (the translation identity of `a10_translate_identity_dir`, then Jensen in the displacement and in
  the segment parameter).

The cube forms are at the scales `h = 3^n` on `□_n ⊂ □_{n+1}` with the normalized norms.
-/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped ENNReal


namespace SuperdiffusionCLT.Section7

/-- Jensen's inequality for a sub-probability weight, in the extended nonnegative reals. -/
theorem m1_jensen_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {K G : α → ℝ≥0∞}
    (hK : AEMeasurable K μ) (hG : AEMeasurable G μ) (hK1 : ∫⁻ a, K a ∂μ ≤ 1) {q : ℝ}
    (hq : 1 ≤ q) :
    (∫⁻ a, K a * G a ∂μ) ^ q ≤ ∫⁻ a, K a * G a ^ q ∂μ := by
  rcases hq.eq_or_lt with h1 | h1
  · rw [← h1]
    simp
  · have hq0 : 0 < q := by linarith only [h1]
    have hpq : (q.conjExponent).HolderConjugate q := (Real.HolderConjugate.conjExponent h1).symm
    set p : ℝ := q.conjExponent with hp
    have hsum : 1 / p + 1 / q = 1 := by
      rw [one_div, one_div]
      exact hpq.inv_add_inv_eq_one
    have hp0 : 0 ≤ 1 / p := by
      have := hpq.pos
      positivity
    have hq0' : 0 ≤ 1 / q := by positivity
    have hmul : ∀ a, K a ^ (1 / p) * (K a ^ (1 / q) * G a) = K a * G a := by
      intro a
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hp0 hq0', hsum, ENNReal.rpow_one]
    have hH : ∫⁻ a, K a * G a ∂μ ≤ (∫⁻ a, (K a ^ (1 / p)) ^ p ∂μ) ^ (1 / p) *
        (∫⁻ a, (K a ^ (1 / q) * G a) ^ q ∂μ) ^ (1 / q) := by
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := fun a => K a ^ (1 / p))
        (g := fun a => K a ^ (1 / q) * G a) (hK.pow_const _) ((hK.pow_const _).mul hG)
      simpa only [Pi.mul_apply, hmul] using this
    have hfp : ∀ a, (K a ^ (1 / p)) ^ p = K a := by
      intro a
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpq.pos.ne', ENNReal.rpow_one]
    have hgq : ∀ a, (K a ^ (1 / q) * G a) ^ q = K a * G a ^ q := by
      intro a
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
    simp only [hfp, hgq] at hH
    have h2 : (∫⁻ a, K a ∂μ) ^ (1 / p) ≤ 1 :=
      ENNReal.rpow_le_one hK1 hp0
    have h3 : ∫⁻ a, K a * G a ∂μ ≤ (∫⁻ a, K a * G a ^ q ∂μ) ^ (1 / q) := by
      calc _ ≤ _ := hH
        _ ≤ 1 * (∫⁻ a, K a * G a ^ q ∂μ) ^ (1 / q) := mul_le_mul_left h2 _
        _ = _ := one_mul _
    calc (∫⁻ a, K a * G a ∂μ) ^ q ≤ ((∫⁻ a, K a * G a ^ q ∂μ) ^ (1 / q)) ^ q :=
          ENNReal.rpow_le_rpow h3 hq0.le
      _ = _ := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]

variable {d : ℕ}

/-- A nonnegative normalized profile: nonnegative, continuous, supported in the unit sup-ball, of
integral one. -/
theorem m1_kernel_nonneg {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη0 : ∀ w, 0 ≤ η w) (w : Vec d) :
    0 ≤ a16_kernel d h η w :=
  mul_nonneg (pow_nonneg (inv_nonneg.mpr hh.le) d) (hη0 _)

/-- The integral of the scaled kernel equals the integral of the profile. -/
theorem m1_kernel_integral {h : ℝ} (hh : 0 < h) (η : Vec d → ℝ) :
    ∫ w, a16_kernel d h η w = ∫ w, η w := by
  unfold a16_kernel
  rw [integral_const_mul, Measure.integral_comp_smul (μ := (volume : Measure (Vec d)))
    (fun w => η w) h⁻¹]
  simp only [Module.finrank_fin_fun, smul_eq_mul, inv_inv, inv_pow]
  rw [abs_of_nonneg (pow_nonneg hh.le d)]
  field_simp

/-- The scaled kernel is integrable when the profile is. -/
theorem m1_kernel_integrable {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη : Integrable η volume) :
    Integrable (a16_kernel d h η) volume := by
  unfold a16_kernel
  exact (hη.comp_smul (inv_ne_zero hh.ne')).const_mul _

/-- The scaled kernel has lower integral one. -/
theorem m1_lintegral_kernel {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη0 : ∀ w, 0 ≤ η w)
    (hη1 : ∫ w, η w = 1) :
    ∫⁻ w, ENNReal.ofReal (a16_kernel d h η w) = 1 := by
  have hint : Integrable η volume := by
    by_contra hni
    rw [integral_undef hni] at hη1
    exact zero_ne_one hη1
  rw [← ofReal_integral_eq_lintegral_ofReal (m1_kernel_integrable hh hint)
    (Filter.Eventually.of_forall (m1_kernel_nonneg hh hη0)), m1_kernel_integral hh, hη1,
    ENNReal.ofReal_one]

/-- Pointwise bound of a mollification by the weighted lower integral of the modulus. -/
theorem m1_enorm_conv_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη0 : ∀ w, 0 ≤ η w)
    (ψ : Vec d → ℝ) (x : Vec d) :
    ‖∫ y, a16_kernel d h η (x - y) * ψ y‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (a16_kernel d h η (x - y)) * ‖ψ y‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  rw [enorm_mul, Real.enorm_of_nonneg (m1_kernel_nonneg hh hη0 _)]

/-- **The `L^q` contraction of the mollification**, lower-integral form: for a
nonnegative normalized profile, a measurable set `V` and a set `W` containing the sup-balls of radius
`h` around the points of `V`,
`∫_V |η_h ∗ ψ|^q ≤ ∫_W |ψ|^q`. -/
theorem m1_conv_lintegral_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {q : ℝ} (hq : 1 ≤ q) {ψ : Vec d → ℝ}
    (hψ : Measurable ψ) {V W : Set (Vec d)} (hV : MeasurableSet V)
    (hVW : ∀ x ∈ V, ∀ y, dist y x ≤ h → y ∈ W) :
    ∫⁻ x in V, ‖∫ y, a16_kernel d h η (x - y) * ψ y‖ₑ ^ q ≤ ∫⁻ y in W, ‖ψ y‖ₑ ^ q := by
  set K : Vec d → ℝ≥0∞ := fun w => ENNReal.ofReal (a16_kernel d h η w) with hK
  have hKm : Measurable K := (a16_kernel_continuous hηc).measurable.ennreal_ofReal
  have hK1 : ∫⁻ w, K w = 1 := m1_lintegral_kernel hh hη0 hη1
  have hq0 : 0 < q := by linarith only [hq]
  have step1 : ∀ x, ‖∫ y, a16_kernel d h η (x - y) * ψ y‖ₑ ^ q ≤
      ∫⁻ y, K (x - y) * ‖ψ y‖ₑ ^ q := by
    intro x
    refine (ENNReal.rpow_le_rpow (m1_enorm_conv_le hh hη0 ψ x) hq0.le).trans ?_
    refine (m1_jensen_lintegral (μ := volume) (K := fun y => K (x - y))
      (G := fun y => ‖ψ y‖ₑ) (hKm.comp (measurable_const.sub measurable_id)).aemeasurable
      hψ.enorm.aemeasurable ?_ hq)
    rw [lintegral_sub_left_eq_self (fun w => K w) x, hK1]
  have step2 : ∫⁻ x in V, ‖∫ y, a16_kernel d h η (x - y) * ψ y‖ₑ ^ q ≤
      ∫⁻ x in V, ∫⁻ y, K (x - y) * ‖ψ y‖ₑ ^ q := lintegral_mono step1
  refine step2.trans ?_
  have hmeas : Measurable (fun p : Vec d × Vec d => K (p.1 - p.2) * ‖ψ p.2‖ₑ ^ q) :=
    (hKm.comp (measurable_fst.sub measurable_snd)).mul
      ((hψ.comp measurable_snd).enorm.pow_const q)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hin : ∀ y, ∫⁻ x in V, K (x - y) * ‖ψ y‖ₑ ^ q ≤ W.indicator (fun y => ‖ψ y‖ₑ ^ q) y := by
    intro y
    have hKy : Measurable fun x : Vec d => K (x - y) := hKm.comp (measurable_id.sub measurable_const)
    rw [lintegral_mul_const _ hKy]
    by_cases hy : y ∈ W
    · rw [Set.indicator_of_mem hy]
      have : ∫⁻ x in V, K (x - y) ≤ 1 := by
        calc ∫⁻ x in V, K (x - y) ≤ ∫⁻ x, K (x - y) := setLIntegral_le_lintegral _ _
          _ = 1 := by rw [lintegral_sub_right_eq_self (fun w => K w) y, hK1]
      calc (∫⁻ x in V, K (x - y)) * ‖ψ y‖ₑ ^ q ≤ 1 * ‖ψ y‖ₑ ^ q := by gcongr
        _ = _ := one_mul _
    · rw [Set.indicator_of_notMem hy]
      have hz : ∫⁻ x in V, K (x - y) = 0 := by
        rw [setLIntegral_congr_fun hV (g := fun _ => 0) ?_, lintegral_zero]
        intro x hx
        simp only [hK]
        have hne : ¬ dist y x ≤ h := fun hd => hy (hVW x hx y hd)
        rw [dist_pi_le_iff hh.le] at hne
        push Not at hne
        obtain ⟨i, hi⟩ := hne
        rw [a16_kernel_eq_zero hh hηs (w := x - y) (i := i) ?_, ENNReal.ofReal_zero]
        rw [Real.dist_eq] at hi
        simpa only [Pi.sub_apply, abs_sub_comm] using hi
      rw [hz, zero_mul]
  calc ∫⁻ y, ∫⁻ x in V, K (x - y) * ‖ψ y‖ₑ ^ q ≤ ∫⁻ y, W.indicator (fun y => ‖ψ y‖ₑ ^ q) y :=
        lintegral_mono hin
    _ ≤ _ := lintegral_indicator_le _ _

/-- The `q`-th power of the increment along a segment, pointwise almost everywhere. -/
theorem m1_increment_le {W : Set (Vec d)} (hW : IsOpen W) {U : Vec d → ℝ}
    {G : Fin d → Vec d → ℝ} (hUm : Measurable U) (hGm : ∀ i, Measurable (G i))
    (hUl : LocallyIntegrable U volume) (hGl : ∀ i, LocallyIntegrable (G i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, U x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x)
    {q : ℝ} (hq : 1 ≤ q) (w : Vec d) :
    ∀ᵐ x : Vec d, (∀ s ∈ Icc (0 : ℝ) 1, x + s • w ∈ W) →
      ‖U (x + w) - U x‖ₑ ^ q ≤ ENNReal.ofReal (eucNorm w) ^ q *
        ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (eucNorm (fun i => G i (x + s • w))) ^ q := by
  have hGhm : Measurable fun y : Vec d => ∑ i, G i y * w i :=
    Finset.measurable_sum _ fun i _ => (hGm i).mul_const _
  have hGhl : LocallyIntegrable (fun y : Vec d => ∑ i, G i y * w i) volume :=
    locallyIntegrable_finsetSum _ fun i _ => by
      have e : (fun y : Vec d => G i y * w i) = w i • G i := by
        ext y
        simp [mul_comm]
      rw [e]
      exact (hGl i).smul _
  have hid := a10_translate_identity_dir hW hUm hGhm hUl hGhl w (a10_weak_dir hUl hGl hweak w)
  filter_upwards [hid] with x hx hxO
  rw [hx hxO]
  have hq0 : 0 < q := by linarith only [hq]
  have hnn : ∀ v : Vec d, 0 ≤ vecNormSq v := fun v => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hpt : ∀ s : ℝ, ‖∑ i, G i (x + s • w) * w i‖ₑ ≤
      ENNReal.ofReal (eucNorm w) * ENNReal.ofReal (eucNorm (fun i => G i (x + s • w))) := by
    intro s
    rw [← ENNReal.ofReal_mul (by unfold eucNorm; exact Real.sqrt_nonneg _),
      Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => G i (x + s • w)) (fun i => w i)
    have e1 : (∑ i, G i (x + s • w) * w i) ^ 2 ≤
        vecNormSq w * vecNormSq (fun i => G i (x + s • w)) := by
      refine hcs.trans (le_of_eq ?_)
      unfold vecNormSq vecDot
      simp only [sq]
      rw [mul_comm]
    unfold eucNorm
    rw [← Real.sqrt_mul (hnn w)]
    exact Real.abs_le_sqrt e1
  have h1 : ‖∫ s in Icc (0 : ℝ) 1, ∑ i, G i (x + s • w) * w i‖ₑ ≤
      ∫⁻ s in Icc (0 : ℝ) 1, ‖∑ i, G i (x + s • w) * w i‖ₑ := enorm_integral_le_lintegral_enorm _
  have hgm : Measurable fun s : ℝ => ENNReal.ofReal (eucNorm (fun i => G i (x + s • w))) := by
    refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
    unfold vecNormSq vecDot
    exact Finset.measurable_sum _ fun i _ => ((hGm i).comp (by fun_prop)).mul ((hGm i).comp (by fun_prop))
  have h2 : ∫⁻ s in Icc (0 : ℝ) 1, ‖∑ i, G i (x + s • w) * w i‖ₑ ≤
      ENNReal.ofReal (eucNorm w) *
        ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (eucNorm (fun i => G i (x + s • w))) := by
    rw [← lintegral_const_mul _ hgm]
    exact lintegral_mono hpt
  have hJ := m1_jensen_lintegral (μ := volume.restrict (Icc (0 : ℝ) 1)) (K := fun _ => 1)
    (G := fun s => ENNReal.ofReal (eucNorm (fun i => G i (x + s • w)))) aemeasurable_const
    hgm.aemeasurable (by simp) hq
  simp only [one_mul] at hJ
  calc ‖∫ s in Icc (0 : ℝ) 1, ∑ i, G i (x + s • w) * w i‖ₑ ^ q
      ≤ (ENNReal.ofReal (eucNorm w) *
        ∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (eucNorm (fun i => G i (x + s • w)))) ^ q :=
        ENNReal.rpow_le_rpow (h1.trans h2) (by linarith only [hq])
    _ = ENNReal.ofReal (eucNorm w) ^ q *
        (∫⁻ s in Icc (0 : ℝ) 1, ENNReal.ofReal (eucNorm (fun i => G i (x + s • w)))) ^ q :=
        ENNReal.mul_rpow_of_nonneg _ _ (by linarith only [hq])
    _ ≤ _ := by gcongr


theorem m1_measurable_eucNorm {g : Vec d → Vec d} (hg : ∀ i, Measurable fun x => g x i) :
    Measurable fun x => eucNorm (g x) := by
  refine Real.continuous_sqrt.measurable.comp ?_
  unfold vecNormSq vecDot
  exact Finset.measurable_sum _ fun i _ => (hg i).mul (hg i)

/-- The segment in the definition of the translate: `x - w + s w` is within sup-distance `h` of `x`
when `|w i| ≤ h` and `s ∈ [0, 1]`. -/
theorem m1_dist_segment_le {h : ℝ} (hh : 0 ≤ h) {w : Vec d} (hw : ∀ i, |w i| ≤ h) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (x : Vec d) : dist (x + (s • w - w)) x ≤ h := by
  rw [dist_pi_le_iff hh]
  intro i
  rw [Real.dist_eq]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  have h1 : s * w i - w i = -((1 - s) * w i) := by ring
  rw [h1, abs_neg, abs_mul, abs_of_nonneg (by linarith only [hs.2])]
  calc (1 - s) * |w i| ≤ 1 * |w i| :=
        mul_le_mul_of_nonneg_right (by linarith only [hs.1]) (abs_nonneg _)
    _ ≤ h := by rw [one_mul]; exact hw i

/-- The `L^q` modulus of continuity of a function with weak gradient, along a fixed displacement
`w` with `|w i| ≤ h`: `∫_V |ψ(x) - ψ(x - w)|^q ≤ |w|^q ∫_W |∇ψ|^q`. -/
theorem m1_translate_diff_lintegral_le {h : ℝ} (hh : 0 ≤ h) {W : Set (Vec d)} (hW : IsOpen W)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVW : ∀ x ∈ V, ∀ y, dist y x ≤ h → y ∈ W)
    {ψ : Vec d → ℝ} {g : Vec d → Vec d} (hψm : Measurable ψ) (hgm : ∀ i, Measurable fun x => g x i)
    (hψl : LocallyIntegrable ψ volume) (hgl : ∀ i, LocallyIntegrable (fun x => g x i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, ψ x * fderiv ℝ φ x (basisVec i) = -∫ x, g x i * φ x)
    {q : ℝ} (hq : 1 ≤ q) {w : Vec d} (hw : ∀ i, |w i| ≤ h) :
    ∫⁻ x in V, ‖ψ x - ψ (x - w)‖ₑ ^ q ≤
      ENNReal.ofReal (eucNorm w) ^ q * ∫⁻ y in W, ENNReal.ofReal (eucNorm (g y)) ^ q := by
  have hq0 : 0 < q := by linarith only [hq]
  have hA := m1_increment_le hW hψm (G := fun i y => g y i) hgm hψl hgl hweak hq w
  have hae := (measurePreserving_sub_right volume w).quasiMeasurePreserving.ae hA
  set Ψ : Vec d → ℝ≥0∞ := fun y => ENNReal.ofReal (eucNorm (g y)) ^ q with hΨ
  have hΨm : Measurable Ψ :=
    (ENNReal.measurable_ofReal.comp (m1_measurable_eucNorm hgm)).pow_const q
  have h1 : ∫⁻ x in V, ‖ψ x - ψ (x - w)‖ₑ ^ q ≤
      ∫⁻ x in V, ENNReal.ofReal (eucNorm w) ^ q * ∫⁻ s in Icc (0 : ℝ) 1, Ψ (x + (s • w - w)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hV] with x hx hxV
    have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x - w + s • w ∈ W := by
      intro s hs
      have := hVW x hxV _ (m1_dist_segment_le hh hw hs x)
      have e : x - w + s • w = x + (s • w - w) := by abel
      rwa [e]
    have := hx hseg
    simp only [sub_add_cancel] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun s => ?_
    have e : x - w + s • w = x + (s • w - w) := by abel
    simp only [hΨ, e]
  refine h1.trans ?_
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
  refine mul_le_mul' le_rfl ?_
  have hmeas : Measurable (fun p : Vec d × ℝ => Ψ (p.1 + (p.2 • w - w))) :=
    hΨm.comp (measurable_fst.add ((measurable_snd.smul_const w).sub measurable_const))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hin : ∀ s ∈ Icc (0 : ℝ) 1, ∫⁻ x in V, Ψ (x + (s • w - w)) ≤ ∫⁻ y in W, Ψ y := by
    intro s hs
    rw [← lintegral_indicator hV, ← lintegral_indicator hW.measurableSet]
    calc ∫⁻ x, V.indicator (fun x => Ψ (x + (s • w - w))) x
        ≤ ∫⁻ x, W.indicator Ψ (x + (s • w - w)) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ V
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hVW x hx _ (m1_dist_segment_le hh hw hs x))]
          · rw [Set.indicator_of_notMem hx]
            exact zero_le
      _ = ∫⁻ y, W.indicator Ψ y := lintegral_add_right_eq_self (fun y => W.indicator Ψ y) _
  calc ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ x in V, Ψ (x + (s • w - w))
      ≤ ∫⁻ s in Icc (0 : ℝ) 1, ∫⁻ y in W, Ψ y := setLIntegral_mono' measurableSet_Icc hin
    _ = ∫⁻ y in W, Ψ y := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        simp

/-- The kernel centered at `x` is integrable against a locally integrable function. -/
theorem m1_integrable_kernel_mul_loc {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ψ : Vec d → ℝ}
    (hψ : LocallyIntegrable ψ volume) (x : Vec d) :
    Integrable (fun y => a16_kernel d h η (x - y) * ψ y) volume := by
  have hφc : Continuous fun y => a16_kernel d h η (x - y) :=
    (a16_kernel_continuous hηc).comp (continuous_const.sub continuous_id)
  have hcomp : HasCompactSupport fun y => a16_kernel d h η (x - y) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x h) ?_
    intro y hy
    rw [Metric.mem_closedBall]
    by_contra hne
    rw [dist_pi_le_iff hh.le] at hne
    push Not at hne
    obtain ⟨i, hi⟩ := hne
    apply hy
    rw [Real.dist_eq] at hi
    exact a16_kernel_eq_zero hh hηs (w := x - y) (i := i) (by simpa only [Pi.sub_apply, abs_sub_comm] using hi)
  have := hψ.integrable_smul_left_of_hasCompactSupport hφc hcomp
  simpa only [smul_eq_mul] using this

/-- The difference `ψ x - η ∗ ψ x` as the average of the increments `ψ x - ψ (x - w)`. -/
theorem m1_sub_conv_eq {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ψ : Vec d → ℝ}
    (hψ : LocallyIntegrable ψ volume) (x : Vec d) :
    ψ x - ∫ y, a16_kernel d h η (x - y) * ψ y =
      ∫ w, a16_kernel d h η w * (ψ x - ψ (x - w)) := by
  have hint : Integrable η volume := by
    by_contra hni
    rw [integral_undef hni] at hη1
    exact zero_ne_one hη1
  have hk := m1_kernel_integrable hh hint
  have h1 : Integrable (fun w => a16_kernel d h η w * ψ x) volume := hk.mul_const _
  have h2 : Integrable (fun w => a16_kernel d h η w * ψ (x - w)) volume := by
    have := (m1_integrable_kernel_mul_loc hh hηc hηs hψ x).comp_sub_left x
    simpa only [sub_sub_cancel] using this
  have e1 : ∫ y, a16_kernel d h η (x - y) * ψ y = ∫ w, a16_kernel d h η w * ψ (x - w) := by
    rw [← integral_sub_left_eq_self (fun w => a16_kernel d h η w * ψ (x - w)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel]
  have e2 : ∫ w, a16_kernel d h η w * ψ x = ψ x := by
    rw [integral_mul_const, m1_kernel_integral hh, hη1, one_mul]
  simp only [mul_sub]
  rw [integral_sub h1 h2, e2, e1]

/-- **The standard mollification estimate**, lower-integral form:
`∫_V |ψ - η_h ∗ ψ|^q ≤ (√d h)^q ∫_W |∇ψ|^q` for `ψ` with weak gradient `g` on the open set `W`
containing the sup-balls of radius `h` around the points of `V`. -/
theorem m1_sub_conv_lintegral_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {W : Set (Vec d)} (hW : IsOpen W)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVW : ∀ x ∈ V, ∀ y, dist y x ≤ h → y ∈ W)
    {ψ : Vec d → ℝ} {g : Vec d → Vec d} (hψm : Measurable ψ) (hgm : ∀ i, Measurable fun x => g x i)
    (hψl : LocallyIntegrable ψ volume) (hgl : ∀ i, LocallyIntegrable (fun x => g x i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, ψ x * fderiv ℝ φ x (basisVec i) = -∫ x, g x i * φ x)
    {q : ℝ} (hq : 1 ≤ q) :
    ∫⁻ x in V, ‖ψ x - ∫ y, a16_kernel d h η (x - y) * ψ y‖ₑ ^ q ≤
      ENNReal.ofReal (Real.sqrt d * h) ^ q * ∫⁻ y in W, ENNReal.ofReal (eucNorm (g y)) ^ q := by
  set K : Vec d → ℝ≥0∞ := fun w => ENNReal.ofReal (a16_kernel d h η w) with hK
  have hKm : Measurable K := (a16_kernel_continuous hηc).measurable.ennreal_ofReal
  have hK1 : ∫⁻ w, K w = 1 := m1_lintegral_kernel hh hη0 hη1
  have hq0 : 0 < q := by linarith only [hq]
  set Gq : ℝ≥0∞ := ∫⁻ y in W, ENNReal.ofReal (eucNorm (g y)) ^ q with hGq
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt d * h) ^ q with hc
  have s1 : ∀ x, ‖ψ x - ∫ y, a16_kernel d h η (x - y) * ψ y‖ₑ ^ q ≤
      ∫⁻ w, K w * ‖ψ x - ψ (x - w)‖ₑ ^ q := by
    intro x
    rw [m1_sub_conv_eq hh hηc hη1 hηs hψl x]
    have h1 : ‖∫ w, a16_kernel d h η w * (ψ x - ψ (x - w))‖ₑ ≤
        ∫⁻ w, K w * ‖ψ x - ψ (x - w)‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun w => ?_
      rw [enorm_mul, Real.enorm_of_nonneg (m1_kernel_nonneg hh hη0 _)]
    refine (ENNReal.rpow_le_rpow h1 hq0.le).trans ?_
    exact m1_jensen_lintegral (μ := volume) (K := K) (G := fun w => ‖ψ x - ψ (x - w)‖ₑ)
      hKm.aemeasurable ((measurable_const.sub (hψm.comp (measurable_const.sub measurable_id))).enorm.aemeasurable) (le_of_eq hK1) hq
  have hmeas : Measurable (fun p : Vec d × Vec d => K p.2 * ‖ψ p.1 - ψ (p.1 - p.2)‖ₑ ^ q) :=
    (hKm.comp measurable_snd).mul
      (((hψm.comp measurable_fst).sub (hψm.comp (measurable_fst.sub measurable_snd))).enorm.pow_const q)
  have s2 : ∫⁻ x in V, ‖ψ x - ∫ y, a16_kernel d h η (x - y) * ψ y‖ₑ ^ q ≤
      ∫⁻ w, K w * ∫⁻ x in V, ‖ψ x - ψ (x - w)‖ₑ ^ q := by
    refine (lintegral_mono s1).trans (le_of_eq ?_)
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    refine lintegral_congr fun w => ?_
    rw [lintegral_const_mul]
    exact ((hψm.sub (hψm.comp (measurable_id.sub measurable_const))).enorm.pow_const q)
  refine s2.trans ?_
  have s3 : ∀ w, K w * ∫⁻ x in V, ‖ψ x - ψ (x - w)‖ₑ ^ q ≤ K w * (c * Gq) := by
    intro w
    by_cases hKw : K w = 0
    · rw [hKw, zero_mul, zero_mul]
    · have hw : ∀ i, |w i| ≤ h := by
        intro i
        by_contra hlt
        push Not at hlt
        apply hKw
        simp only [hK]
        rw [a16_kernel_eq_zero hh hηs (w := w) (i := i) hlt, ENNReal.ofReal_zero]
      refine mul_le_mul' le_rfl ?_
      refine (m1_translate_diff_lintegral_le hh.le hW hV hVW hψm hgm hψl hgl hweak hq hw).trans ?_
      refine mul_le_mul' ?_ le_rfl
      refine ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_) hq0.le
      unfold eucNorm
      calc Real.sqrt (vecNormSq w) ≤ Real.sqrt ((d : ℝ) * h ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            unfold vecNormSq vecDot
            calc ∑ i, w i * w i ≤ ∑ _i : Fin d, h ^ 2 := by
                  refine Finset.sum_le_sum fun i _ => ?_
                  have := sq_le_sq' (abs_le.mp (hw i)).1 (abs_le.mp (hw i)).2
                  nlinarith only [this]
              _ = (d : ℝ) * h ^ 2 := by simp
        _ = Real.sqrt d * h := by
            rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hh.le]
  calc ∫⁻ w, K w * ∫⁻ x in V, ‖ψ x - ψ (x - w)‖ₑ ^ q ≤ ∫⁻ w, K w * (c * Gq) := lintegral_mono s3
    _ = c * Gq := by
        rw [lintegral_mul_const _ hKm, hK1, one_mul]

/-- The mollification of a measurable function is measurable. -/
theorem m1_measurable_conv {h : ℝ} {η : Vec d → ℝ} (hηc : Continuous η) {ψ : Vec d → ℝ}
    (hψ : Measurable ψ) : Measurable fun x => ∫ y, a16_kernel d h η (x - y) * ψ y := by
  have hm : Measurable (fun p : Vec d × Vec d => a16_kernel d h η (p.1 - p.2) * ψ p.2) :=
    ((a16_kernel_continuous hηc).measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hψ.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

/-- Passage from a lower-integral inequality to `L^q` norms. -/
theorem m1_eLpNorm_le_of_lintegral_le {q : ℝ} (hq : 1 ≤ q) {μ ν : Measure (Vec d)}
    {F G : Vec d → ℝ} (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G ν)
    {c : ℝ≥0∞} (H : ∫⁻ x, ‖F x‖ₑ ^ q ∂μ ≤ c ^ q * ∫⁻ x, ‖G x‖ₑ ^ q ∂ν) :
    eLpNorm F (ENNReal.ofReal q) μ ≤ c * eLpNorm G (ENNReal.ofReal q) ν := by
  have hq0 : 0 < q := by linarith only [hq]
  have h0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have h1 : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h0 h1 hF, eLpNorm_eq_lintegral_rpow_enorm_toReal h0 h1 hG,
    ENNReal.toReal_ofReal hq0.le]
  have hqi : 0 ≤ 1 / q := by positivity
  calc (∫⁻ x, ‖F x‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (c ^ q * ∫⁻ x, ‖G x‖ₑ ^ q ∂ν) ^ (1 / q) :=
        ENNReal.rpow_le_rpow H hqi
    _ = c * (∫⁻ x, ‖G x‖ₑ ^ q ∂ν) ^ (1 / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hqi, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne',
          ENNReal.rpow_one]

/-- **The `L^q` contraction of the mollification**: for a nonnegative normalized
mollifier, `‖η_h ∗ ψ‖_{L^q(V)} ≤ ‖ψ‖_{L^q(W)}` when `W` contains the sup-balls of radius `h`
around the points of `V`. -/
theorem m1_conv_eLpNorm_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {q : ℝ} (hq : 1 ≤ q) {ψ : Vec d → ℝ}
    (hψ : Measurable ψ) {V W : Set (Vec d)} (hV : MeasurableSet V)
    (hVW : ∀ x ∈ V, ∀ y, dist y x ≤ h → y ∈ W) :
    eLpNorm (fun x => ∫ y, a16_kernel d h η (x - y) * ψ y) (ENNReal.ofReal q)
        (volume.restrict V) ≤ eLpNorm ψ (ENNReal.ofReal q) (volume.restrict W) := by
  have := m1_eLpNorm_le_of_lintegral_le hq (μ := volume.restrict V) (ν := volume.restrict W)
    (F := fun x => ∫ y, a16_kernel d h η (x - y) * ψ y) (G := ψ)
    (m1_measurable_conv hηc hψ).aestronglyMeasurable hψ.aestronglyMeasurable
    (c := 1) (by
      rw [ENNReal.one_rpow, one_mul]
      exact m1_conv_lintegral_le hh hηc hη0 hη1 hηs hq hψ hV hVW)
  simpa only [one_mul] using this

/-- **The standard mollification estimate**, `L^q` form: for `ψ` with weak gradient `g`
on the open set `W` containing the sup-balls of radius `h` around the points of `V`,
`‖ψ - η_h ∗ ψ‖_{L^q(V)} ≤ √d h ‖∇ψ‖_{L^q(W)}`. -/
theorem m1_sub_conv_eLpNorm_le {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {W : Set (Vec d)} (hW : IsOpen W)
    {V : Set (Vec d)} (hV : MeasurableSet V) (hVW : ∀ x ∈ V, ∀ y, dist y x ≤ h → y ∈ W)
    {ψ : Vec d → ℝ} {g : Vec d → Vec d} (hψm : Measurable ψ) (hgm : ∀ i, Measurable fun x => g x i)
    (hψl : LocallyIntegrable ψ volume) (hgl : ∀ i, LocallyIntegrable (fun x => g x i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W → ∫ x, ψ x * fderiv ℝ φ x (basisVec i) = -∫ x, g x i * φ x)
    {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun x => ψ x - ∫ y, a16_kernel d h η (x - y) * ψ y) (ENNReal.ofReal q)
        (volume.restrict V) ≤
      ENNReal.ofReal (Real.sqrt d * h) *
        eLpNorm (fun y => eucNorm (g y)) (ENNReal.ofReal q) (volume.restrict W) := by
  refine m1_eLpNorm_le_of_lintegral_le hq (μ := volume.restrict V) (ν := volume.restrict W)
    (F := fun x => ψ x - ∫ y, a16_kernel d h η (x - y) * ψ y) (G := fun y => eucNorm (g y))
    (hψm.sub (m1_measurable_conv hηc hψm)).aestronglyMeasurable
    (m1_measurable_eucNorm hgm).aestronglyMeasurable ?_
  have := m1_sub_conv_lintegral_le hh hηc hη0 hη1 hηs hW hV hVW hψm hgm hψl hgl hweak hq
  refine this.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun y => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (show 0 ≤ eucNorm (g y) from Real.sqrt_nonneg _)]

/-- The sup-ball of radius `3^n` around a point of the open cube `□_n` lies in the open cube
`□_{n+1}`. -/
theorem m1_ball_subset_open (n : ℕ) {x : Vec d} (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    ∀ y, dist y x ≤ (3 : ℝ) ^ (n : ℤ) → y ∈ openCubeSet (originCube d ((n + 1 : ℕ) : ℤ)) := by
  intro y hy
  have hh : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hyi : |y i - x i| ≤ (3 : ℝ) ^ (n : ℤ) := by
    have := (dist_pi_le_iff hh.le).1 hy i
    rwa [Real.dist_eq] at this
  rw [abs_le] at hyi
  obtain ⟨hx1, hx2⟩ := hx i
  have h3 : (3 : ℝ) ^ (((n + 1 : ℕ) : ℤ)) = 3 * (3 : ℝ) ^ (n : ℤ) := by
    rw [Nat.cast_succ, zpow_add_one₀ (by norm_num), mul_comm]
  rw [h3]
  constructor <;> nlinarith only [hyi.1, hyi.2, hx1, hx2]

/-- The normalized `L^q` norm on a cube is the normalized restricted norm on the open cube. -/
theorem m1_cubeLpENorm_eq (Q : TriadicCube d) {q : ℝ} (hq : 0 < q) (f : Vec d → ℝ) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q (ENNReal.ofReal q) f =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / q) *
        eLpNorm f (ENNReal.ofReal q) (volume.restrict (openCubeSet Q)) := by
  unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm
  have h1 : (1 / ENNReal.ofReal q).toReal = 1 / q := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le, one_div]
  rw [normalizedCubeMeasure_eq_smul, eLpNorm_smul_measure_of_ne_zero (by
      simpa using cubeVolume_pos Q), h1, smul_eq_mul]

theorem m1_cubeVolume_succ (n : ℕ) :
    cubeVolume (originCube d ((n + 1 : ℕ) : ℤ)) = 3 ^ d * cubeVolume (originCube d (n : ℤ)) := by
  rw [cubeVolume_eq_scaleFactor_pow, cubeVolume_eq_scaleFactor_pow, ← mul_pow]
  congr 1
  unfold cubeScaleFactor originCube
  simp only
  rw [Nat.cast_succ, zpow_add_one₀ (by norm_num), mul_comm]

/-- **`L^q` contraction on cubes**: `‖η_n ∗ ψ‖_{L̲^q(□_n)} ≤ 3^{d/q} ‖ψ‖_{L̲^q(□_{n+1})}`. -/
theorem m1_conv_cubeLpENorm_le (n : ℕ) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {q : ℝ} (hq : 1 ≤ q) {ψ : Vec d → ℝ}
    (hψ : Measurable ψ) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) (ENNReal.ofReal q)
        (fun x => ∫ y, a16_kernel d ((3 : ℝ) ^ (n : ℤ)) η (x - y) * ψ y) ≤
      ENNReal.ofReal (3 ^ d) ^ (1 / q) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d ((n + 1 : ℕ) : ℤ))
          (ENNReal.ofReal q) ψ := by
  have hq0 : 0 < q := by linarith only [hq]
  have hh : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  have hmain := m1_conv_eLpNorm_le hh hηc hη0 hη1 hηs hq hψ (measurableSet_openCubeSet _)
    (fun x hx y hy => m1_ball_subset_open n hx y hy)
  have hv := cubeVolume_pos (originCube d (n : ℤ))
  have e : ENNReal.ofReal ((cubeVolume (originCube d (n : ℤ)))⁻¹) =
      ENNReal.ofReal (3 ^ d) * ENNReal.ofReal ((3 ^ d * cubeVolume (originCube d (n : ℤ)))⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [m1_cubeLpENorm_eq _ hq0, m1_cubeLpENorm_eq _ hq0, m1_cubeVolume_succ, e,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), mul_assoc]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hmain)

/-- **The standard mollification estimate on cubes**:
`‖ψ - η_n ∗ ψ‖_{L̲^q(□_n)} ≤ 3^{d/q} √d 3^n ‖∇ψ‖_{L̲^q(□_{n+1})}`, for `ψ` with weak gradient `g`
on the open cube `□_{n+1}`. -/
theorem m1_sub_conv_cubeLpENorm_le (n : ℕ) {η : Vec d → ℝ} (hηc : Continuous η)
    (hη0 : ∀ w, 0 ≤ η w) (hη1 : ∫ w, η w = 1)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {ψ : Vec d → ℝ} {g : Vec d → Vec d}
    (hψm : Measurable ψ) (hgm : ∀ i, Measurable fun x => g x i)
    (hψl : LocallyIntegrable ψ volume) (hgl : ∀ i, LocallyIntegrable (fun x => g x i) volume)
    (hweak : ∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ openCubeSet (originCube d ((n + 1 : ℕ) : ℤ)) →
        ∫ x, ψ x * fderiv ℝ φ x (basisVec i) = -∫ x, g x i * φ x)
    {q : ℝ} (hq : 1 ≤ q) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) (ENNReal.ofReal q)
        (fun x => ψ x - ∫ y, a16_kernel d ((3 : ℝ) ^ (n : ℤ)) η (x - y) * ψ y) ≤
      ENNReal.ofReal (3 ^ d) ^ (1 / q) * ENNReal.ofReal (Real.sqrt d * (3 : ℝ) ^ (n : ℤ)) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d ((n + 1 : ℕ) : ℤ))
          (ENNReal.ofReal q) (fun y => eucNorm (g y)) := by
  have hq0 : 0 < q := by linarith only [hq]
  have hh : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
  have hmain := m1_sub_conv_eLpNorm_le hh hηc hη0 hη1 hηs (isOpen_openCubeSet _)
    (measurableSet_openCubeSet _) (fun x hx y hy => m1_ball_subset_open n hx y hy) hψm hgm hψl hgl
    hweak hq
  have hv := cubeVolume_pos (originCube d (n : ℤ))
  have e : ENNReal.ofReal ((cubeVolume (originCube d (n : ℤ)))⁻¹) =
      ENNReal.ofReal (3 ^ d) * ENNReal.ofReal ((3 ^ d * cubeVolume (originCube d (n : ℤ)))⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [m1_cubeLpENorm_eq _ hq0, m1_cubeLpENorm_eq _ hq0, m1_cubeVolume_succ, e,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  calc _ ≤ (ENNReal.ofReal (3 ^ d) ^ (1 / q) *
        ENNReal.ofReal ((3 ^ d * cubeVolume (originCube d (n : ℤ)))⁻¹) ^ (1 / q)) *
        (ENNReal.ofReal (Real.sqrt d * (3 : ℝ) ^ (n : ℤ)) *
          eLpNorm (fun y => eucNorm (g y)) (ENNReal.ofReal q)
            (volume.restrict (openCubeSet (originCube d ((n + 1 : ℕ) : ℤ))))) :=
        mul_le_mul' le_rfl hmain
    _ = _ := by ring

/-- A nonnegative normalized Lipschitz mollifier profile supported in the unit sup-ball: the tent
function divided by its integral. -/
theorem m1_exists_profile (d : ℕ) :
    ∃ (η : Vec d → ℝ) (A : ℝ) (L : NNReal), Continuous η ∧ (∀ w, 0 ≤ η w) ∧ ∫ w, η w = 1 ∧
      (∀ w, |η w| ≤ A) ∧ LipschitzWith L η ∧ (∀ w, (∃ i, 1 < |w i|) → η w = 0) := by
  set t : Vec d → ℝ := fun w => max 0 (1 - ‖w‖) with ht
  have htc : Continuous t := continuous_const.max (continuous_const.sub continuous_norm)
  have ht0 : ∀ w, 0 ≤ t w := fun w => le_max_left _ _
  have hts : ∀ w, (∃ i, 1 < |w i|) → t w = 0 := by
    intro w ⟨i, hi⟩
    have : 1 < ‖w‖ := lt_of_lt_of_le hi (by
      rw [← Real.norm_eq_abs]
      exact norm_le_pi_norm w i)
    exact max_eq_left (by linarith only [this])
  have htcs : HasCompactSupport t := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Vec d) 1) ?_
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hne
    apply hw
    exact max_eq_left (by linarith only [not_le.mp hne])
  have hti : Integrable t volume := htc.integrable_of_hasCompactSupport htcs
  have htle : ∀ w, t w ≤ 1 := fun w => max_le (by norm_num) (by linarith only [norm_nonneg w])
  have hpos : 0 < ∫ w, t w := by
    rw [integral_pos_iff_support_of_nonneg ht0 hti]
    have hopen : IsOpen (Function.support t) := htc.isOpen_support
    refine hopen.measure_pos volume ⟨0, ?_⟩
    simp [ht]
  set I : ℝ := ∫ w, t w with hI
  have hLt : LipschitzWith 1 t := by
    refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    rw [ht]
    simp only
    rw [max_comm 0, max_comm 0 (1 - ‖w'‖)]
    calc |max (1 - ‖w‖) 0 - max (1 - ‖w'‖) 0| ≤ |(1 - ‖w‖) - (1 - ‖w'‖)| :=
          abs_max_sub_max_le_abs _ _ _
      _ = |‖w'‖ - ‖w‖| := by ring_nf
      _ ≤ ‖w - w'‖ := by rw [abs_sub_comm]; exact abs_norm_sub_norm_le w w'
  refine ⟨fun w => I⁻¹ * t w, I⁻¹, ⟨I⁻¹, by positivity⟩, continuous_const.mul htc,
    fun w => mul_nonneg (inv_nonneg.2 hpos.le) (ht0 w), ?_, fun w => ?_, ?_, fun w hw => ?_⟩
  · rw [integral_const_mul, ← hI, inv_mul_cancel₀ hpos.ne']
  · rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hpos.le) (ht0 w))]
    calc I⁻¹ * t w ≤ I⁻¹ * 1 := mul_le_mul_of_nonneg_left (htle w) (inv_nonneg.2 hpos.le)
      _ = I⁻¹ := mul_one _
  · refine LipschitzWith.of_dist_le_mul fun w w' => ?_
    have h1 := hLt.dist_le_mul w w'
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at h1
    rw [Real.dist_eq]
    show |I⁻¹ * t w - I⁻¹ * t w'| ≤ I⁻¹ * dist w w'
    rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.2 hpos.le)]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
  · show I⁻¹ * t w = 0
    rw [hts w hw, mul_zero]

/-- The constant function `1` has weak gradient `0` on every open set. -/
theorem m1_weak_const (i : Fin d) (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, (fun _ : Vec d => (1 : ℝ)) x * fderiv ℝ φ x (basisVec i) =
      -∫ x, (fun _ : Vec d => (0 : ℝ)) x * φ x := by
  have hcont : Continuous fun x => fderiv ℝ φ x (basisVec i) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcomp : HasCompactSupport fun x => fderiv ℝ φ x (basisVec i) := hφc.fderiv_apply ℝ (basisVec i)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vec d)))
    (f := fun _ : Vec d => (1 : ℝ)) (g := φ) (v := basisVec i)
    (by simp)
    (by simpa using hcont.integrable_of_hasCompactSupport hcomp)
    (by simpa using hφ.continuous.integrable_of_hasCompactSupport hφc)
    (fun x _ => differentiableAt_const _) (fun x _ => hφ.differentiable (by simp) x)
  simpa using h

/-- Satisfiability witness for `m1_conv_cubeLpENorm_le` and `m1_sub_conv_cubeLpENorm_le`
(`d = 2`, `n = 0`, `q = 2`): the normalized tent profile, the constant function `1`, with weak
gradient `0`; every hypothesis is met and both estimates hold for these data. -/
example : ∃ η : Vec 2 → ℝ, Continuous η ∧ (∀ w, 0 ≤ η w) ∧ ∫ w, η w = 1 ∧
    (∀ w, (∃ i, 1 < |w i|) → η w = 0) ∧
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 ((0 : ℕ) : ℤ)) (ENNReal.ofReal 2)
        (fun x => ∫ y, a16_kernel 2 ((3 : ℝ) ^ ((0 : ℕ) : ℤ)) η (x - y) * (fun _ : Vec 2 => (1 : ℝ)) y) ≤
      ENNReal.ofReal (3 ^ 2) ^ (1 / (2 : ℝ)) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 ((0 + 1 : ℕ) : ℤ))
          (ENNReal.ofReal 2) (fun _ : Vec 2 => (1 : ℝ)) ∧
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 ((0 : ℕ) : ℤ)) (ENNReal.ofReal 2)
        (fun x => (fun _ : Vec 2 => (1 : ℝ)) x -
          ∫ y, a16_kernel 2 ((3 : ℝ) ^ ((0 : ℕ) : ℤ)) η (x - y) * (fun _ : Vec 2 => (1 : ℝ)) y) ≤
      ENNReal.ofReal (3 ^ 2) ^ (1 / (2 : ℝ)) * ENNReal.ofReal (Real.sqrt (2 : ℕ) * (3 : ℝ) ^ ((0 : ℕ) : ℤ)) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube 2 ((0 + 1 : ℕ) : ℤ))
          (ENNReal.ofReal 2) (fun y => eucNorm ((fun _ : Vec 2 => (0 : Vec 2)) y)) := by
  obtain ⟨η, _, _, hηc, hη0, hη1, -, -, hηs⟩ := m1_exists_profile 2
  refine ⟨η, hηc, hη0, hη1, hηs, ?_, ?_⟩
  · exact m1_conv_cubeLpENorm_le 0 hηc hη0 hη1 hηs (q := 2) (by norm_num) measurable_const
  · exact m1_sub_conv_cubeLpENorm_le 0 hηc hη0 hη1 hηs (g := fun _ => 0) measurable_const
      (fun i => measurable_const) (locallyIntegrable_const _) (fun i => locallyIntegrable_const _)
      (fun i φ hφ hφc _ => m1_weak_const i φ hφ hφc) (q := 2) (by norm_num)

end SuperdiffusionCLT.Section7
