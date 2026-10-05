/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Homogenization.Sobolev.W1p.GlobalMollifierLp
public import SuperdiffusionCLT.Section7.Analytic.Geometry.LayerPoincare
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Boundary-layer Poincare inequality for zero-trace functions

`Section7.layerPoincare_local`: the chart estimate for `ψ ∈ H¹₀(U)` and every `q ≥ 1`, obtained by
mollifying the zero extension of `ψ` (the mollified function vanishes above the graph shifted by
`κ a`), applying the chart lemma, bounding the mollified gradient by the localized Young
inequality, and passing to an almost-everywhere limit by Fatou.
-/

@[expose] public section

open MeasureTheory Homogenization Convolution Filter
open scoped ENNReal Topology

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem layerPoincare_enorm_gradient_rpow {U : Set (Vec d)} (ψ : H10Function U) {q : ℝ}
    (hq : 0 < q) (w : Vec d) :
    ‖(d : ℝ) * ‖ψ.zeroExtensionGrad w‖‖ₑ ^ q =
      ENNReal.ofReal d ^ q * U.indicator (fun w => ‖ψ.toH1Function.grad w‖ₑ ^ q) w := by
  by_cases hw : w ∈ U
  · rw [Set.indicator_of_mem hw, ψ.zeroExtensionGrad_apply_of_mem hw, enorm_mul, enorm_norm,
      Real.enorm_of_nonneg (Nat.cast_nonneg d), ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  · rw [Set.indicator_of_notMem hw, ψ.zeroExtensionGrad_apply_of_not_mem hw]
    simp [ENNReal.zero_rpow_of_pos hq]

/-- If `w - t'` leaves `U` for every `‖t'‖ ≤ a`, the mollified zero extension vanishes at `w`. -/
theorem layerPoincare_mollified_eq_zero {U : Set (Vec d)} {x' : Vec d} {r R : ℝ} {e : Vec d}
    (he : vecNormSq e = 1) {γ : Vec d → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) {M₁ : ℝ}
    (hb : ∀ y, ‖fderiv ℝ γ y‖ ≤ M₁)
    (hch : ∀ y ∈ Metric.ball x' r, (y ∈ U ↔ vecDot e y < γ (y - vecDot e y • e)))
    {ρ : Vec d → ℝ} (hρ : IsConvexApproxKernel ρ) {a : ℝ} (ha : 0 < a) (ψ : H10Function U)
    (hRa : R + a ≤ r) {w : Vec d} (hw : w ∈ Metric.ball x' R)
    (hz : γ (w - vecDot e w • e) + ((d : ℝ) + (1 + d) * M₁) * a ≤ vecDot e w) :
    (scaledConvexApproxKernel ρ a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ.zeroExtension) w
      = 0 := by
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  refine convolution_eq_zero_of_far (a := a)
    (fun t ht => scaledKernel_ne_zero_norm_le hρ ha ht) fun t ht => ?_
  refine ψ.zeroExtension_apply_of_not_mem fun hmem => ?_
  have hwb : ‖w - x'‖ < R := by simpa [dist_eq_norm] using hw
  have hw'b : w - t ∈ Metric.ball x' r := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖w - t - x'‖ = ‖(w - x') - t‖ := by congr 1; abel
      _ ≤ ‖w - x'‖ + ‖t‖ := norm_sub_le _ _
      _ < r := by linarith only [hwb, ht, hRa]
  have h1 := (hch _ hw'b).1 hmem
  have h2 := abs_vecDot_le he t
  have h3 := abs_proj_comp_sub_le he hγ hb w (w - t)
  have h4 : ‖w - (w - t)‖ = ‖t‖ := by congr 1; abel
  rw [h4] at h3
  have hv := vecDot_sub e w t
  have h5 := (abs_le.1 h2).2
  have h6 := (abs_le.1 h3).1
  have h7 : (1 + (d : ℝ)) * M₁ * ‖t‖ ≤ (1 + (d : ℝ)) * M₁ * a :=
    mul_le_mul_of_nonneg_left ht (by positivity)
  have h8 : (d : ℝ) * ‖t‖ ≤ d * a := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg d)
  have h9 : γ (w - vecDot e w • e) + ((d : ℝ) + (1 + d) * M₁) * a =
      γ (w - vecDot e w • e) + d * a + (1 + (d : ℝ)) * M₁ * a := by ring
  linarith only [h1, hv, h5, h6, h7, h8, h9, hz]

theorem layerPoincare_memLp_gradNorm {Du : Vec d → Vec d}
    (hDu : ∀ i, MemLp (fun x => Du x i) 2 volume) :
    MemLp (fun x => (d : ℝ) * ‖Du x‖) 2 volume := by
  have hs : MemLp (fun x => ∑ i, ‖Du x i‖) 2 volume :=
    memLp_finsetSum Finset.univ fun i _ => (hDu i).norm
  have hmeas : AEStronglyMeasurable Du volume :=
    (aemeasurable_pi_iff.2 fun i => (hDu i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  refine (hs.const_mul (d : ℝ)).mono' (hmeas.norm.const_mul _) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i => ?_
  exact Finset.single_le_sum (f := fun j => ‖Du x j‖) (fun j _ => norm_nonneg _)
    (Finset.mem_univ i)

/-- **The local estimate for `ψ ∈ H¹₀(U)`** in a `C^{1,1}` chart: for every `q ≥ 1`, with
`κ = d + (1 + d) M₁` and `A ⊆ U ∩ B(x', 2t)`,
`∫_A |ψ|^q ≤ (3 κ t d)^q ∫_{B(x', (3κ+4) t) ∩ U} |∇ψ|^q`. -/
theorem layerPoincare_local {U : Set (Vec d)} (hU : IsOpen U) (ψ : H10Function U)
    {x' : Vec d} (hx' : x' ∈ frontier U) {r : ℝ} {e : Vec d} (he : vecNormSq e = 1)
    {γ : Vec d → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) {M₁ : ℝ} (hb : ∀ y, ‖fderiv ℝ γ y‖ ≤ M₁)
    (hch : ∀ y ∈ Metric.ball x' r, (y ∈ U ↔ vecDot e y < γ (y - vecDot e y • e)))
    {q : ℝ} (hq : 1 ≤ q) {t : ℝ} (ht : 0 < t)
    (hr : (3 * ((d : ℝ) + (1 + d) * M₁) + 4) * t ≤ r)
    {A : Set (Vec d)} (hA : MeasurableSet A) (hAU : A ⊆ U)
    (hAb : A ⊆ Metric.ball x' (2 * t)) :
    ∫⁻ y in A, ‖ψ.toH1Function.toFun y‖ₑ ^ q ≤
      ENNReal.ofReal (3 * ((d : ℝ) + (1 + d) * M₁) * t) ^ q * ENNReal.ofReal d ^ q *
        ∫⁻ w in Metric.closedBall x' ((3 * ((d : ℝ) + (1 + d) * M₁) + 4) * t),
          U.indicator (fun w => ‖ψ.toH1Function.grad w‖ₑ ^ q) w := by
  have hq0 : 0 < q := by linarith only [hq]
  set κ : ℝ := (d : ℝ) + (1 + d) * M₁ with hκ
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb 0)
  have hκ0 : 0 ≤ κ := by positivity
  have hmeasU : MeasurableSet U := hU.measurableSet
  set u0 := ψ.zeroExtension with hu0def
  set Du := ψ.zeroExtensionGrad with hDudef
  have hw : HasWeakGradientOn Set.univ u0 Du := ψ.hasWeakGradientOn_univ_zeroExtension hmeasU
  have hu0 : MemLp u0 2 volume := ψ.memLp_zeroExtension hmeasU ψ.toH1Function.memL2
  have hDu : ∀ i, MemLp (fun x => Du x i) 2 volume := by
    intro i
    have := ψ.gradMemLp_zeroExtensionGrad hmeasU ψ.toH1Function.gradMemL2 i
    simpa only [MemLpOn, Measure.restrict_univ] using this
  have hG : MemLp (fun x => (d : ℝ) * ‖Du x‖) 2 volume := layerPoincare_memLp_gradNorm hDu
  have hu0loc : LocallyIntegrable u0 volume := hu0.locallyIntegrable (by norm_num)
  have hDuLoc : ∀ i, LocallyIntegrable (fun x => Du x i) volume := fun i =>
    (hDu i).locallyIntegrable (by norm_num)
  have hGloc : LocallyIntegrable (fun x => (d : ℝ) * ‖Du x‖) volume :=
    hG.locallyIntegrable (by norm_num)
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hεpos : ∀ n, 0 < unitConvexApproxScale n := fun n => by
    simp only [unitConvexApproxScale]; positivity
  have hconv := tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel hρ
    (p := 2) (g := u0) (by norm_num) (by simp) hu0 ht tendsto_unitConvexApproxScale_zero
    (Filter.Eventually.of_forall hεpos)
  have hmeasure : TendstoInMeasure volume (fun n x =>
      (scaledConvexApproxKernel unitConvexApproxKernel (unitConvexApproxScale n * t) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] u0) x) Filter.atTop u0 :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, -, hae⟩ := hmeasure.exists_seq_tendsto_ae
  set Rad : ℝ := (3 * κ + 4) * t with hRad
  set R : ℝ := 3 * (1 + κ) * t with hRdef
  set B : ℝ≥0∞ := ENNReal.ofReal (3 * κ * t) ^ q * ENNReal.ofReal d ^ q *
    ∫⁻ w in Metric.closedBall x' Rad,
      U.indicator (fun w => ‖ψ.toH1Function.grad w‖ₑ ^ q) w with hB
  set g : ℕ → Vec d → ℝ := fun n =>
    scaledConvexApproxKernel unitConvexApproxKernel (unitConvexApproxScale n * t) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] u0 with hgdef
  have hgsm : ∀ n, ContDiff ℝ 1 (g n) := by
    intro n
    have ha : 0 < unitConvexApproxScale n * t := mul_pos (hεpos n) ht
    have hk : ContDiff ℝ (⊤ : ℕ∞)
        (scaledConvexApproxKernel unitConvexApproxKernel (unitConvexApproxScale n * t)) :=
      contDiff_scaledConvexApproxKernel hρ _
    have hkc := hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
    exact (HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hkc hk
      hu0loc).of_le (by exact_mod_cast le_top)
  have hbound : ∀ n, ∫⁻ y in A, ‖g n y‖ₑ ^ q ≤ B := by
    intro n
    set a : ℝ := unitConvexApproxScale n * t with hadef
    have ha : 0 < a := mul_pos (hεpos n) ht
    have hale : a ≤ t := by
      have := unitConvexApproxScale_le_one n
      nlinarith only [this, ht]
    have hka : κ * a ≤ κ * t := mul_le_mul_of_nonneg_left hale hκ0
    have hRr : R + a ≤ r := by
      have : R + t = Rad := by rw [hRdef, hRad]; ring
      linarith only [this, hale, hr]
    have hchart := layerPoincare_chart hU hx' he hγ hb hch (hgsm n) ha.le (by positivity)
      (R := R) (by rw [hRdef]; nlinarith only [hka, ht, hκ0])
      (by linarith only [hRr, ha]) (fun w hw hzw =>
        layerPoincare_mollified_eq_zero he hγ hb hch hρ ha ψ hRr hw hzw) hq hA hAU hAb
    set k := scaledConvexApproxKernel unitConvexApproxKernel a with hkdef
    have hk : ContDiff ℝ (⊤ : ℕ∞) k := contDiff_scaledConvexApproxKernel hρ a
    have hkc : HasCompactSupport k := hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha
    have hk0 : ∀ y, 0 ≤ k y := scaledConvexApproxKernel_nonneg hρ ha
    have hH0 : ∀ w, 0 ≤ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => (d : ℝ) * ‖Du y‖)) w := fun w => by
      rw [convolution_def]
      exact integral_nonneg fun t => mul_nonneg (hk0 t) (by positivity)
    have hpt : ∀ w, ‖fderiv ℝ (g n) w‖ₑ ^ q ≤ ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => (d : ℝ) * ‖Du y‖)) w‖ₑ ^ q := by
      intro w
      refine ENNReal.rpow_le_rpow ?_ hq0.le
      have h := norm_fderiv_convolution_le hk hkc hk0 hu0loc hw hDuLoc hGloc w
      rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (hH0 w)]
      exact ENNReal.ofReal_le_ofReal h
    have h1 : ENNReal.ofReal (κ * (2 * t + a)) ≤ ENNReal.ofReal (3 * κ * t) :=
      ENNReal.ofReal_le_ofReal (by nlinarith only [hka, ht, hκ0])
    have hY := layerPoincare_young_closedBall hρ ha hGloc hq x' R
    have hRa : R + a ≤ Rad := by
      have : R + t = Rad := by rw [hRdef, hRad]; ring
      linarith only [this, hale]
    have hcR : ENNReal.ofReal d ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top
    calc ∫⁻ y in A, ‖g n y‖ₑ ^ q
        ≤ ENNReal.ofReal (κ * (2 * t + a)) ^ q *
          ∫⁻ w in Metric.closedBall x' R, ‖fderiv ℝ (g n) w‖ₑ ^ q := hchart
      _ ≤ ENNReal.ofReal (3 * κ * t) ^ q * ∫⁻ w in Metric.closedBall x' R,
          ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => (d : ℝ) * ‖Du y‖)) w‖ₑ ^ q :=
        mul_le_mul' (ENNReal.rpow_le_rpow h1 hq0.le)
          (setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun w _ => hpt w)
      _ ≤ ENNReal.ofReal (3 * κ * t) ^ q * ∫⁻ w in Metric.closedBall x' (R + a),
          ‖(d : ℝ) * ‖Du w‖‖ₑ ^ q := mul_le_mul_right hY _
      _ ≤ ENNReal.ofReal (3 * κ * t) ^ q * ∫⁻ w in Metric.closedBall x' Rad,
          ‖(d : ℝ) * ‖Du w‖‖ₑ ^ q :=
        mul_le_mul_right (lintegral_mono_set (Metric.closedBall_subset_closedBall hRa)) _
      _ = ENNReal.ofReal (3 * κ * t) ^ q * (ENNReal.ofReal d ^ q * ∫⁻ w in Metric.closedBall x' Rad,
          U.indicator (fun w => ‖ψ.toH1Function.grad w‖ₑ ^ q) w) := by
        congr 1
        rw [← lintegral_const_mul' _ _ hcR]
        exact lintegral_congr fun w => layerPoincare_enorm_gradient_rpow ψ hq0 w
      _ = B := by rw [hB]; exact (mul_assoc _ _ _).symm
  have hlim : ∀ᵐ x ∂(volume.restrict A), Tendsto (fun n => ‖g (ns n) x‖ₑ ^ q) atTop
      (𝓝 (‖u0 x‖ₑ ^ q)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    exact (ENNReal.continuous_rpow_const (y := q)).tendsto _ |>.comp
      ((continuous_enorm.tendsto _).comp hx)
  have hmeasg : ∀ n, Measurable fun y => ‖g (ns n) y‖ₑ ^ q := fun n =>
    ((hgsm (ns n)).continuous.enorm.measurable).pow_const q
  calc ∫⁻ y in A, ‖ψ.toH1Function.toFun y‖ₑ ^ q
      = ∫⁻ y in A, ‖u0 y‖ₑ ^ q :=
        setLIntegral_congr_fun hA (fun y hy => by rw [hu0def, ψ.zeroExtension_apply_of_mem (hAU hy)])
    _ = ∫⁻ y in A, liminf (fun n => ‖g (ns n) y‖ₑ ^ q) atTop :=
        lintegral_congr_ae (hlim.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ y in A, ‖g (ns n) y‖ₑ ^ q) atTop := lintegral_liminf_le hmeasg
    _ ≤ B := le_trans liminf_le_limsup (limsup_le_of_le (h := Eventually.of_forall fun n => hbound _))

/-! ### Assembly over a grid of cells -/

theorem layerPoincare_isOpen_boundaryLayer {U : Set (Vec d)} (hU : IsOpen U) (t : ℝ) :
    IsOpen (boundaryLayer U t) :=
  hU.inter (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)

theorem layerPoincare_box {t m : ℝ} (ht : 0 < t) {B : ℕ} (hB : m ≤ B) {z y₀ : Vec d}
    (hz : ‖z - y₀‖ < m * t) {k : Fin d → ℤ} (hk : ∀ i, ⌊y₀ i / t⌋ = k i) :
    k ∈ Fintype.piFinset fun i => Finset.Icc (⌊z i / t⌋ - (B : ℤ)) (⌊z i / t⌋ + (B : ℤ)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc, ← hk i]
  have h1 : |z i - y₀ i| < m * t :=
    lt_of_le_of_lt (by simpa using norm_le_pi_norm (z - y₀) i) hz
  have h2 : |z i / t - y₀ i / t| < m := by
    rw [← sub_div, abs_div, abs_of_pos ht, div_lt_iff₀ ht]
    exact h1
  obtain ⟨h2a, h2b⟩ := abs_lt.1 h2
  have f1 := Int.floor_le (z i / t)
  have f2 := Int.lt_floor_add_one (z i / t)
  have g1 := Int.floor_le (y₀ i / t)
  have g2 := Int.lt_floor_add_one (y₀ i / t)
  have hB' : m ≤ (B : ℝ) := hB
  constructor
  · have h : ((⌊z i / t⌋ : ℤ) : ℝ) - B < ((⌊y₀ i / t⌋ : ℤ) : ℝ) + 1 := by
      linarith only [f1, g2, h2a, h2b, hB']
    have h' : ⌊z i / t⌋ - (B : ℤ) < ⌊y₀ i / t⌋ + 1 := by exact_mod_cast h
    omega
  · have h : ((⌊y₀ i / t⌋ : ℤ) : ℝ) < ((⌊z i / t⌋ : ℤ) : ℝ) + B + 1 := by
      linarith only [g1, f2, h2a, h2b, hB']
    have h' : ⌊y₀ i / t⌋ < ⌊z i / t⌋ + (B : ℤ) + 1 := by exact_mod_cast h
    omega

theorem layerPoincare_card_box (t : ℝ) (z : Vec d) (B : ℕ) :
    (Fintype.piFinset fun i : Fin d =>
      Finset.Icc (⌊z i / t⌋ - (B : ℤ)) (⌊z i / t⌋ + (B : ℤ))).card = (2 * B + 1) ^ d := by
  rw [Fintype.card_piFinset]
  have : ∀ i : Fin d, (Finset.Icc (⌊z i / t⌋ - (B : ℤ)) (⌊z i / t⌋ + (B : ℤ))).card = 2 * B + 1 := by
    intro i
    rw [Int.card_Icc]
    omega
  simp [this]

theorem layerPoincare_rpow_div {X a b N I : ℝ≥0∞} {q : ℝ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (h : X ≤ a ^ q * b ^ q * N * I) : X ^ (1 / q) ≤ a * b * N * I ^ (1 / q) := by
  have hq0 : 0 < q := by linarith only [hq]
  have h1q : 0 ≤ 1 / q := by positivity
  have hinv : ∀ x : ℝ≥0∞, (x ^ q) ^ (1 / q) = x := fun x => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  calc X ^ (1 / q) ≤ (a ^ q * b ^ q * N * I) ^ (1 / q) := ENNReal.rpow_le_rpow h h1q
    _ = a * b * N ^ (1 / q) * I ^ (1 / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1q, ENNReal.mul_rpow_of_nonneg _ _ h1q,
          ENNReal.mul_rpow_of_nonneg _ _ h1q, hinv, hinv]
    _ ≤ a * b * N * I ^ (1 / q) := by
        gcongr
        calc N ^ (1 / q) ≤ N ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le hN (by rw [div_le_one hq0]; exact hq)
          _ = N := ENNReal.rpow_one N

theorem layerPoincare_frontier_nonempty [NeZero d] {U : Set (Vec d)} {D : ℝ}
    (hD : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D) (hU0 : U ≠ ∅) : (frontier U).Nonempty := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  exact frontier_nonempty_of_uniform hD hU0

/-- **The `L^q` layer estimate in integral form**, for `0 < t` with `(3κ + 4) t ≤ r`,
`κ = d + (1 + d) M₁`. -/
theorem layerPoincare_integral [NeZero d] {U : Set (Vec d)} {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain U r M₁ M₂ D) (ψ : H10Function U) {q : ℝ} (hq : 1 ≤ q)
    {t : ℝ} (ht : 0 < t) (hr : (3 * ((d : ℝ) + (1 + d) * M₁) + 4) * t ≤ r) :
    ∫⁻ x in boundaryLayer U t, ‖ψ.toH1Function.toFun x‖ₑ ^ q ≤
      ENNReal.ofReal (3 * ((d : ℝ) + (1 + d) * M₁) * t) ^ q * ENNReal.ofReal d ^ q *
        (((2 * ⌈3 * ((d : ℝ) + (1 + d) * M₁) + 5⌉₊ + 1) ^ d : ℕ) : ℝ≥0∞) *
        ∫⁻ x in boundaryLayer U ((3 * ((d : ℝ) + (1 + d) * M₁) + 5) * t),
          ‖ψ.toH1Function.grad x‖ₑ ^ q := by
  classical
  have hq0 : 0 < q := by linarith only [hq]
  set κ : ℝ := (d : ℝ) + (1 + d) * M₁ with hκ
  have hU : IsOpen U := h.1
  have hmeasU : MeasurableSet U := hU.measurableSet
  set Rad : ℝ := (3 * κ + 4) * t with hRad
  set L : Set (Vec d) := boundaryLayer U t with hL
  set L' : Set (Vec d) := boundaryLayer U ((3 * κ + 5) * t) with hL'
  set Bn : ℕ := ⌈3 * κ + 5⌉₊ with hBn
  set N : ℕ := (2 * Bn + 1) ^ d with hN
  set cell : (Fin d → ℤ) → Set (Vec d) := fun k => {y | ∀ i, ⌊y i / t⌋ = k i} with hcell
  set A : (Fin d → ℤ) → Set (Vec d) := fun k => L ∩ cell k with hA
  have hLo : IsOpen L := layerPoincare_isOpen_boundaryLayer hU t
  have hL'o : IsOpen L' := layerPoincare_isOpen_boundaryLayer hU _
  have hLm : MeasurableSet L := hLo.measurableSet
  have hL'm : MeasurableSet L' := hL'o.measurableSet
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
  have hL'U : L' ⊆ U := fun w hw => hw.1
  -- anchors
  have hanch : ∀ k, ∃ c : Vec d, (A k).Nonempty →
      c ∈ frontier U ∧ ∃ y₀ ∈ A k, ‖y₀ - c‖ < t := by
    intro k
    by_cases hk : (A k).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hk
      have hne : (frontier U).Nonempty :=
        layerPoincare_frontier_nonempty h.2.2.1 (fun hU0 => by
          have := hy₀.1.1
          rw [hU0] at this
          exact this)
      obtain ⟨c, hc, hcd⟩ := isClosed_frontier.exists_infDist_eq_dist hne y₀
      refine ⟨c, fun _ => ⟨hc, y₀, hy₀, ?_⟩⟩
      have := hy₀.1.2
      rw [hcd, dist_eq_norm] at this
      exact this
    · exact ⟨0, fun h => absurd h hk⟩
  choose c hc using hanch
  set S : (Fin d → ℤ) → Set (Vec d) :=
    fun k => {w | (A k).Nonempty ∧ w ∈ Metric.closedBall (c k) Rad} with hS
  have hSeq : ∀ k, (A k).Nonempty → S k = Metric.closedBall (c k) Rad := fun k hk => by
    ext w
    simp [hS, hk]
  have hSemp : ∀ k, ¬ (A k).Nonempty → S k = ∅ := fun k hk => by
    ext w
    simp [hS, hk]
  have hSm : ∀ k, MeasurableSet (S k) := fun k => by
    by_cases hk : (A k).Nonempty
    · rw [hSeq k hk]
      exact Metric.isClosed_closedBall.measurableSet
    · rw [hSemp k hk]
      exact MeasurableSet.empty
  set f : Vec d → ℝ≥0∞ := fun w => ‖ψ.toH1Function.grad w‖ₑ ^ q with hf
  set Fl : Vec d → ℝ≥0∞ := L'.indicator f with hFl
  set Kc : ℝ≥0∞ := ENNReal.ofReal (3 * κ * t) ^ q * ENNReal.ofReal d ^ q with hKc
  have hper : ∀ k, ∫⁻ y in A k, ‖ψ.toH1Function.toFun y‖ₑ ^ q ≤ Kc * ∫⁻ w in S k, Fl w := by
    intro k
    by_cases hk : (A k).Nonempty
    · obtain ⟨hcF, y₀, hy₀, hy₀c⟩ := hc k hk
      obtain ⟨e, γ, he, hγ, hb, -, hch⟩ := h.2.2.2 (c k) hcF
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
      have hloc := layerPoincare_local hU ψ hcF he hγ hb hch hq ht hr (hAm k) hAU hAb
      refine hloc.trans ?_
      rw [hSeq k hk]
      refine mul_le_mul_right ?_ _
      refine setLIntegral_mono' Metric.isClosed_closedBall.measurableSet fun w hw => ?_
      by_cases hwU : w ∈ U
      · have hwL : w ∈ L' := by
          refine ⟨hwU, ?_⟩
          calc Metric.infDist w (frontier U) ≤ dist w (c k) := Metric.infDist_le_dist_of_mem hcF
            _ ≤ Rad := Metric.mem_closedBall.1 hw
            _ < (3 * κ + 5) * t := by rw [hRad]; nlinarith only [ht]
        simp only [hFl, Set.indicator_of_mem hwU, Set.indicator_of_mem hwL]
        exact le_rfl
      · simp [Set.indicator_of_notMem hwU]
    · have : A k = ∅ := Set.not_nonempty_iff_eq_empty.1 hk
      rw [this]
      simp
  -- overlap
  have hpt : ∀ w, ∑' k, (S k).indicator Fl w ≤ (N : ℝ≥0∞) * Fl w := by
    intro w
    set P := Fintype.piFinset fun i : Fin d =>
      Finset.Icc (⌊w i / t⌋ - (Bn : ℤ)) (⌊w i / t⌋ + (Bn : ℤ)) with hP
    have hmem : ∀ k, w ∈ S k → k ∈ P := by
      intro k hk
      by_cases hne : (A k).Nonempty
      · obtain ⟨hcF, y₀, hy₀, hy₀c⟩ := hc k hne
        rw [hSeq k hne] at hk
        simp only [Metric.mem_closedBall, dist_eq_norm] at hk
        refine layerPoincare_box ht (m := 3 * κ + 5) (Nat.le_ceil _) ?_ hy₀.2
        calc ‖w - y₀‖ = ‖(w - c k) + (c k - y₀)‖ := by congr 1; abel
          _ ≤ ‖w - c k‖ + ‖c k - y₀‖ := norm_add_le _ _
          _ < (3 * κ + 5) * t := by
              rw [norm_sub_rev (c k) y₀]
              rw [hRad] at hk
              linarith only [hk, hy₀c]
      · rw [hSemp k hne] at hk
        exact absurd hk (Set.notMem_empty w)
    rw [tsum_eq_sum (s := P) (fun k hk => by
      rw [Set.indicator_of_notMem]
      exact fun hw => hk (hmem k hw))]
    calc ∑ k ∈ P, (S k).indicator Fl w ≤ ∑ k ∈ P, Fl w :=
          Finset.sum_le_sum fun k _ => Set.indicator_le_self _ _ w
      _ = P.card • Fl w := Finset.sum_const _
      _ = (N : ℝ≥0∞) * Fl w := by
          rw [nsmul_eq_mul, hP, layerPoincare_card_box]
  have hfae : AEMeasurable f (volume.restrict U) := by
    have hmeas : AEStronglyMeasurable ψ.toH1Function.grad (volume.restrict U) :=
      (aemeasurable_pi_iff.2 fun i =>
        (ψ.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
    exact hmeas.enorm.pow_const q
  have hFlae : AEMeasurable Fl (volume.restrict U) := hfae.indicator hL'm
  have hFlsupp : ∀ w, w ∉ U → Fl w = 0 := fun w hw =>
    Set.indicator_of_notMem (fun hw' => hw (hL'U hw')) _
  have hconv : ∀ k, ∫⁻ w in S k, Fl w = ∫⁻ w in U, (S k).indicator Fl w := by
    intro k
    rw [← lintegral_indicator (hSm k)]
    refine (setLIntegral_eq_of_support_subset ?_).symm
    intro w hw
    by_contra hwU
    exact hw (by simp [hFlsupp w hwU])
  have hsum : ∑' k, ∫⁻ w in S k, Fl w ≤ (N : ℝ≥0∞) * ∫⁻ w in L', f w := by
    calc ∑' k, ∫⁻ w in S k, Fl w = ∑' k, ∫⁻ w in U, (S k).indicator Fl w := tsum_congr hconv
      _ = ∫⁻ w in U, ∑' k, (S k).indicator Fl w :=
          (lintegral_tsum fun k => hFlae.indicator (hSm k)).symm
      _ ≤ ∫⁻ w in U, (N : ℝ≥0∞) * Fl w := lintegral_mono hpt
      _ = (N : ℝ≥0∞) * ∫⁻ w in U, Fl w := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)
      _ = (N : ℝ≥0∞) * ∫⁻ w in L', f w := by
          congr 1
          rw [hFl, lintegral_indicator hL'm, Measure.restrict_restrict hL'm,
            Set.inter_eq_left.2 hL'U]
  calc ∫⁻ x in L, ‖ψ.toH1Function.toFun x‖ₑ ^ q
      ≤ ∫⁻ x in ⋃ k, A k, ‖ψ.toH1Function.toFun x‖ₑ ^ q := lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ x in A k, ‖ψ.toH1Function.toFun x‖ₑ ^ q := lintegral_iUnion_le _ _
    _ ≤ ∑' k, Kc * ∫⁻ w in S k, Fl w := ENNReal.tsum_le_tsum hper
    _ = Kc * ∑' k, ∫⁻ w in S k, Fl w := ENNReal.tsum_mul_left
    _ ≤ Kc * ((N : ℝ≥0∞) * ∫⁻ w in L', f w) := mul_le_mul_right hsum _
    _ = Kc * (N : ℝ≥0∞) * ∫⁻ w in L', f w := (mul_assoc _ _ _).symm

/-- **Boundary-layer Poincare inequality for zero-trace functions.** For a uniformly `C^{1,1}`
bounded open set `U` with data `(r, M₁, M₂, D)`, every `ψ ∈ H¹₀(U)` and every `1 ≤ q < ∞`,
and every `0 < t ≤ t₀`,
`‖ψ‖_{L^q(boundaryLayer U t)} ≤ C t ‖∇ψ‖_{L^q(boundaryLayer U (K t))}`,
where `C, K, t₀` depend only on `(d, r, M₁)` (not on `q`, `M₂`, `D`, `U`). -/
theorem exists_layerPoincare [NeZero d] (r M₁ : ℝ) (hr : 0 < r) :
    ∃ C K t₀ : ℝ, 0 ≤ C ∧ 1 ≤ K ∧ 0 < t₀ ∧
      ∀ {U : Set (Vec d)} {M₂ D : ℝ}, IsUniformC11Domain U r M₁ M₂ D →
        ∀ (ψ : H10Function U) {q : ℝ}, 1 ≤ q → ∀ {t : ℝ}, 0 < t → t ≤ t₀ →
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
  refine ⟨3 * κ₀ * d * Nr, 3 * κ₀ + 5, r / (3 * κ₀ + 4), by positivity, by linarith only [hκ0],
    by positivity, ?_⟩
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

end SuperdiffusionCLT.Section7
