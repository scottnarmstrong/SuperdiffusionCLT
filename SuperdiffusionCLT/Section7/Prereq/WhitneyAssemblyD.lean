/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyAssemblyC
public import SuperdiffusionCLT.Section7.Analytic.Geometry.WhitneyBallB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiB
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationD

/-!
# The boundary-layer step and the variance inequality, in lower-integral form

* `Section7.wh3_layer_enn`: for `w ∈ H¹(W)` on a uniformly `C^{1,1}` domain, with the part of `W`
  outside a measurable `U1` inside the layer of width `s`,
  `∫_W (w - c)² ≤ 2 ∫_{U1} (w - c)² + 2 C s r ∫_W |∇w|²` (as soon as `C s / r ≤ 1/2`).
* `Section7.wh3_variance`: `∫_W (u - (u)_W)² ≤ ∫_W (u - c)²` for every constant `c`.
* `Section7.wh3_core`: the deterministic core of the coarse-grained Poincare inequality.
* `Section7.wh3_hyp_conv`, `Section7.wh3_sqrt_step`, `Section7.wh3_numeric`: the transfer of the
  Poincare hypothesis, the square-root step and the numerical constants of the final assembly.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- `x ≤ y + x / 2` with `x` finite gives `x ≤ 2 y`. -/
theorem wh3_absorb {x y : ℝ≥0∞} (hx : x ≠ ⊤) (h : x ≤ 2⁻¹ * y + 2⁻¹ * x) : x ≤ y := by
  have h2 : 2⁻¹ * x + 2⁻¹ * x ≤ 2⁻¹ * y + 2⁻¹ * x := by
    rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    exact h
  have hx2 : 2⁻¹ * x ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hx
  have h3 := (ENNReal.add_le_add_iff_right hx2).1 h2
  have h4 := mul_le_mul_right (a := 2) h3
  rw [← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul,
    one_mul] at h4
  exact h4

/-- The boundary-layer step (lower-integral form). -/
theorem wh3_layer_enn [NeZero d] (M₁ : ℝ) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ {W : Set (Vec d)} {r' M₂ D' : ℝ}, IsUniformC11Domain W r' M₁ M₂ D' →
      ∀ (w : H1Function W) {s : ℝ}, 0 < s → Cl * (s / r') ≤ 1 / 2 →
        ∀ {U1 : Set (Vec d)}, MeasurableSet U1 → U1 ⊆ W →
          (∀ᵐ x : Vec d, x ∈ W → x ∉ U1 → x ∈ boundaryLayer W s) → ∀ c : ℝ,
            ∫⁻ x in W, ENNReal.ofReal ((w.toFun x - c) ^ 2) ≤
              2 * (∫⁻ x in U1, ENNReal.ofReal ((w.toFun x - c) ^ 2)) +
                2 * ENNReal.ofReal (Cl * (s * r')) * ∫⁻ x in W, ‖w.grad x‖ₑ ^ (2 : ℝ) := by
  obtain ⟨C, hC0, hmain⟩ := exists_layerH1 (d := d) M₁
  refine ⟨C, hC0, fun {W r' M₂ D'} h w s hs ha U1 hU1 hU1W hcov c => ?_⟩
  have hr : 0 < r' := h.2.1
  have hWm : MeasurableSet W := h.1.measurableSet
  have : IsFiniteMeasure (volume.restrict W) := hl_isFiniteMeasure h.2.2.1
  set wt : H1Function W := w - H1Function.const (U := W) c with hwt
  have hm := hmain h wt hs
  simp_rw [hwt, hl_sub_const_toFun, hl_sub_const_grad, hl_enorm_rpow_two] at hm
  set Y : ℝ≥0∞ := ∫⁻ x in W, ENNReal.ofReal ((w.toFun x - c) ^ 2) with hY
  set Y1 : ℝ≥0∞ := ∫⁻ x in U1, ENNReal.ofReal ((w.toFun x - c) ^ 2) with hY1
  set X' : ℝ≥0∞ := ∫⁻ x in W \ U1, ENNReal.ofReal ((w.toFun x - c) ^ 2) with hX'
  set G : ℝ≥0∞ := ∫⁻ x in W, ‖w.grad x‖ₑ ^ (2 : ℝ) with hG
  set a : ℝ≥0∞ := ENNReal.ofReal (C * (s / r')) with ha0
  set b : ℝ≥0∞ := ENNReal.ofReal (C * (s * r')) with hb0
  have hYtop : Y ≠ ⊤ := by
    have hint : Integrable (fun x => (w.toFun x - c) ^ 2) (volume.restrict W) := by
      have := hl_integrable_sq wt
      simpa only [hwt, hl_sub_const_toFun] using this
    exact (hint.lintegral_lt_top).ne
  have hsplit : Y1 + X' = Y := by
    have := lintegral_inter_add_sdiff (μ := volume)
      (fun x => ENNReal.ofReal ((w.toFun x - c) ^ 2)) W hU1
    rw [Set.inter_eq_right.2 hU1W] at this
    exact this
  have hX'Y : X' ≤ Y := by
    rw [← hsplit]; exact le_add_self
  have hX'top : X' ≠ ⊤ := ne_top_of_le_ne_top hYtop hX'Y
  have hlay : X' ≤ ∫⁻ x in boundaryLayer W s, ENNReal.ofReal ((w.toFun x - c) ^ 2) := by
    refine lintegral_mono' (Measure.restrict_mono_ae ?_) le_rfl
    filter_upwards [hcov] with x hx hxs
    exact hx hxs.1 hxs.2
  have h1 : X' ≤ a * Y + b * G := hlay.trans hm
  have ha2 : a ≤ 2⁻¹ := by
    rw [ha0]
    have : C * (s / r') ≤ 1 / 2 := ha
    calc ENNReal.ofReal (C * (s / r')) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal this
      _ = 2⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have h2 : X' ≤ 2⁻¹ * (Y1 + 2 * (b * G)) + 2⁻¹ * X' := by
    have e : a * Y + b * G ≤ 2⁻¹ * (Y1 + X') + b * G := by
      rw [← hsplit]
      gcongr
    have e2 : 2⁻¹ * (Y1 + X') + b * G = 2⁻¹ * (Y1 + 2 * (b * G)) + 2⁻¹ * X' := by
      rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num)
        (by norm_num), one_mul]
      ring
    exact h1.trans (e.trans e2.le)
  have h3 := wh3_absorb hX'top h2
  calc Y = Y1 + X' := hsplit.symm
    _ ≤ Y1 + (Y1 + 2 * (b * G)) := by gcongr
    _ = 2 * Y1 + 2 * b * G := by ring

/-- Mean-subtracted functions minimize the `L²` distance to constants. -/
theorem wh3_variance {W : Set (Vec d)} (hW : volume W ≠ ⊤) (u : H1Function W) (c : ℝ) :
    ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - ⨍ z in W, u.toFun z) ^ 2) ≤
      ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - c) ^ 2) := by
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hW⟩
  set ub : ℝ := ⨍ z in W, u.toFun z with hub
  have hu1 : Integrable u.toFun (volume.restrict W) := u.memL2.integrable (by norm_num)
  have hq : ∀ e : ℝ, Integrable (fun x => (u.toFun x - e) ^ 2) (volume.restrict W) := by
    intro e
    have : MemLp (fun x => u.toFun x - e) 2 (volume.restrict W) :=
      u.memL2.sub (memLp_const e)
    exact this.integrable_sq
  have hint : ∫ x in W, u.toFun x = (volume.restrict W).real univ * ub := by
    have := measure_smul_average (μ := volume.restrict W) u.toFun
    rw [smul_eq_mul] at this
    exact this.symm
  have key : ∫ x in W, (u.toFun x - c) ^ 2 =
      (∫ x in W, (u.toFun x - ub) ^ 2) + (volume.restrict W).real univ * (ub - c) ^ 2 := by
    have e : ∀ x, (u.toFun x - c) ^ 2 = (u.toFun x - ub) ^ 2 +
        ((2 * (ub - c)) * u.toFun x + ((ub - c) ^ 2 - 2 * (ub - c) * ub)) := by
      intro x; ring
    have hI2 : Integrable (fun x => (2 * (ub - c)) * u.toFun x + ((ub - c) ^ 2 - 2 * (ub - c) * ub))
        (volume.restrict W) := (hu1.const_mul _).add (integrable_const _)
    have I1 : ∫ x in W, ((u.toFun x - ub) ^ 2 +
        ((2 * (ub - c)) * u.toFun x + ((ub - c) ^ 2 - 2 * (ub - c) * ub))) =
        (∫ x in W, (u.toFun x - ub) ^ 2) +
          ∫ x in W, ((2 * (ub - c)) * u.toFun x + ((ub - c) ^ 2 - 2 * (ub - c) * ub)) :=
      integral_add (hq ub) hI2
    have I2 : ∫ x in W, ((2 * (ub - c)) * u.toFun x + ((ub - c) ^ 2 - 2 * (ub - c) * ub)) =
        (2 * (ub - c)) * (∫ x in W, u.toFun x) +
          (volume.restrict W).real univ • ((ub - c) ^ 2 - 2 * (ub - c) * ub) := by
      rw [integral_add (hu1.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp_rw [e]
    rw [I1, I2, hint, smul_eq_mul]
    ring
  have hle : ∫ x in W, (u.toFun x - ub) ^ 2 ≤ ∫ x in W, (u.toFun x - c) ^ 2 := by
    rw [key]
    have : 0 ≤ (volume.restrict W).real univ * (ub - c) ^ 2 := by positivity
    linarith only [this]
  rw [← ofReal_integral_eq_lintegral_ofReal (hq ub) (Filter.Eventually.of_forall fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (hq c) (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hle

/-- `‖v‖ₑ² ≤ ofReal (eucNorm v ²)`. -/
theorem wh3_enorm_le_eucNorm (v : Vec d) :
    ‖v‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (eucNorm v ^ 2) := by
  rw [hl_enorm_vec_rpow_two]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (wpd_norm_le_eucNorm v) 2)

theorem wh3_eucNorm_sq (v : Vec d) : eucNorm v ^ 2 = ∑ i, v i ^ 2 := by
  unfold eucNorm
  rw [Real.sq_sqrt (by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _),
    wpd_vecNormSq_eq]

/-- The deterministic core of the coarse-grained Poincare inequality in a dilated domain. -/
theorem wh3_core [NeZero d] (M₁ : ℝ) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ {W : Set (Vec d)} {r' M₂ D' : ℝ}, IsUniformC11Domain W r' M₁ M₂ D' →
      ∀ {h : ℝ}, 0 < h → ∀ (Zg : Finset (Fin d → ℤ)), (∀ k, k ∈ Zg ↔ k ∈ wh3_good h W) →
        Cl * (14 * h / r') ≤ 1 / 2 → ∀ (u : H1Function W) (c : (Fin d → ℤ) → ℝ) {P : ℝ},
          (∀ φ : H1Function W,
            ∫⁻ x in ⋃ k ∈ Zg, wh3_cell h k,
                ENNReal.ofReal ((φ.toFun x - ⨍ z in ⋃ k ∈ Zg, wh3_cell h k, φ.toFun z) ^ 2) ≤
              ENNReal.ofReal (P ^ 2) *
                ∫⁻ x in ⋃ k ∈ Zg, wh3_cell h k, ENNReal.ofReal (eucNorm (φ.grad x) ^ 2)) →
          ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - ⨍ z in W, u.toFun z) ^ 2) ≤
            (4 * 9 ^ d + 4 * ENNReal.ofReal (P ^ 2) * ENNReal.ofReal (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) *
                (∑ a ∈ Zg, wh1_osc h (27 * h / 2) u.toFun c a) +
              2 * ENNReal.ofReal (Cl * (14 * h * r')) *
                ∫⁻ x in W, ENNReal.ofReal (eucNorm (u.grad x) ^ 2) := by
  obtain ⟨Cl, hCl0, hlay⟩ := wh3_layer_enn (d := d) M₁
  refine ⟨Cl, hCl0, fun {W r' M₂ D'} hW h hh Zg hZg hsmall u c P hP => ?_⟩
  have hr' : 0 < r' := hW.2.1
  have hWm : MeasurableSet W := hW.1.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict W) := hl_isFiniteMeasure hW.2.2.1
  have hWtop : volume W ≠ ⊤ := by
    have := hfin.measure_univ_lt_top
    rw [Measure.restrict_apply_univ] at this
    exact this.ne
  set U1 : Set (Vec d) := ⋃ k ∈ Zg, wh3_cell h k with hU1
  have hU1m : MeasurableSet U1 :=
    Finset.measurableSet_biUnion Zg fun k _ => wh1_box_measurable _ _
  have hbox : ∀ k ∈ Zg, wh1_box (wh1_pt h k) (27 * h / 2) ⊆ W := fun k hk => (hZg k).1 hk
  have hU1W : U1 ⊆ W := by
    intro x hx
    simp only [hU1, Set.mem_iUnion, exists_prop] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    exact hbox k hk (wh1_box_mono _ (by linarith only [hh]) hxk)
  have hcov := wh3_layer_cover hW.1 hh hZg
  have hu : ∀ k₀ ∈ Zg, AEMeasurable u.toFun
      (volume.restrict (wh1_box (wh1_pt h k₀) (27 * h / 2))) := fun k₀ hk₀ =>
    u.memL2.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono (hbox k₀ hk₀) le_rfl)
  set Z : Finset (Fin d → ℤ) := Zg.biUnion wh1_nbhd with hZ
  set At : H1Function W := wh1_H1 hh hWtop Z (fun k => c (wh3_sig Zg k)) with hAt
  have hAtfun : At.toFun = wh1_A h Z (fun k => c (wh3_sig Zg k)) := rfl
  have hAtgrad : At.grad = lipGradient (wh1_A h Z (fun k => c (wh3_sig Zg k))) := rfl
  have hr : 5 * h / 2 ≤ 27 * h / 2 := by linarith only [hh]
  have hI1 := wh3_interp_sub_A hh hr Zg c u.toFun hu
  have hI2 := wh3_interp_grad hh hr Zg c u.toFun hu
  set S : ℝ≥0∞ := ∑ a ∈ Zg, wh1_osc h (27 * h / 2) u.toFun c a with hS
  set c₀ : ℝ := ⨍ z in U1, At.toFun z with hc₀
  -- the interpolant step
  have hAcont : Continuous At.toFun := (wh1_A_lipschitz hh Z _).continuous
  have hmeas_u : AEMeasurable u.toFun (volume.restrict W) :=
    u.memL2.aestronglyMeasurable.aemeasurable
  have hmeas1 : AEMeasurable (fun x => ENNReal.ofReal ((u.toFun x - At.toFun x) ^ 2))
      (volume.restrict U1) :=
    (((hmeas_u.mono_measure (Measure.restrict_mono hU1W le_rfl)).sub
      hAcont.aemeasurable).pow_const 2).ennreal_ofReal
  have hpt : ∀ x, ENNReal.ofReal ((u.toFun x - c₀) ^ 2) ≤
      2 * ENNReal.ofReal ((u.toFun x - At.toFun x) ^ 2) +
        2 * ENNReal.ofReal ((At.toFun x - c₀) ^ 2) := by
    intro x
    rw [← wh1_ofReal_two_mul, ← wh1_ofReal_two_mul,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have key : 2 * (u.toFun x - At.toFun x) ^ 2 + 2 * (At.toFun x - c₀) ^ 2 -
        (u.toFun x - c₀) ^ 2 = (u.toFun x - 2 * At.toFun x + c₀) ^ 2 := by ring
    linarith only [key, sq_nonneg (u.toFun x - 2 * At.toFun x + c₀)]
  have hA1 : ∫⁻ x in U1, ENNReal.ofReal ((u.toFun x - c₀) ^ 2) ≤
      2 * (9 ^ d * S) + 2 * (ENNReal.ofReal (P ^ 2) *
        (ENNReal.ofReal (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2) * S)) := by
    calc ∫⁻ x in U1, ENNReal.ofReal ((u.toFun x - c₀) ^ 2)
        ≤ ∫⁻ x in U1, (2 * ENNReal.ofReal ((u.toFun x - At.toFun x) ^ 2) +
            2 * ENNReal.ofReal ((At.toFun x - c₀) ^ 2)) := lintegral_mono fun x => hpt x
      _ = 2 * (∫⁻ x in U1, ENNReal.ofReal ((u.toFun x - At.toFun x) ^ 2)) +
            2 * (∫⁻ x in U1, ENNReal.ofReal ((At.toFun x - c₀) ^ 2)) := by
          rw [lintegral_add_left' (hmeas1.const_mul 2), lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp)]
      _ ≤ 2 * (9 ^ d * S) + 2 * (ENNReal.ofReal (P ^ 2) *
            (ENNReal.ofReal (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2) * S)) := by
          gcongr
          · exact hI1
          · refine (hP At).trans ?_
            gcongr
            have e : ∀ x, ENNReal.ofReal (eucNorm (At.grad x) ^ 2) =
                ENNReal.ofReal (∑ i, (lipGradient (wh1_A h Z (fun k => c (wh3_sig Zg k))) x i) ^ 2) := by
              intro x
              rw [wh3_eucNorm_sq, hAtgrad]
            simp_rw [e]
            exact hI2
  have hL := hlay hW u (s := 14 * h) (by positivity) hsmall hU1m hU1W hcov c₀
  have hvar := wh3_variance hWtop u c₀
  have hG : ∫⁻ x in W, ‖u.grad x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x in W, ENNReal.ofReal (eucNorm (u.grad x) ^ 2) :=
    lintegral_mono fun x => wh3_enorm_le_eucNorm _
  refine hvar.trans (hL.trans ?_)
  calc 2 * (∫⁻ x in U1, ENNReal.ofReal ((u.toFun x - c₀) ^ 2)) +
        2 * ENNReal.ofReal (Cl * (14 * h * r')) * ∫⁻ x in W, ‖u.grad x‖ₑ ^ (2 : ℝ)
      ≤ 2 * (2 * (9 ^ d * S) + 2 * (ENNReal.ofReal (P ^ 2) *
          (ENNReal.ofReal (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2) * S))) +
        2 * ENNReal.ofReal (Cl * (14 * h * r')) *
          ∫⁻ x in W, ENNReal.ofReal (eucNorm (u.grad x) ^ 2) := by gcongr
    _ = _ := by ring

theorem wh3_eLpNorm_sq {μ : Measure (Vec d)} {f : Vec d → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf]
  unfold eLpNorm'
  simp only [ENNReal.toReal_ofNat, hl_enorm_rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The scaled Poincare hypothesis, transferred to the union of the open cells. -/
theorem wh3_hyp_conv {W Q U1 : Set (Vec d)} (hae : Q =ᵐ[volume] U1) (hUW : U1 ⊆ W) {Dm : ℝ} (hD : 0 ≤ Dm)
    (hQ : ∀ φ : H1Function W,
      eLpNorm (fun x => φ.toFun x - ⨍ z in Q, φ.toFun z) 2 (volume.restrict Q) ≤
        ENNReal.ofReal Dm * eLpNorm (fun x => eucNorm (φ.grad x)) 2 (volume.restrict Q)) :
    ∀ φ : H1Function W,
      ∫⁻ x in U1, ENNReal.ofReal ((φ.toFun x - ⨍ z in U1, φ.toFun z) ^ 2) ≤
        ENNReal.ofReal (Dm ^ 2) * ∫⁻ x in U1, ENNReal.ofReal (eucNorm (φ.grad x) ^ 2) := by
  intro φ
  have h := hQ φ
  rw [Measure.restrict_congr_set hae] at h
  have h2 := pow_le_pow_left' h 2
  have hm1 : AEStronglyMeasurable (fun x => φ.toFun x - ⨍ z in U1, φ.toFun z)
      (volume.restrict U1) := by
    exact (φ.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hUW le_rfl)).sub aestronglyMeasurable_const
  have hm2 : AEStronglyMeasurable (fun x => eucNorm (φ.grad x)) (volume.restrict U1) := by
    exact (memLp_eucNorm_grad φ).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono hUW le_rfl)
  rw [mul_pow, wh3_eLpNorm_sq hm1, wh3_eLpNorm_sq hm2] at h2
  have e : ENNReal.ofReal Dm ^ 2 = ENNReal.ofReal (Dm ^ 2) := by
    rw [ENNReal.ofReal_pow hD]
  rw [e] at h2
  exact h2

theorem wh3_le_of_sq_le {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have := ENNReal.rpow_le_rpow h (z := 1 / 2) (by norm_num)
  rwa [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    Nat.cast_ofNat, mul_one_div_cancel (by norm_num), ENNReal.rpow_one, ENNReal.rpow_one] at this

/-- The square-root step. -/
theorem wh3_sqrt_step {E Eg Ef : ℝ≥0∞} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : E ^ 2 ≤ ENNReal.ofReal (a ^ 2) * Eg ^ 2 + ENNReal.ofReal (b ^ 2) * Ef ^ 2) :
    E ≤ ENNReal.ofReal a * Eg + ENNReal.ofReal b * Ef := by
  have e1 : ENNReal.ofReal (a ^ 2) * Eg ^ 2 = (ENNReal.ofReal a * Eg) ^ 2 := by
    rw [mul_pow, ENNReal.ofReal_pow ha]
  have e2 : ENNReal.ofReal (b ^ 2) * Ef ^ 2 = (ENNReal.ofReal b * Ef) ^ 2 := by
    rw [mul_pow, ENNReal.ofReal_pow hb]
  rw [e1, e2] at h
  have h3 : (ENNReal.ofReal a * Eg) ^ 2 + (ENNReal.ofReal b * Ef) ^ 2 ≤
      (ENNReal.ofReal a * Eg + ENNReal.ofReal b * Ef) ^ 2 := by
    rw [add_sq]
    calc _ ≤ (ENNReal.ofReal a * Eg) ^ 2 + (ENNReal.ofReal b * Ef) ^ 2 +
          2 * (ENNReal.ofReal a * Eg) * (ENNReal.ofReal b * Ef) := le_self_add
      _ = _ := by ring
  have h4 := h.trans h3
  exact wh3_le_of_sq_le h4


theorem wh3_numeric (d : ℕ) (Cp C₂ Ce Cl r₀ : ℝ) (hCp : 0 < Cp) (hC₂ : 1 ≤ C₂) (hCe : 0 < Ce)
    (hCl : 0 ≤ Cl) (hr₀ : 0 < r₀) :
    ∃ Γ : ℝ, 1 ≤ Γ ∧ ∀ {ν σ s D T h q rr : ℝ}, 0 < ν → 0 < σ → 0 ≤ s → s ^ 2 * σ = ν →
      s ^ 2 ≤ 2 * Ce → 1 ≤ D → 0 < T → 0 < h → h ≤ T → h * σ ≤ T * ν → q = 27 * h →
      rr ≤ T * r₀ → 0 ≤ rr →
        ((4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * 27 ^ d *
              (2 * (Cp * q) ^ 2 * (C₂ * s) ^ 2) + 2 * Cl * (14 * h * rr) ≤ (Γ * D * T * s) ^ 2) ∧
        ((4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * 27 ^ d *
              (2 * (Cp * q) ^ 2 * ((C₂ * s + C₂) * (C₂ * q / ν)) ^ 2) ≤ (Γ * D * T * h / ν) ^ 2) := by
  set κ : ℝ := 4 * 9 ^ d + 16 * (d : ℝ) ^ 3 * 27 ^ d with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set G1 : ℝ := 27 ^ d * 2 * C₂ ^ 2 * 729 * Cp ^ 2 * κ + 28 * Cl * r₀ with hG1
  set G2 : ℝ := 27 ^ d * 2 * 729 * Cp ^ 2 * κ * C₂ ^ 4 * (2 + 2 * Ce) ^ 2 * 729 with hG2
  have hG10 : 0 ≤ G1 := by positivity
  have hG20 : 0 ≤ G2 := by positivity
  refine ⟨Real.sqrt (G1 + G2 + 1), ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ G1 + G2 + 1 := by linarith only [hG10, hG20]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  intro ν σ s D T h q rr hν hσ hs0 hs hs2 hD hT hh hhT hhσ hq hrr hrr0
  have hGam : Real.sqrt (G1 + G2 + 1) ^ 2 = G1 + G2 + 1 :=
    Real.sq_sqrt (by linarith only [hG10, hG20])
  have hDT : h ≤ D * T := by nlinarith only [hD, hT, hhT]
  have hDT0 : 0 < D * T := mul_pos (by linarith only [hD]) hT
  have hΩ : (4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * (Cp * q) ^ 2 ≤
      729 * Cp ^ 2 * κ * (D * T) ^ 2 := by
    have e : (4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * (Cp * q) ^ 2 =
        Cp ^ 2 * 729 * (4 * 9 ^ d * h ^ 2 + 16 * (d : ℝ) ^ 3 * 27 ^ d * (D * T) ^ 2) := by
      rw [hq]; field_simp; ring
    rw [e]
    have h1 : 4 * (9 : ℝ) ^ d * h ^ 2 ≤ 4 * 9 ^ d * (D * T) ^ 2 := by
      have : h ^ 2 ≤ (D * T) ^ 2 := pow_le_pow_left₀ hh.le hDT 2
      have h9 : (0 : ℝ) ≤ 4 * 9 ^ d := by positivity
      exact mul_le_mul_of_nonneg_left this h9
    have h2 : 4 * (9 : ℝ) ^ d * h ^ 2 + 16 * (d : ℝ) ^ 3 * 27 ^ d * (D * T) ^ 2 ≤
        κ * (D * T) ^ 2 := by
      calc 4 * (9 : ℝ) ^ d * h ^ 2 + 16 * (d : ℝ) ^ 3 * 27 ^ d * (D * T) ^ 2
          ≤ 4 * 9 ^ d * (D * T) ^ 2 + 16 * (d : ℝ) ^ 3 * 27 ^ d * (D * T) ^ 2 := by
            linarith only [h1]
        _ = κ * (D * T) ^ 2 := by rw [hκ]; ring
    have h3 : 0 ≤ Cp ^ 2 * 729 := by positivity
    calc Cp ^ 2 * 729 * (4 * 9 ^ d * h ^ 2 + 16 * (d : ℝ) ^ 3 * 27 ^ d * (D * T) ^ 2)
        ≤ Cp ^ 2 * 729 * (κ * (D * T) ^ 2) := mul_le_mul_of_nonneg_left h2 h3
      _ = _ := by ring
  have hs2σ : h ≤ T * s ^ 2 := by
    have : h * σ ≤ (T * s ^ 2) * σ :=
      calc h * σ ≤ T * ν := hhσ
        _ = T * (s ^ 2 * σ) := by rw [hs]
        _ = (T * s ^ 2) * σ := by ring
    exact le_of_mul_le_mul_right this hσ
  constructor
  · have hA : (4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * 27 ^ d *
        (2 * (Cp * q) ^ 2 * (C₂ * s) ^ 2) =
        27 ^ d * 2 * C₂ ^ 2 * s ^ 2 *
          ((4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * (Cp * q) ^ 2) := by
      ring
    have hB : 2 * Cl * (14 * h * rr) ≤ 28 * Cl * r₀ * ((D * T) ^ 2 * s ^ 2) := by
      have e1 : 2 * Cl * (14 * h * rr) = 28 * Cl * (h * rr) := by ring
      have e2 : h * rr ≤ (T * s ^ 2) * (T * r₀) :=
        mul_le_mul hs2σ hrr hrr0 (by positivity)
      have e3 : (T * s ^ 2) * (T * r₀) ≤ ((D * T) ^ 2 * s ^ 2) * r₀ := by
        have h1 : T ^ 2 ≤ (D * T) ^ 2 := pow_le_pow_left₀ hT.le (by nlinarith only [hD, hT]) 2
        have h2 : T ^ 2 * (s ^ 2 * r₀) ≤ (D * T) ^ 2 * (s ^ 2 * r₀) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        calc (T * s ^ 2) * (T * r₀) = T ^ 2 * (s ^ 2 * r₀) := by ring
          _ ≤ (D * T) ^ 2 * (s ^ 2 * r₀) := h2
          _ = _ := by ring
      have h28 : 0 ≤ 28 * Cl := by positivity
      calc 2 * Cl * (14 * h * rr) = 28 * Cl * (h * rr) := e1
        _ ≤ 28 * Cl * (((D * T) ^ 2 * s ^ 2) * r₀) :=
            mul_le_mul_of_nonneg_left (e2.trans e3) h28
        _ = _ := by ring
    rw [hA]
    have hC : 27 ^ d * 2 * C₂ ^ 2 * s ^ 2 *
        ((4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * (Cp * q) ^ 2) ≤
        27 ^ d * 2 * C₂ ^ 2 * s ^ 2 * (729 * Cp ^ 2 * κ * (D * T) ^ 2) :=
      mul_le_mul_of_nonneg_left hΩ (by positivity)
    have hG : (G1 : ℝ) * (D * T * s) ^ 2 ≤ (Real.sqrt (G1 + G2 + 1) * D * T * s) ^ 2 := by
      have : (Real.sqrt (G1 + G2 + 1) * D * T * s) ^ 2 =
          (G1 + G2 + 1) * (D * T * s) ^ 2 := by
        have e : (Real.sqrt (G1 + G2 + 1) * D * T * s) ^ 2 =
            Real.sqrt (G1 + G2 + 1) ^ 2 * (D * T * s) ^ 2 := by ring
        rw [e, hGam]
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith only [hG20]) (sq_nonneg _)
    have hG' : 27 ^ d * 2 * C₂ ^ 2 * s ^ 2 * (729 * Cp ^ 2 * κ * (D * T) ^ 2) +
        28 * Cl * r₀ * ((D * T) ^ 2 * s ^ 2) = G1 * (D * T * s) ^ 2 := by
      rw [hG1]; ring
    linarith only [hC, hB, hG, hG']
  · have hB0 : (C₂ * s + C₂) * (C₂ * q / ν) ≤ (C₂ ^ 2 * (2 + 2 * Ce) * 27) * (h / ν) := by
      have hs1 : s ≤ 1 + 2 * Ce := by
        by_cases h1 : s ≤ 1
        · linarith only [h1, hCe]
        · push Not at h1
          have : s ≤ s ^ 2 := by nlinarith only [h1]
          linarith only [this, hs2]
      have e : (C₂ * s + C₂) * (C₂ * q / ν) = C₂ ^ 2 * (s + 1) * 27 * (h / ν) := by
        rw [hq]; ring
      rw [e]
      have : s + 1 ≤ 2 + 2 * Ce := by linarith only [hs1]
      have h5 : 0 ≤ C₂ ^ 2 * 27 * (h / ν) := by positivity
      calc C₂ ^ 2 * (s + 1) * 27 * (h / ν) = (s + 1) * (C₂ ^ 2 * 27 * (h / ν)) := by ring
        _ ≤ (2 + 2 * Ce) * (C₂ ^ 2 * 27 * (h / ν)) := mul_le_mul_of_nonneg_right this h5
        _ = _ := by ring
    have hB1 : ((C₂ * s + C₂) * (C₂ * q / ν)) ^ 2 ≤ ((C₂ ^ 2 * (2 + 2 * Ce) * 27) * (h / ν)) ^ 2 :=
      pow_le_pow_left₀ (by rw [hq]; positivity) hB0 2
    calc (4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) * 27 ^ d *
          (2 * (Cp * q) ^ 2 * ((C₂ * s + C₂) * (C₂ * q / ν)) ^ 2)
        = 27 ^ d * 2 * (((4 * 9 ^ d + 4 * (D * T) ^ 2 * (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2)) *
            (Cp * q) ^ 2) * ((C₂ * s + C₂) * (C₂ * q / ν)) ^ 2) := by ring
      _ ≤ 27 ^ d * 2 * ((729 * Cp ^ 2 * κ * (D * T) ^ 2) *
            ((C₂ ^ 2 * (2 + 2 * Ce) * 27) * (h / ν)) ^ 2) := by
          gcongr
      _ = G2 * (D * T * h / ν) ^ 2 := by
          rw [hG2]; field_simp; ring
      _ ≤ (Real.sqrt (G1 + G2 + 1) * D * T * h / ν) ^ 2 := by
          have : (Real.sqrt (G1 + G2 + 1) * D * T * h / ν) ^ 2 =
              (G1 + G2 + 1) * (D * T * h / ν) ^ 2 := by
            have e : (Real.sqrt (G1 + G2 + 1) * D * T * h / ν) ^ 2 =
                Real.sqrt (G1 + G2 + 1) ^ 2 * (D * T * h / ν) ^ 2 := by ring
            rw [e, hGam]
          rw [this]
          exact mul_le_mul_of_nonneg_right (by linarith only [hG10]) (sq_nonneg _)


end SuperdiffusionCLT.Section7
