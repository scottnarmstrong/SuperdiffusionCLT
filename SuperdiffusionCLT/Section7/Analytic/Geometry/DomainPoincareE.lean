/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareD

/-!
# Poincare inequalities on star-ball domains: the mean-value inequality

`Section7.a10_poincare_starBall`: for `W` star-shaped with respect to every point of a cube of
half-width `s` and of diameter at most `D`, and `u ∈ H¹(W)`,
`‖u - ū_W‖_{L²(W)} ≤ C(d, D/s) D ‖∇u‖_{L²(W)}`, with an explicit constant depending only on `d`
and `D/s`. The mean over `W` is compared with the mean over the cube by Jensen's inequality.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem a10_two_sq_le (a b c : ℝ) : (b - a) ^ 2 ≤ 2 * (a - c) ^ 2 + 2 * (b - c) ^ 2 := by
  have : 0 ≤ (a + b - 2 * c) ^ 2 := sq_nonneg _
  nlinarith only [this]

/-- The mean over `W` is within a factor `4` (in square) of the best constant. -/
theorem a10_meanW_le {W : Set (Vec d)} (hW0 : volume W ≠ 0)
    (hWt : volume W ≠ ⊤) {U : Vec d → ℝ} (hUm : Measurable U) (hUi : IntegrableOn U W volume)
    (c : ℝ) :
    ∫⁻ x in W, ENNReal.ofReal ((U x - (∫ y in W, U y) / (volume W).toReal) ^ 2) ≤
      4 * ∫⁻ x in W, ENNReal.ofReal ((U x - c) ^ 2) := by
  set mW : ℝ := (∫ y in W, U y) / (volume W).toReal with hmW
  set Ec : ENNReal := ∫⁻ x in W, ENNReal.ofReal ((U x - c) ^ 2) with hEc
  have hpt : ∀ x y : ℝ, ENNReal.ofReal ((x - y) ^ 2) ≤
      2 * ENNReal.ofReal ((x - c) ^ 2) + 2 * ENNReal.ofReal ((y - c) ^ 2) := by
    intro x y
    have h := a10_two_sq_le x y c
    calc ENNReal.ofReal ((x - y) ^ 2) = ENNReal.ofReal ((y - x) ^ 2) := by
          congr 1; ring
      _ ≤ ENNReal.ofReal (2 * (x - c) ^ 2 + 2 * (y - c) ^ 2) := ENNReal.ofReal_le_ofReal h
      _ = 2 * ENNReal.ofReal ((x - c) ^ 2) + 2 * ENNReal.ofReal ((y - c) ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          simp
  have hstep : ∀ x : ℝ, volume W * ENNReal.ofReal ((x - mW) ^ 2) ≤
      ∫⁻ y in W, ENNReal.ofReal ((x - U y) ^ 2) := fun x =>
    a10_mean_dev_le hW0 hWt hUm hUi x
  have hint : ∀ x : Vec d, ∫⁻ y in W, ENNReal.ofReal ((U x - U y) ^ 2) ≤
      2 * volume W * ENNReal.ofReal ((U x - c) ^ 2) + 2 * Ec := by
    intro x
    calc ∫⁻ y in W, ENNReal.ofReal ((U x - U y) ^ 2)
        ≤ ∫⁻ y in W, (2 * ENNReal.ofReal ((U x - c) ^ 2) + 2 * ENNReal.ofReal ((U y - c) ^ 2)) :=
          lintegral_mono fun y => hpt _ _
      _ = 2 * volume W * ENNReal.ofReal ((U x - c) ^ 2) + 2 * Ec := by
          rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul' _ _
            (by norm_num), Measure.restrict_apply_univ]
          ring
  have hmeas : Measurable fun x : Vec d => ENNReal.ofReal ((U x - c) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hUm.sub_const c).pow_const 2)
  have hmain : volume W * ∫⁻ x in W, ENNReal.ofReal ((U x - mW) ^ 2) ≤ volume W * (4 * Ec) := by
    calc volume W * ∫⁻ x in W, ENNReal.ofReal ((U x - mW) ^ 2)
        = ∫⁻ x in W, volume W * ENNReal.ofReal ((U x - mW) ^ 2) :=
          (lintegral_const_mul' _ _ hWt).symm
      _ ≤ ∫⁻ x in W, (2 * volume W * ENNReal.ofReal ((U x - c) ^ 2) + 2 * Ec) :=
          lintegral_mono fun x => (hstep (U x)).trans (hint x)
      _ = volume W * (4 * Ec) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hmeas, lintegral_const,
            Measure.restrict_apply_univ]
          ring
  exact (ENNReal.mul_le_mul_iff_right hW0 hWt).1 hmain

theorem a10_volume_le_ratio {W : Set (Vec d)} {x0 : Vec d} {s D : ℝ} (hs : 0 < s) (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ W, ‖x - x0‖ ≤ D) :
    volume W ≤ ENNReal.ofReal ((D / s) ^ d) * volume (Metric.ball x0 s) := by
  have hsub : W ⊆ Metric.closedBall x0 D := fun x hx => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hdiam x hx
  calc volume W ≤ volume (Metric.closedBall x0 D) := measure_mono hsub
    _ = ENNReal.ofReal ((2 * D) ^ d) := by
        rw [Real.volume_pi_closedBall _ hD]; simp
    _ = ENNReal.ofReal ((D / s) ^ d) * ENNReal.ofReal ((2 * s) ^ d) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
        congr 2
        field_simp
    _ = ENNReal.ofReal ((D / s) ^ d) * volume (Metric.ball x0 s) := by
        rw [Real.volume_pi_ball _ hs]; simp

/-- **Mean-value Poincare on a star-ball domain**, lower-integral form. -/
theorem a10_poincare_starBall_lintegral {W : Set (Vec d)} {x0 : Vec d} {s D : ℝ}
    (hW : IsStarBallDomain W x0 s D) (u : H1Function W) :
    ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal) ^ 2) ≤
      ENNReal.ofReal (4 * d * D ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2) := by
  have hW' := hW
  obtain ⟨hWo, hs, hBW, hstar, hdiam⟩ := hW
  obtain ⟨hB0, hBt⟩ := a10_volume_ball_ne x0 hs
  have hWm : MeasurableSet W := hWo.measurableSet
  have hx0W : x0 ∈ W := hBW (Metric.mem_ball_self hs)
  have hD : 0 ≤ D := by simpa using hdiam x0 hx0W x0 hx0W
  have hdx0 : ∀ x ∈ W, ‖x - x0‖ ≤ D := fun x hx => hdiam x hx x0 hx0W
  have hWsub : W ⊆ Metric.closedBall x0 D := fun x hx => by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hdx0 x hx
  have hWt : volume W ≠ ⊤ :=
    ((measure_mono hWsub).trans_lt (measure_closedBall_lt_top (x := x0) (r := D))).ne
  have hW0 : volume W ≠ 0 := by
    intro h0
    have := measure_mono (μ := (volume : Measure (Vec d))) hBW
    rw [h0] at this
    exact hB0 (le_antisymm this zero_le)
  obtain ⟨U, G, hUm, hGm, hUl, hGl, hweak, hUae, hGae⟩ := a10_clean_data hWo u
  have hUi : IntegrableOn U W volume :=
    (hUl.integrableOn_isCompact (isCompact_closedBall x0 D)).mono_set hWsub
  have hBsub : Metric.ball x0 s ⊆ W := hBW
  have hBae : U =ᵐ[volume.restrict (Metric.ball x0 s)] u.toFun :=
    ae_restrict_of_ae_restrict_of_subset hBW hUae
  have hmeanB : ∫ b in Metric.ball x0 s, U b = ∫ b in Metric.ball x0 s, u.toFun b :=
    integral_congr_ae hBae
  have hmeanW : ∫ b in W, U b = ∫ b in W, u.toFun b := integral_congr_ae hUae
  set c : ℝ := (∫ b in Metric.ball x0 s, u.toFun b) / (volume (Metric.ball x0 s)).toReal with hc
  have hE1 := a10_meanW_le hW0 hWt hUm hUi c
  rw [hmeanW] at hE1
  have hEq : ∀ (m : ℝ), ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - m) ^ 2) =
      ∫⁻ x in W, ENNReal.ofReal ((U x - m) ^ 2) := fun m => by
    refine lintegral_congr_ae ?_
    filter_upwards [hUae] with x hx
    rw [hx]
  have h2 := a10_poincare_lintegral hW' u
  rw [← hc] at h2
  set Ec : ENNReal := ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - c) ^ 2) with hEc
  set Eg : ENNReal := ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2) with hEg
  have hratio := a10_volume_le_ratio hs hD hdx0
  have hsum : volume W + volume (Metric.ball x0 s) ≤
      (ENNReal.ofReal ((D / s) ^ d) + 1) * volume (Metric.ball x0 s) := by
    calc volume W + volume (Metric.ball x0 s)
        ≤ ENNReal.ofReal ((D / s) ^ d) * volume (Metric.ball x0 s) + volume (Metric.ball x0 s) :=
          add_le_add_left hratio _
      _ = (ENNReal.ofReal ((D / s) ^ d) + 1) * volume (Metric.ball x0 s) := by ring
  have h3 : volume (Metric.ball x0 s) * Ec ≤ volume (Metric.ball x0 s) *
      (ENNReal.ofReal (d * D ^ 2) * 2 ^ d * (ENNReal.ofReal ((D / s) ^ d) + 1) * Eg) := by
    refine h2.trans ?_
    calc ENNReal.ofReal (d * D ^ 2) * (2 ^ d * (volume W + volume (Metric.ball x0 s))) * Eg
        ≤ ENNReal.ofReal (d * D ^ 2) * (2 ^ d * ((ENNReal.ofReal ((D / s) ^ d) + 1) *
            volume (Metric.ball x0 s))) * Eg := by gcongr
      _ = volume (Metric.ball x0 s) *
          (ENNReal.ofReal (d * D ^ 2) * 2 ^ d * (ENNReal.ofReal ((D / s) ^ d) + 1) * Eg) := by
          ring
  have h4 : Ec ≤ ENNReal.ofReal (d * D ^ 2) * 2 ^ d * (ENNReal.ofReal ((D / s) ^ d) + 1) * Eg :=
    (ENNReal.mul_le_mul_iff_right hB0 hBt).1 h3
  have hconst : ENNReal.ofReal (4 * d * D ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) =
      4 * (ENNReal.ofReal (d * D ^ 2) * 2 ^ d * (ENNReal.ofReal ((D / s) ^ d) + 1)) := by
    have hq : 0 ≤ (D / s) ^ d := by positivity
    have e : 4 * (d : ℝ) * D ^ 2 * 2 ^ d * (1 + (D / s) ^ d) =
        4 * ((d * D ^ 2) * 2 ^ d * ((D / s) ^ d + 1)) := by ring
    rw [e, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hq zero_le_one]
    simp
  rw [hEq, hconst]
  refine hE1.trans ?_
  rw [← hEq c]
  calc 4 * Ec ≤ 4 * (ENNReal.ofReal (d * D ^ 2) * 2 ^ d * (ENNReal.ofReal ((D / s) ^ d) + 1) * Eg) :=
        by gcongr
    _ = 4 * (ENNReal.ofReal (d * D ^ 2) * 2 ^ d * (ENNReal.ofReal ((D / s) ^ d) + 1)) * Eg := by
        ring

theorem a10_eLpNorm_le_of_lintegral {μ : Measure (Vec d)} {f g : Vec d → ℝ} {κ : ℝ}
    (hκ : 0 ≤ κ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (h : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal κ * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt κ) * eLpNorm g 2 μ := by
  have hE : ∀ (k : Vec d → ℝ), ∀ x, ‖k x‖ₑ ^ ((2 : ENNReal).toReal) = ENNReal.ofReal (k x ^ 2) :=
    fun k x => by
      rw [ENNReal.toReal_ofNat, Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  simp only [hE]
  have h2 : (0 : ℝ) ≤ 1 / (2 : ENNReal).toReal := by norm_num
  calc (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / (2 : ENNReal).toReal)
      ≤ (ENNReal.ofReal κ * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) ^ (1 / (2 : ENNReal).toReal) :=
        ENNReal.rpow_le_rpow h h2
    _ = ENNReal.ofReal κ ^ (1 / (2 : ENNReal).toReal) *
          (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) ^ (1 / (2 : ENNReal).toReal) :=
        ENNReal.mul_rpow_of_nonneg _ _ h2
    _ = ENNReal.ofReal (Real.sqrt κ) *
          (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) ^ (1 / (2 : ENNReal).toReal) := by
        congr 1
        rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg hκ (by norm_num),
          Real.sqrt_eq_rpow]

theorem a10_sum_sq_le (g : Vec d) : ∑ i, g i ^ 2 ≤ d * ‖g‖ ^ 2 := by
  have := a10_vecNormSq_le g
  unfold vecNormSq vecDot at this
  simpa [sq] using this

/-- **Mean-value Poincare on a star-ball domain.** For every `u ∈ H¹(W)`,
`‖u - ū_W‖_{L²(W)} ≤ 2 d 2^{d/2} (1 + (D/s)^d)^{1/2} D ‖∇u‖_{L²(W)}` (the gradient measured in the
sup norm of `Vec d`). -/
theorem a10_poincare_starBall {W : Set (Vec d)} {x0 : Vec d} {s D : ℝ}
    (hW : IsStarBallDomain W x0 s D) (u : H1Function W) :
    eLpNorm (fun x => u.toFun x - (∫ y in W, u.toFun y) / (volume W).toReal) 2
        (volume.restrict W) ≤
      ENNReal.ofReal (Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) * D) *
        eLpNorm (fun x => ‖u.grad x‖) 2 (volume.restrict W) := by
  have hW' := hW
  obtain ⟨hWo, hs, hBW, -, hdiam⟩ := hW
  have hx0W : x0 ∈ W := hBW (Metric.mem_ball_self hs)
  have hD : 0 ≤ D := by simpa using hdiam x0 hx0W x0 hx0W
  have hq : 0 ≤ (D / s) ^ d := by positivity
  set κ : ℝ := 4 * (d : ℝ) ^ 2 * D ^ 2 * 2 ^ d * (1 + (D / s) ^ d) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hsq : Real.sqrt κ = Real.sqrt (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) * D := by
    have : κ = (4 * (d : ℝ) ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) * D ^ 2 := by rw [hκ]; ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hD]
  have hmeas_f : AEStronglyMeasurable (fun x => u.toFun x -
      (∫ y in W, u.toFun y) / (volume W).toReal) (volume.restrict W) :=
    u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hmeas_g : AEStronglyMeasurable (fun x => ‖u.grad x‖) (volume.restrict W) := by
    have : AEMeasurable u.grad (volume.restrict W) :=
      aemeasurable_pi_iff.2 fun i => (u.gradMemL2 i).aestronglyMeasurable.aemeasurable
    exact this.norm.aestronglyMeasurable
  rw [← hsq]
  refine a10_eLpNorm_le_of_lintegral hκ0 hmeas_f hmeas_g ?_
  have h1 := a10_poincare_starBall_lintegral hW' u
  refine h1.trans ?_
  have hpt : ∀ z, ENNReal.ofReal (∑ i, u.grad z i ^ 2) ≤
      ENNReal.ofReal d * ENNReal.ofReal (‖u.grad z‖ ^ 2) := fun z => by
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    exact ENNReal.ofReal_le_ofReal (a10_sum_sq_le _)
  calc ENNReal.ofReal (4 * d * D ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2)
      ≤ ENNReal.ofReal (4 * d * D ^ 2 * 2 ^ d * (1 + (D / s) ^ d)) *
        ∫⁻ z in W, ENNReal.ofReal d * ENNReal.ofReal (‖u.grad z‖ ^ 2) := by
        gcongr with z
        exact hpt z
    _ = ENNReal.ofReal κ * ∫⁻ z in W, ENNReal.ofReal (‖u.grad z‖ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [hκ]; ring

end SuperdiffusionCLT.Section7
