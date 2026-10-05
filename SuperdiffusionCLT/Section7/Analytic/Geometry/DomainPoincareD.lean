/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareC

/-!
# Poincare inequalities on star-ball domains: the lower-integral form

`Section7.IsStarBallDomain W x0 s D`: `W` is open, star-shaped with respect to every point of the
cube `ball x0 s ⊆ W`, of diameter at most `D`. For `u : H1Function W`,
`Section7.a10_poincare_lintegral` bounds `|B| ∫_W |u - u_B|²` by
`d D² 2^d (|W| + |B|) ∫_W |∇u|²`, where `u_B` is the mean over the cube `B`.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem a10_integral_indicator_mul {W : Set (Vec d)} (hWm : MeasurableSet W) (f c : Vec d → ℝ) :
    ∫ x, W.indicator f x * c x = ∫ x in W, f x * c x := by
  have : ∀ x, W.indicator f x * c x = W.indicator (fun x => f x * c x) x := by
    intro x
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  simp only [this]
  exact integral_indicator hWm

/-- Measurable global representatives of an `H¹(W)` function and its weak gradient. -/
theorem a10_clean_data {W : Set (Vec d)} (hW : IsOpen W) (u : H1Function W) :
    ∃ (U : Vec d → ℝ) (G : Fin d → Vec d → ℝ), Measurable U ∧ (∀ i, Measurable (G i)) ∧
      LocallyIntegrable U volume ∧ (∀ i, LocallyIntegrable (G i) volume) ∧
      (∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ W → ∫ x, U x * fderiv ℝ φ x (basisVec i) = -∫ x, G i x * φ x) ∧
      U =ᵐ[volume.restrict W] u.toFun ∧
      ∀ i, G i =ᵐ[volume.restrict W] fun x => u.grad x i := by
  have hWm : MeasurableSet W := hW.measurableSet
  have hu := u.memL2
  set u' : Vec d → ℝ := hu.aestronglyMeasurable.mk u.toFun with hu'
  have hu'm : Measurable u' := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : u.toFun =ᵐ[volume.restrict W] u' := hu.aestronglyMeasurable.ae_eq_mk
  have hgm : ∀ i : Fin d, AEStronglyMeasurable (fun x => u.grad x i) (volume.restrict W) :=
    fun i => (u.gradMemL2 i).aestronglyMeasurable
  set g' : Fin d → Vec d → ℝ := fun i => (hgm i).mk (fun x => u.grad x i) with hg'
  have hg'm : ∀ i, Measurable (g' i) := fun i => (hgm i).stronglyMeasurable_mk.measurable
  have hgae : ∀ i, (fun x => u.grad x i) =ᵐ[volume.restrict W] g' i := fun i => (hgm i).ae_eq_mk
  refine ⟨W.indicator u', fun i => W.indicator (g' i), hu'm.indicator hWm,
    fun i => (hg'm i).indicator hWm, ?_, fun i => ?_, fun i φ hφ hφc hφW => ?_, ?_, fun i => ?_⟩
  · have : MemLp (W.indicator u') 2 volume :=
      (memLp_indicator_iff_restrict hWm).2 (hu.ae_eq hae)
    exact this.locallyIntegrable (by norm_num)
  · have : MemLp (W.indicator (g' i)) 2 volume :=
      (memLp_indicator_iff_restrict hWm).2 ((u.gradMemL2 i).ae_eq (hgae i))
    exact this.locallyIntegrable (by norm_num)
  · have h1 : ∫ x, W.indicator u' x * fderiv ℝ φ x (basisVec i) =
        ∫ x in W, u.toFun x * fderiv ℝ φ x (basisVec i) := by
      rw [a10_integral_indicator_mul hWm]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    have h2 : ∫ x, W.indicator (g' i) x * φ x = ∫ x in W, u.grad x i * φ x := by
      rw [a10_integral_indicator_mul hWm]
      refine integral_congr_ae ?_
      filter_upwards [hgae i] with x hx
      rw [hx]
    rw [h1, h2]
    exact u.hasWeakGradient i φ hφ hφc hφW
  · exact (indicator_ae_eq_restrict hWm).trans hae.symm
  · exact (indicator_ae_eq_restrict hWm).trans (hgae i).symm

/-- Jensen's inequality for the square, for a finite measure. -/
theorem a10_jensen_sq_gen {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf : Measurable f) :
    ENNReal.ofReal ((∫ a, f a ∂μ) ^ 2) ≤ μ univ * ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ := by
  have h1 : ‖∫ a, f a ∂μ‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
  have h2 : (∫⁻ a, ‖f a‖ₑ ∂μ) ≤
      (∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (μ univ) ^ (1 / (2 : ℝ)) := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
      (Real.HolderConjugate.two_two) (f := fun a => ‖f a‖ₑ) (g := fun _ => (1 : ENNReal))
      hf.enorm.aemeasurable aemeasurable_const
    simpa using this
  have h3 : ENNReal.ofReal ((∫ a, f a ∂μ) ^ 2) = ‖∫ a, f a ∂μ‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h4 : ∀ a, ‖f a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f a ^ 2) := fun a => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [h3]
  calc ‖∫ a, f a ∂μ‖ₑ ^ 2 ≤ (∫⁻ a, ‖f a‖ₑ ∂μ) ^ 2 := by gcongr
    _ ≤ ((∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (μ univ) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = (∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ) * μ univ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _ : ENNReal), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        simp [h4]
    _ = μ univ * ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ := mul_comm _ _

/-- The deviation of a value from the mean over `B`, via Jensen. -/
theorem a10_mean_dev_le {B : Set (Vec d)} (hB0 : volume B ≠ 0)
    (hBt : volume B ≠ ⊤) {u : Vec d → ℝ} (hum : Measurable u) (hui : IntegrableOn u B volume)
    (c : ℝ) :
    volume B * ENNReal.ofReal ((c - (∫ b in B, u b) / (volume B).toReal) ^ 2) ≤
      ∫⁻ b in B, ENNReal.ofReal ((c - u b) ^ 2) := by
  have hvB : 0 < (volume B).toReal := ENNReal.toReal_pos hB0 hBt
  set m : ℝ := (∫ b in B, u b) / (volume B).toReal with hm
  have hint : ∫ b in B, (c - u b) = (volume B).toReal * (c - m) := by
    have hfin : IsFiniteMeasure (volume.restrict B) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hBt⟩
    have hc : Integrable (fun _ : Vec d => c) (volume.restrict B) := integrable_const c
    rw [integral_sub hc hui, integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, hm]
    field_simp
  have hJ := a10_jensen_sq_gen (volume.restrict B) (f := fun b => c - u b)
    (measurable_const.sub hum)
  rw [hint, Measure.restrict_apply_univ] at hJ
  have hL : ENNReal.ofReal (((volume B).toReal * (c - m)) ^ 2) =
      volume B * (volume B * ENNReal.ofReal ((c - m) ^ 2)) := by
    rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow hvB.le,
      ENNReal.ofReal_toReal hBt, sq, mul_assoc]
  rw [hL] at hJ
  exact (ENNReal.mul_le_mul_iff_right hB0 hBt).1 hJ

/-- A bounded open set that is star-shaped with respect to every point of the cube `ball x0 s`
(the sup-norm ball), with diameter bound `D`. -/
def IsStarBallDomain (W : Set (Vec d)) (x0 : Vec d) (s D : ℝ) : Prop :=
  IsOpen W ∧ 0 < s ∧ Metric.ball x0 s ⊆ W ∧
    (∀ x ∈ W, ∀ b ∈ Metric.ball x0 s, ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • x + t • b ∈ W) ∧
    ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ D

theorem a10_volume_ball_ne (x0 : Vec d) {s : ℝ} (hs : 0 < s) :
    volume (Metric.ball x0 s) ≠ 0 ∧ volume (Metric.ball x0 s) ≠ ⊤ := by
  refine ⟨?_, ?_⟩
  · exact (Metric.isOpen_ball.measure_pos volume ⟨x0, Metric.mem_ball_self hs⟩).ne'
  · exact (measure_ball_lt_top (x := x0) (r := s)).ne

/-- The mean-value Poincare inequality for star-ball domains, in lower-integral form, with the
mean over the cube `B`. -/
theorem a10_poincare_lintegral {W : Set (Vec d)} {x0 : Vec d} {s D : ℝ}
    (hW : IsStarBallDomain W x0 s D) (u : H1Function W) :
    volume (Metric.ball x0 s) *
        ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - (∫ b in Metric.ball x0 s, u.toFun b) /
          (volume (Metric.ball x0 s)).toReal) ^ 2) ≤
      ENNReal.ofReal (d * D ^ 2) * (2 ^ d * (volume W + volume (Metric.ball x0 s))) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2) := by
  obtain ⟨hWo, hs, hBW, hstar, hdiam⟩ := hW
  obtain ⟨hB0, hBt⟩ := a10_volume_ball_ne x0 hs
  have hBm : MeasurableSet (Metric.ball x0 s) := Metric.isOpen_ball.measurableSet
  have hWm : MeasurableSet W := hWo.measurableSet
  obtain ⟨U, G, hUm, hGm, hUl, hGl, hweak, hUae, hGae⟩ := a10_clean_data hWo u
  have hD : ∀ x ∈ W, ∀ b ∈ Metric.ball x0 s, ‖b - x‖ ≤ D := fun x hx b hb => by
    rw [norm_sub_rev]; exact hdiam x hx b (hBW hb)
  have hdd := a10_double_integral_le hWo hBm hstar hD hUm hGm hUl hGl hweak
  have hBae : U =ᵐ[volume.restrict (Metric.ball x0 s)] u.toFun :=
    ae_restrict_of_ae_restrict_of_subset hBW hUae
  have hmean : ∫ b in Metric.ball x0 s, U b = ∫ b in Metric.ball x0 s, u.toFun b :=
    integral_congr_ae hBae
  have hui : IntegrableOn U (Metric.ball x0 s) volume :=
    hUl.integrableOn_isCompact (isCompact_closedBall x0 s) |>.mono_set Metric.ball_subset_closedBall
  have hstep : ∀ x : Vec d, volume (Metric.ball x0 s) *
      ENNReal.ofReal ((U x - (∫ b in Metric.ball x0 s, U b) /
        (volume (Metric.ball x0 s)).toReal) ^ 2) ≤
      ∫⁻ b in Metric.ball x0 s, ENNReal.ofReal ((U b - U x) ^ 2) := by
    intro x
    refine (a10_mean_dev_le hB0 hBt hUm hui (U x)).trans (le_of_eq ?_)
    refine lintegral_congr fun b => ?_
    congr 1
    ring
  calc volume (Metric.ball x0 s) *
        ∫⁻ x in W, ENNReal.ofReal ((u.toFun x - (∫ b in Metric.ball x0 s, u.toFun b) /
          (volume (Metric.ball x0 s)).toReal) ^ 2)
      = volume (Metric.ball x0 s) *
        ∫⁻ x in W, ENNReal.ofReal ((U x - (∫ b in Metric.ball x0 s, U b) /
          (volume (Metric.ball x0 s)).toReal) ^ 2) := by
        rw [hmean]
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [hUae] with x hx
        rw [hx]
    _ = ∫⁻ x in W, volume (Metric.ball x0 s) *
        ENNReal.ofReal ((U x - (∫ b in Metric.ball x0 s, U b) /
          (volume (Metric.ball x0 s)).toReal) ^ 2) :=
        (lintegral_const_mul' _ _ hBt).symm
    _ ≤ ∫⁻ x in W, ∫⁻ b in Metric.ball x0 s, ENNReal.ofReal ((U b - U x) ^ 2) :=
        lintegral_mono hstep
    _ ≤ ENNReal.ofReal (d * D ^ 2) * (2 ^ d * (volume W + volume (Metric.ball x0 s))) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, G i z ^ 2) := hdd
    _ = ENNReal.ofReal (d * D ^ 2) * (2 ^ d * (volume W + volume (Metric.ball x0 s))) *
        ∫⁻ z in W, ENNReal.ofReal (∑ i, u.grad z i ^ 2) := by
        congr 1
        refine lintegral_congr_ae ?_
        have hall : ∀ᵐ z ∂(volume.restrict W), ∀ i, G i z = u.grad z i := by
          rw [ae_all_iff]; exact hGae
        filter_upwards [hall] with z hz
        simp [hz]

end SuperdiffusionCLT.Section7
