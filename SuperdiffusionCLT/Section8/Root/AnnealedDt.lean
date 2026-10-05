/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The annealed variance bound: moments with constants independent of the law

Two pieces of real analysis, with every constant explicit:

* a random variable on a probability space whose tail beyond `a` is bounded by
  `B exp (-(s / a)^2)` has `q`-th moment at most an explicit constant `annDt_M a B q` depending only on
  `a, B, q` (the layer-cake argument; the constant does not depend on the space or the law);
* the splitting of an integral along a good and a bad event, the bad event being treated by the
  Cauchy-Schwarz inequality against a majorant with a bounded fourth-power-type moment.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The explicit integrand whose integral bounds the layer-cake integral. -/
def annDt_h (a B q : ℝ) (t : ℝ) : ℝ :=
  (Ioc 0 a).indicator (fun t => t ^ (q - 1)) t + B * (t ^ (q - 1) * Real.exp (-(1 / a ^ 2) * t ^ 2))

/-- The uniform constant of the moment bound. -/
def annDt_M (a B q : ℝ) : ℝ :=
  (ENNReal.ofReal q * ∫⁻ t in Ioi 0, ENNReal.ofReal (annDt_h a B q t)).toReal

theorem annDt_h_integrableOn {a B q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    IntegrableOn (annDt_h a B q) (Ioi 0) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Ioc 0 a) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := a) (r := q - 1)
      (by linarith only [hq]))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).1 this
  have h1' : IntegrableOn (fun t : ℝ => t ^ (q - 1)) (Ioc 0 a) (volume.restrict (Ioi 0)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 Ioc_subset_Ioi_self]
    exact h1
  have h2 : IntegrableOn ((Ioc 0 a).indicator fun t : ℝ => t ^ (q - 1)) (Ioi 0) :=
    (integrable_indicator_iff measurableSet_Ioc).2 h1'
  have h3 := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / a ^ 2) (by positivity)
    (s := q - 1) (by linarith only [hq])
  exact h2.add (h3.const_mul B)

theorem annDt_M_lt_top {a B q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    ENNReal.ofReal q * ∫⁻ t in Ioi 0, ENNReal.ofReal (annDt_h a B q t) ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (annDt_h_integrableOn (B := B) ha hq).lintegral_lt_top.ne

/-- **Uniform moment bound from a Gaussian tail.**  The constant depends only on `a, B, q`. -/
theorem annDt_lintegral_rpow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {a B : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B)
    (htail : ∀ s : ℝ, a ≤ s → μ {ω | s < X ω} ≤ ENNReal.ofReal (B * Real.exp (-((s / a) ^ 2))))
    {q : ℝ} (hq : 0 < q) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ q) ∂μ ≤ ENNReal.ofReal (annDt_M a B q) := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (Filter.Eventually.of_forall hX0)
    hX.aemeasurable hq]
  rw [annDt_M, ENNReal.ofReal_toReal (annDt_M_lt_top ha hq)]
  refine mul_le_mul_right ?_ _
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hpow : 0 ≤ t ^ (q - 1) := Real.rpow_nonneg ht0.le _
  have hμ : μ {ω | t < X ω} ≤ ENNReal.ofReal ((Ioc 0 a).indicator (fun _ => (1 : ℝ)) t +
      B * Real.exp (-(1 / a ^ 2) * t ^ 2)) := by
    by_cases hta : t ≤ a
    · have hmem : t ∈ Ioc 0 a := ⟨ht0, hta⟩
      have h1 : μ {ω | t < X ω} ≤ 1 := by
        calc μ {ω | t < X ω} ≤ μ univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ
      refine h1.trans ?_
      rw [Set.indicator_of_mem hmem]
      have : 0 ≤ B * Real.exp (-(1 / a ^ 2) * t ^ 2) := by positivity
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith only [this])
    · have hta' : a ≤ t := (not_le.1 hta).le
      refine (htail t hta').trans (ENNReal.ofReal_le_ofReal ?_)
      have e : -((t / a) ^ 2) = -(1 / a ^ 2) * t ^ 2 := by field_simp
      rw [e]
      have : 0 ≤ (Ioc 0 a).indicator (fun _ => (1 : ℝ)) t :=
        indicator_nonneg (fun _ _ => zero_le_one) _
      linarith only [this]
  have hI : 0 ≤ (Ioc 0 a).indicator (fun _ => (1 : ℝ)) t :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  have hE : 0 ≤ B * Real.exp (-(1 / a ^ 2) * t ^ 2) := by positivity
  calc μ {ω | t < X ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
      ENNReal.ofReal ((Ioc 0 a).indicator (fun _ => (1 : ℝ)) t +
        B * Real.exp (-(1 / a ^ 2) * t ^ 2)) * ENNReal.ofReal (t ^ (q - 1)) := by gcongr
    _ = ENNReal.ofReal (((Ioc 0 a).indicator (fun _ => (1 : ℝ)) t +
        B * Real.exp (-(1 / a ^ 2) * t ^ 2)) * t ^ (q - 1)) := by
        rw [← ENNReal.ofReal_mul (by linarith only [hI, hE])]
    _ = ENNReal.ofReal (annDt_h a B q t) := by
        congr 1
        unfold annDt_h
        by_cases hta : t ∈ Ioc 0 a
        · simp only [Set.indicator_of_mem hta]; ring
        · simp only [Set.indicator_of_notMem hta]; ring

/-- A power of `L` against a stretched exponential decay is bounded. -/
theorem annDt_pow_exp_le {q κ β : ℝ} (hκ : 0 < κ) (hβ : 0 < β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ L : ℝ, 1 ≤ L → L ^ q * Real.exp (-(κ * L ^ β)) ≤ M := by
  obtain ⟨k, hk⟩ := exists_nat_ge (q / β)
  refine ⟨(k.factorial : ℝ) / κ ^ k, by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := by linarith only [hL]
  have hLb : 0 ≤ L ^ β := Real.rpow_nonneg hL0.le _
  have h1 : (κ * L ^ β) ^ k / (k.factorial : ℝ) ≤ Real.exp (κ * L ^ β) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have h2 : L ^ q ≤ L ^ (β * k) := Real.rpow_le_rpow_of_exponent_le hL (by
    have := (div_le_iff₀ hβ).1 hk
    linarith only [this])
  have h3 : L ^ (β * k) = (L ^ β) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hκk : (0 : ℝ) < κ ^ k := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc L ^ q ≤ (L ^ β) ^ k := h2.trans h3.le
    _ = (κ * L ^ β) ^ k / κ ^ k := by rw [mul_pow]; field_simp
    _ ≤ ((k.factorial : ℝ) * Real.exp (κ * L ^ β)) / κ ^ k := by
        gcongr
        rw [div_le_iff₀ hfac] at h1
        linarith only [h1]
    _ = (k.factorial : ℝ) / κ ^ k * Real.exp (κ * L ^ β) := by ring

/-! ## The good/bad splitting -/

end

end SuperdiffusionCLT.Section8
