/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.LocalizeSwitch
public import SuperdiffusionCLT.Section5.Thresholds.ScaleArithmetic
public import SuperdiffusionCLT.Section2.Estimates.Stream.TranslatedIncrementLinfty

/-!
# The fourth moment of `D_z` (`e.principal.Dz.moment`)

`(avsum_z E[D_z^4])^{1/4} ≤ C m^{-100}`. The deterministic bound `principal_Dz_le` reduces `D_z` to
the derivative gauge `g` of the translated shell sequence; `g` is `Γ₂` with amplitude `γ 3^{-(m-h)}`
(`isBigOWith_gammaSigma_finiteShellDerivGauge_translate`, uniform in the translation, which is the
stationarity of the shell law), so its eighth moment is `(c γ 3^{-(m-h)})^8`. The scale
`n = ⌊m - h - 100 log_3(ν⁻¹ m)⌋` gives `3^n 3^{-(m-h)} ≤ (ν/m)^{100}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

variable {d : ℕ}

/-- `(x + x²)⁴ ≤ 8 (x⁴ + x⁸)` for `x ≥ 0`. -/
theorem add_sq_pow_four_le {x : ℝ} : (x + x ^ 2) ^ 4 ≤ 8 * (x ^ 4 + x ^ 8) := by
  have h1 : (x + x ^ 2) ^ 2 ≤ 2 * (x ^ 2 + (x ^ 2) ^ 2) := by
    nlinarith only [sq_nonneg (x - x ^ 2)]
  have h2 : (x ^ 2 + (x ^ 2) ^ 2) ^ 2 ≤ 2 * ((x ^ 2) ^ 2 + ((x ^ 2) ^ 2) ^ 2) := by
    nlinarith only [sq_nonneg (x ^ 2 - (x ^ 2) ^ 2)]
  have h0 : 0 ≤ (x + x ^ 2) ^ 2 := sq_nonneg _
  calc (x + x ^ 2) ^ 4 = ((x + x ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (x ^ 2 + (x ^ 2) ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * (x ^ 2 + (x ^ 2) ^ 2) ^ 2 := by ring
    _ ≤ 4 * (2 * ((x ^ 2) ^ 2 + ((x ^ 2) ^ 2) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 8 * (x ^ 4 + x ^ 8) := by ring

/-- The scale `n` of `e.n.def.recurrence` is `≤ m - h - 100 log_3(ν⁻¹ m)`. -/
theorem principal_scale_le {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {m h n : ℕ}
    (h400 : 400 * h ≤ m) (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊) :
    (n : ℝ) ≤ (m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have h400' : 400 * (h : ℝ) ≤ m := by exact_mod_cast h400
  have hm0 : 0 < (m : ℝ) := by linarith only [hm']
  have hy1 : 1 ≤ nu⁻¹ * m := by
    have : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
    nlinarith only [this, hm']
  have hy0 : 0 < nu⁻¹ * m := by positivity
  have hl3 : 1 < Real.log 3 := one_lt_log_three
  have hlogy : Real.log (nu⁻¹ * m) ≤ 2 * Real.log m := by
    have : nu⁻¹ * (m : ℝ) ≤ (m : ℝ) * m := mul_le_mul_of_nonneg_right hnum hm0.le
    have := Real.log_le_log hy0 this
    rw [Real.log_mul hm0.ne' hm0.ne'] at this
    linarith only [this]
  have hlogy0 : 0 ≤ Real.log (nu⁻¹ * m) := Real.log_nonneg hy1
  have hlogb : Real.logb 3 (nu⁻¹ * m) ≤ Real.log (nu⁻¹ * m) := by
    rw [Real.logb]
    exact div_le_self hlogy0 hl3.le
  have hsq := log_le_two_sqrt hm0
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hss : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have hs1000 : 1000 ≤ Real.sqrt m := by
    rw [show (1000 : ℝ) = Real.sqrt (1000 ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith only [hm'])
  have hnonneg : 0 ≤ (m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m) := by
    nlinarith only [hlogb, hlogy, hsq, hss, hs1000, h400', hs0]
  rw [hn]
  exact Nat.floor_le hnonneg

/-- `3^n / 3^{m-h} ≤ (ν/m)^{100}`. -/
theorem principal_pow_ratio_le {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {m h n : ℕ}
    (h400 : 400 * h ≤ m) (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊) :
    (3 : ℝ) ^ n * ((3 : ℝ) ^ (m - h))⁻¹ ≤ (nu / m) ^ 100 := by
  have hle := principal_scale_le hnu hnu1 h400 hm hnum hn
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith only [hm']
  have hhm : h ≤ m := by omega
  have hy0 : 0 < nu⁻¹ * m := by positivity
  have hcast : ((m - h : ℕ) : ℝ) = (m : ℝ) - h := Nat.cast_sub hhm
  have h1 : (3 : ℝ) ^ (n : ℝ) ≤ (3 : ℝ) ^ ((m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
  have h2 : (3 : ℝ) ^ ((m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)) =
      (3 : ℝ) ^ (m - h) * ((nu⁻¹ * m) ^ 100)⁻¹ := by
    rw [Real.rpow_sub (by norm_num), ← hcast, Real.rpow_natCast, mul_comm (100 : ℝ),
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hy0]
    rw [show ((100 : ℝ)) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  have h3 : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (m - h) * ((nu⁻¹ * m) ^ 100)⁻¹ := by
    rw [← h2, ← Real.rpow_natCast]
    exact h1
  have hpos : 0 < (3 : ℝ) ^ (m - h) := by positivity
  calc (3 : ℝ) ^ n * ((3 : ℝ) ^ (m - h))⁻¹
      ≤ ((3 : ℝ) ^ (m - h) * ((nu⁻¹ * m) ^ 100)⁻¹) * ((3 : ℝ) ^ (m - h))⁻¹ :=
        mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hpos.le)
    _ = (nu / m) ^ 100 := by
        field_simp

/-! ## The moments of the derivative gauge -/

/-- The `p`-th moment constant `γ_2-moment · p^{1/2}` of the stretched-exponential class. -/
noncomputable def gaugeMomentConst (p : ℕ) : ℝ :=
  Homogenization.IndependentSums.gammaMomentConst 2 * (p : ℝ) ^ ((2 : ℝ)⁻¹)

theorem gaugeMomentConst_pos (p : ℕ) (hp : 1 ≤ p) : 0 < gaugeMomentConst p := by
  unfold gaugeMomentConst
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  exact mul_pos (Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num))
    (Real.rpow_pos_of_pos hp0 _)

/-- The `p`-th moment of the derivative gauge of the translated shell sequence, `p ≥ 1`:
integrable, and at most `(γ_p · c γ 3^{-(m-h)})^p`, uniformly in the translation. -/
theorem gauge_moment [NeZero d] {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {m h : ℕ} (hh : 1 ≤ h) (hhm : h ≤ m)
    (z : Vec d) (p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun ω : ShellSeq d =>
        finiteShellDerivGauge (m - h) m (ShellField.translateSequence z ω) ^ p) P.toMeasure ∧
      ∫ ω, finiteShellDerivGauge (m - h) m (ShellField.translateSequence z ω) ^ p ∂P.toMeasure ≤
        (gaugeMomentConst p *
          (Homogenization.IndependentSums.gammaTriangleConst 2 * ((3 : ℝ) ^ (m - h))⁻¹)) ^ p := by
  have hnm : m - h < m := by omega
  have hbig := isBigOWith_gammaSigma_finiteShellDerivGauge_translate hPrefix hJ3 hnm z
  have hK : 0 < Homogenization.IndependentSums.gammaTriangleConst 2 * ((3 : ℝ) ^ (m - h))⁻¹ :=
    mul_pos Homogenization.IndependentSums.gammaTriangleConst_pos (by positivity)
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hY : ∀ ω : ShellSeq d,
      0 ≤ finiteShellDerivGauge (m - h) m (ShellField.translateSequence z ω) :=
    fun ω => finiteShellDerivGauge_nonneg _ _ _
  have hmeas := (measurable_finiteShellDerivGauge_translate z (m - h) m).aemeasurable (μ := P.toMeasure)
  constructor
  · have := Homogenization.IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (μ := P.toMeasure) (σ := 2) (p := (p : ℝ)) (by norm_num) hK hp' hY hmeas hbig
    simpa only [Real.rpow_natCast] using this
  · have := Homogenization.IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
      (μ := P.toMeasure) (σ := 2) (p := (p : ℝ)) (by norm_num) hK hp' hY hmeas hbig
    simpa only [Real.rpow_natCast, gaugeMomentConst] using this

/-! ## The fourth moment of `D_z` -/

/-- The constant `K = c γ (γ_4 + γ_8)` of the moment bound, `c = d √d`. -/
noncomputable def dzMomentConst (d : ℕ) : ℝ :=
  ((d : ℝ) * Real.sqrt d) * Homogenization.IndependentSums.gammaTriangleConst 2 *
    (gaugeMomentConst 4 + gaugeMomentConst 8)

theorem dzMomentConst_nonneg (d : ℕ) : 0 ≤ dzMomentConst d := by
  unfold dzMomentConst
  have h4 := gaugeMomentConst_pos 4 (by norm_num)
  have h8 := gaugeMomentConst_pos 8 (by norm_num)
  have hg := Homogenization.IndependentSums.gammaTriangleConst_pos (σ := 2)
  have : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d := by positivity
  positivity

/-- One cube: `E[D_z^4] ≤ 8 (T^4 + T^8)` with `T = K m^{-100}`. -/
theorem principal_Dz_pow4_integral_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {m h n : ℕ} (hh : 1 ≤ h)
    (h400 : 400 * h ≤ m) (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊)
    (R : TriadicCube d) (hR : R.scale = (n : ℤ)) :
    ∫ ω, principalDz nu m h R ω ^ 4 ∂P.toMeasure ≤
      8 * ((dzMomentConst d * ((m : ℝ) ^ 100)⁻¹) ^ 4 + (dzMomentConst d * ((m : ℝ) ^ 100)⁻¹) ^ 8) := by
  have hhm : h ≤ m := by omega
  have hnm : n ≤ m - h := by
    have := principal_scale_le hnu hnu1 h400 hm hnum hn
    have hcast : ((m - h : ℕ) : ℝ) = (m : ℝ) - h := Nat.cast_sub hhm
    have hl : 0 ≤ Real.logb 3 (nu⁻¹ * m) := by
      apply Real.logb_nonneg (by norm_num)
      have : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).mpr hnu1
      have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith only [this, hm']
    have : (n : ℝ) ≤ ((m - h : ℕ) : ℝ) := by rw [hcast]; linarith only [this, hl]
    exact_mod_cast this
  set cc : ℝ := (d : ℝ) * Real.sqrt d with hcc
  set γ : ℝ := Homogenization.IndependentSums.gammaTriangleConst 2 with hγ
  set z : Vec d := cubeCenter R with hz
  set g : ShellSeq d → ℝ := fun ω =>
    finiteShellDerivGauge (m - h) m (ShellField.translateSequence z ω) with hg
  set α : ℝ := nu⁻¹ * cc * (3 : ℝ) ^ n with hα
  have hα0 : 0 ≤ α := by positivity
  have hpoint : ∀ ω, principalDz nu m h R ω ^ 4 ≤ 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) := by
    intro ω
    have hD := principal_Dz_le hnu hnm R hR ω
    have hD0 := principalDz_nonneg hnu m h R ω
    have hg0 : 0 ≤ g ω := finiteShellDerivGauge_nonneg _ _ _
    have hx : 0 ≤ α * g ω := mul_nonneg hα0 hg0
    have hD' : principalDz nu m h R ω ≤ α * g ω + (α * g ω) ^ 2 := by
      refine le_trans hD (le_of_eq ?_)
      rw [hα, hg]
      ring
    calc principalDz nu m h R ω ^ 4 ≤ (α * g ω + (α * g ω) ^ 2) ^ 4 :=
          pow_le_pow_left₀ hD0 hD' 4
      _ ≤ 8 * ((α * g ω) ^ 4 + (α * g ω) ^ 8) := add_sq_pow_four_le
      _ = 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) := by ring
  obtain ⟨hi4, hm4⟩ := gauge_moment hPrefix hJ3 hh hhm z 4 (by norm_num)
  obtain ⟨hi8, hm8⟩ := gauge_moment hPrefix hJ3 hh hhm z 8 (by norm_num)
  have hint : Integrable (fun ω => 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8)) P.toMeasure :=
    ((hi4.const_mul (α ^ 4)).add (hi8.const_mul (α ^ 8))).const_mul 8
  have h1 : ∫ ω, principalDz nu m h R ω ^ 4 ∂P.toMeasure ≤
      ∫ ω, 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) ∂P.toMeasure :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      pow_nonneg (principalDz_nonneg hnu m h R ω) 4) hint (Filter.Eventually.of_forall hpoint)
  have h2 : ∫ ω, 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) ∂P.toMeasure =
      8 * (α ^ 4 * ∫ ω, g ω ^ 4 ∂P.toMeasure + α ^ 8 * ∫ ω, g ω ^ 8 ∂P.toMeasure) := by
    rw [integral_const_mul, integral_add (hi4.const_mul _) (hi8.const_mul _),
      integral_const_mul, integral_const_mul]
  -- the amplitude
  have hratio := principal_pow_ratio_le hnu hnu1 h400 hm hnum hn
  have hm0 : (0 : ℝ) < m := by
    have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hm']
  have hmu : 0 < ((m : ℝ) ^ 100)⁻¹ := by positivity
  have hnu99 : nu⁻¹ * (nu / m) ^ 100 ≤ ((m : ℝ) ^ 100)⁻¹ := by
    have : nu⁻¹ * (nu / m) ^ 100 = nu ^ 99 * ((m : ℝ) ^ 100)⁻¹ := by
      field_simp
    rw [this]
    calc nu ^ 99 * ((m : ℝ) ^ 100)⁻¹ ≤ 1 * ((m : ℝ) ^ 100)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hnu.le hnu1) hmu.le
      _ = _ := one_mul _
  have hγ0 : 0 < γ := Homogenization.IndependentSums.gammaTriangleConst_pos
  have hcc0 : 0 ≤ cc := by positivity
  have hampl : α * (γ * ((3 : ℝ) ^ (m - h))⁻¹) ≤ cc * γ * ((m : ℝ) ^ 100)⁻¹ := by
    have e1 : α * (γ * ((3 : ℝ) ^ (m - h))⁻¹) =
        (cc * γ) * (nu⁻¹ * ((3 : ℝ) ^ n * ((3 : ℝ) ^ (m - h))⁻¹)) := by
      rw [hα]; ring
    rw [e1]
    have : nu⁻¹ * ((3 : ℝ) ^ n * ((3 : ℝ) ^ (m - h))⁻¹) ≤ ((m : ℝ) ^ 100)⁻¹ :=
      le_trans (mul_le_mul_of_nonneg_left hratio (inv_pos.mpr hnu).le) hnu99
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hKp : ∀ p : ℕ, 1 ≤ p → p ≤ 8 → (p = 4 ∨ p = 8) →
      α * (gaugeMomentConst p * (γ * ((3 : ℝ) ^ (m - h))⁻¹)) ≤
        dzMomentConst d * ((m : ℝ) ^ 100)⁻¹ := by
    intro p hp _ hp48
    have hMp : 0 < gaugeMomentConst p := gaugeMomentConst_pos p hp
    have hle : gaugeMomentConst p ≤ gaugeMomentConst 4 + gaugeMomentConst 8 := by
      have h4 := gaugeMomentConst_pos 4 (by norm_num)
      have h8 := gaugeMomentConst_pos 8 (by norm_num)
      rcases hp48 with rfl | rfl <;> linarith only [h4, h8]
    calc α * (gaugeMomentConst p * (γ * ((3 : ℝ) ^ (m - h))⁻¹))
        = gaugeMomentConst p * (α * (γ * ((3 : ℝ) ^ (m - h))⁻¹)) := by ring
      _ ≤ gaugeMomentConst p * (cc * γ * ((m : ℝ) ^ 100)⁻¹) :=
          mul_le_mul_of_nonneg_left hampl hMp.le
      _ ≤ (gaugeMomentConst 4 + gaugeMomentConst 8) * (cc * γ * ((m : ℝ) ^ 100)⁻¹) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = dzMomentConst d * ((m : ℝ) ^ 100)⁻¹ := by
          unfold dzMomentConst; rw [hcc, hγ]; ring
  have hA0 : 0 ≤ ((m : ℝ) ^ 100)⁻¹ := hmu.le
  have hb4 : α ^ 4 * ∫ ω, g ω ^ 4 ∂P.toMeasure ≤ (dzMomentConst d * ((m : ℝ) ^ 100)⁻¹) ^ 4 := by
    calc α ^ 4 * ∫ ω, g ω ^ 4 ∂P.toMeasure
        ≤ α ^ 4 * (gaugeMomentConst 4 * (γ * ((3 : ℝ) ^ (m - h))⁻¹)) ^ 4 :=
          mul_le_mul_of_nonneg_left hm4 (by positivity)
      _ = (α * (gaugeMomentConst 4 * (γ * ((3 : ℝ) ^ (m - h))⁻¹))) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by
            have := gaugeMomentConst_pos 4 (by norm_num)
            positivity) (hKp 4 (by norm_num) (by norm_num) (Or.inl rfl)) 4
  have hb8 : α ^ 8 * ∫ ω, g ω ^ 8 ∂P.toMeasure ≤ (dzMomentConst d * ((m : ℝ) ^ 100)⁻¹) ^ 8 := by
    calc α ^ 8 * ∫ ω, g ω ^ 8 ∂P.toMeasure
        ≤ α ^ 8 * (gaugeMomentConst 8 * (γ * ((3 : ℝ) ^ (m - h))⁻¹)) ^ 8 :=
          mul_le_mul_of_nonneg_left hm8 (by positivity)
      _ = (α * (gaugeMomentConst 8 * (γ * ((3 : ℝ) ^ (m - h))⁻¹))) ^ 8 := by ring
      _ ≤ _ := pow_le_pow_left₀ (by
            have := gaugeMomentConst_pos 8 (by norm_num)
            positivity) (hKp 8 (by norm_num) (by norm_num) (Or.inr rfl)) 8
  rw [h2] at h1
  linarith only [h1, hb4, hb8]

/-- **`e.principal.Dz.moment`**, the average over the subcubes
`z + cu_n`, `z ∈ 3^n ℤ^d ∩ cu_K`, of the fourth moment of `D_z`:
`(avsum_z E[D_z^4])^{1/4} ≤ C m^{-100}`. Only the shell prefix law and J3 are used; the stationarity
is that of the translated gauge. The scale hypotheses are the standing ones of `lem.principal.term`:
`1 ≤ h`, `400 h ≤ m`, `ν ≤ 1`, `ν⁻¹ ≤ m` and `m ≥ 10^6` (consequences of `m ≥ 2 L₀`), and `n` is
`e.n.def.recurrence`. -/
theorem principal_Dz_moment (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ3 d P →
      ∀ m h n Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 1000000 ≤ m → nu⁻¹ ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ → n ≤ Kc →
        (((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
            ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
              ∫ ω, principalDz nu m h Q ω ^ 4 ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
          C * (m : ℝ) ^ (-(100 : ℝ)) := by
  set K := dzMomentConst d with hK
  have hK0 : 0 ≤ K := dzMomentConst_nonneg d
  have hX : 0 ≤ 8 * (1 + K ^ 4) * K ^ 4 := by positivity
  refine ⟨1 + 8 * (1 + K ^ 4) * K ^ 4, by linarith only [hX], ?_⟩
  intro nu hnu hnu1 P hPrefix hJ3 m h n Kc hh h400 hm hnum hn hnK
  set C : ℝ := 1 + 8 * (1 + K ^ 4) * K ^ 4 with hC
  have hC1 : 1 ≤ C := by rw [hC]; linarith only [hX]
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith only [hm']
  have hmu : 0 < ((m : ℝ) ^ 100)⁻¹ := by positivity
  have hmu1 : ((m : ℝ) ^ 100)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by linarith only [hm'])
  have hpow : (m : ℝ) ^ (-(100 : ℝ)) = ((m : ℝ) ^ 100)⁻¹ := by
    rw [Real.rpow_neg hm0.le, show (100 : ℝ) = ((100 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  set μ : ℝ := ((m : ℝ) ^ 100)⁻¹ with hμ
  -- per-cube
  have hcube : ∀ R ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ∫ ω, principalDz nu m h R ω ^ 4 ∂P.toMeasure ≤ (C * μ) ^ 4 := by
    intro R hR
    have hRs : R.scale = (n : ℤ) :=
      Homogenization.Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube
        (by exact_mod_cast hnK) hR
    have h1 := principal_Dz_pow4_integral_le hnu hnu1 hPrefix hJ3 hh h400 hm hnum hn R hRs
    refine le_trans h1 ?_
    have hT : K * μ ≤ K := by
      calc K * μ ≤ K * 1 := mul_le_mul_of_nonneg_left hmu1 hK0
        _ = K := mul_one K
    have hT0 : 0 ≤ K * μ := by positivity
    have e8 : (K * μ) ^ 8 = (K * μ) ^ 4 * (K * μ) ^ 4 := by ring
    have h8 : (K * μ) ^ 8 ≤ (K * μ) ^ 4 * K ^ 4 := by
      rw [e8]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hT 4) (by positivity)
    have h4 : 8 * ((K * μ) ^ 4 + (K * μ) ^ 8) ≤ 8 * (1 + K ^ 4) * K ^ 4 * μ ^ 4 := by
      have : (K * μ) ^ 4 = K ^ 4 * μ ^ 4 := by ring
      rw [this] at h8 ⊢
      nlinarith only [h8]
    have hC4 : C ≤ C ^ 4 := by
      calc C = C ^ 1 := (pow_one C).symm
        _ ≤ C ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
    calc 8 * ((K * μ) ^ 4 + (K * μ) ^ 8) ≤ 8 * (1 + K ^ 4) * K ^ 4 * μ ^ 4 := h4
      _ ≤ C * μ ^ 4 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hC]; linarith only []
      _ ≤ C ^ 4 * μ ^ 4 := mul_le_mul_of_nonneg_right hC4 (by positivity)
      _ = (C * μ) ^ 4 := by ring
  -- average
  have hnn : 0 ≤ (((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
      ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        ∫ ω, principalDz nu m h Q ω ^ 4 ∂P.toMeasure) :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun Q _ => integral_nonneg fun ω =>
        pow_nonneg (principalDz_nonneg hnu m h Q ω) 4)
  have havg : (((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
      ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        ∫ ω, principalDz nu m h Q ω ^ 4 ∂P.toMeasure) ≤ (C * μ) ^ 4 := by
    set D := descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)
    by_cases hD : D.card = 0
    · rw [hD]; simp only [Nat.cast_zero, inv_zero, zero_mul]; positivity
    · have hDpos : (0 : ℝ) < D.card := by exact_mod_cast Nat.pos_of_ne_zero hD
      have hs : ∑ Q ∈ D, ∫ ω, principalDz nu m h Q ω ^ 4 ∂P.toMeasure ≤ D.card * (C * μ) ^ 4 := by
        have := Finset.sum_le_card_nsmul D _ _ hcube
        simpa only [nsmul_eq_mul] using this
      rw [inv_mul_le_iff₀ hDpos]
      exact hs
  calc _ ≤ ((C * μ) ^ 4) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hnn havg (by norm_num)
    _ = C * μ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-! ## Satisfiability -/

/-- The hypotheses of `principal_Dz_moment` are met: `d = 2`, the Dirac law at the zero shell
sequence (prefix and J3), `ν = 1`, `m = 10^6`, `h = 1`, `n` the printed scale, `K = n`. -/
example : ∃ C : ℝ, 1 ≤ C ∧
    (((descendantsAtScale (originCube 2
          ((⌊((1000000 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) -
            100 * Real.logb 3 ((1 : ℝ)⁻¹ * ((1000000 : ℕ) : ℝ))⌋₊ : ℕ) : ℤ))
        ((⌊((1000000 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) -
            100 * Real.logb 3 ((1 : ℝ)⁻¹ * ((1000000 : ℕ) : ℝ))⌋₊ : ℕ) : ℤ)).card : ℝ)⁻¹ *
        ∑ Q ∈ descendantsAtScale (originCube 2
          ((⌊((1000000 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) -
            100 * Real.logb 3 ((1 : ℝ)⁻¹ * ((1000000 : ℕ) : ℝ))⌋₊ : ℕ) : ℤ))
        ((⌊((1000000 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) -
            100 * Real.logb 3 ((1 : ℝ)⁻¹ * ((1000000 : ℕ) : ℝ))⌋₊ : ℕ) : ℤ),
          ∫ ω, principalDz (1 : ℝ) 1000000 1 Q ω ^ 4
            ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2).toMeasure) ^
        ((1 : ℝ) / 4) ≤ C * ((1000000 : ℕ) : ℝ) ^ (-(100 : ℝ)) := by
  obtain ⟨C, hC, H⟩ := principal_Dz_moment 2
  refine ⟨C, hC, ?_⟩
  exact H 1 one_pos le_rfl _
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw le_rfl)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    1000000 1 _ _ le_rfl (by norm_num) le_rfl (by norm_num) rfl le_rfl

end SuperdiffusionCLT.Section5
