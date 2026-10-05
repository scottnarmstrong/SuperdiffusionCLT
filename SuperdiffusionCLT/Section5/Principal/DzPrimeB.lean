/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.DzPrime

/-!
# The fourth moment of `D'` (`e.principal.Dz.moment`)

The argument of `principal_Dz_moment` with the measurable bound `D' = αg + (αg)²` in place of `D_z`:
`(avsum_z E[D'^4])^{1/4} ≤ C m^{-100}`. No relation between the scale `n` and `m - h` beyond the
printed `n = ⌊m - h - 100 log_3(ν⁻¹ m)⌋` is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream

variable {d : ℕ}

/-- One cube: `E[D'^4] ≤ 8 (T^4 + T^8)` with `T = K m^{-100}`. -/
theorem dzp_pow4_integral_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {m h n : ℕ} (hh : 1 ≤ h)
    (h400 : 400 * h ≤ m) (hm : 1000000 ≤ m) (hnum : nu⁻¹ ≤ (m : ℝ))
    (hn : n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊)
    (R : TriadicCube d) :
    ∫ ω, dzPrime nu n m h R ω ^ 4 ∂P.toMeasure ≤
      8 * ((dzMomentConst d * ((m : ℝ) ^ 100)⁻¹) ^ 4 + (dzMomentConst d * ((m : ℝ) ^ 100)⁻¹) ^ 8) := by
  have hhm : h ≤ m := by omega
  set cc : ℝ := (d : ℝ) * Real.sqrt d with hcc
  set γ : ℝ := Homogenization.IndependentSums.gammaTriangleConst 2 with hγ
  set z : Vec d := cubeCenter R with hz
  set g : ShellSeq d → ℝ := fun ω =>
    finiteShellDerivGauge (m - h) m (ShellField.translateSequence z ω) with hg
  set α : ℝ := nu⁻¹ * cc * (3 : ℝ) ^ n with hα
  have hα0 : 0 ≤ α := by positivity
  have hpoint : ∀ ω, dzPrime nu n m h R ω ^ 4 ≤ 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) := by
    intro ω
    have hg0 : 0 ≤ g ω := finiteShellDerivGauge_nonneg _ _ _
    have hx : 0 ≤ α * g ω := mul_nonneg hα0 hg0
    have hD' : dzPrime nu n m h R ω = α * g ω + (α * g ω) ^ 2 := rfl
    rw [hD']
    calc (α * g ω + (α * g ω) ^ 2) ^ 4 ≤ 8 * ((α * g ω) ^ 4 + (α * g ω) ^ 8) :=
          add_sq_pow_four_le
      _ = 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) := by ring
  obtain ⟨hi4, hm4⟩ := gauge_moment hPrefix hJ3 hh hhm z 4 (by norm_num)
  obtain ⟨hi8, hm8⟩ := gauge_moment hPrefix hJ3 hh hhm z 8 (by norm_num)
  have hint : Integrable (fun ω => 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8)) P.toMeasure :=
    ((hi4.const_mul (α ^ 4)).add (hi8.const_mul (α ^ 8))).const_mul 8
  have h1 : ∫ ω, dzPrime nu n m h R ω ^ 4 ∂P.toMeasure ≤
      ∫ ω, 8 * (α ^ 4 * g ω ^ 4 + α ^ 8 * g ω ^ 8) ∂P.toMeasure :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      pow_nonneg (dzPrime_nonneg hnu n m h R ω) 4) hint (Filter.Eventually.of_forall hpoint)
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

/-- **`e.principal.Dz.moment` for `D'`**, the average over the subcubes
`z + cu_n`, `z ∈ 3^n ℤ^d ∩ cu_K`, of the fourth moment of `D'`:
`(avsum_z E[D'^4])^{1/4} ≤ C m^{-100}`. Only the shell prefix law and J3 are used; the stationarity
is that of the translated gauge. The scale hypotheses are the standing ones of `lem.principal.term`:
`1 ≤ h`, `400 h ≤ m`, `ν ≤ 1`, `ν⁻¹ ≤ m` and `m ≥ 10^6` (consequences of `m ≥ 2 L₀`), and `n` is
`e.n.def.recurrence`; the relation `n ≤ K` is not needed. -/
theorem dzp_moment (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ3 d P →
      ∀ m h n Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 1000000 ≤ m → nu⁻¹ ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * Real.logb 3 (nu⁻¹ * m)⌋₊ →
        (((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
            ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
              ∫ ω, dzPrime nu n m h Q ω ^ 4 ∂P.toMeasure) ^ ((1 : ℝ) / 4) ≤
          C * (m : ℝ) ^ (-(100 : ℝ)) := by
  set K := dzMomentConst d with hK
  have hK0 : 0 ≤ K := dzMomentConst_nonneg d
  have hX : 0 ≤ 8 * (1 + K ^ 4) * K ^ 4 := by positivity
  refine ⟨1 + 8 * (1 + K ^ 4) * K ^ 4, by linarith only [hX], ?_⟩
  intro nu hnu hnu1 P hPrefix hJ3 m h n Kc hh h400 hm hnum hn
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
      ∫ ω, dzPrime nu n m h R ω ^ 4 ∂P.toMeasure ≤ (C * μ) ^ 4 := by
    intro R _
    have h1 := dzp_pow4_integral_le hnu hnu1 hPrefix hJ3 hh h400 hm hnum hn R
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
        ∫ ω, dzPrime nu n m h Q ω ^ 4 ∂P.toMeasure) :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun Q _ => integral_nonneg fun ω =>
        pow_nonneg (dzPrime_nonneg hnu n m h Q ω) 4)
  have havg : (((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
      ∑ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
        ∫ ω, dzPrime nu n m h Q ω ^ 4 ∂P.toMeasure) ≤ (C * μ) ^ 4 := by
    set D := descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)
    by_cases hD : D.card = 0
    · rw [hD]; simp only [Nat.cast_zero, inv_zero, zero_mul]; positivity
    · have hDpos : (0 : ℝ) < D.card := by exact_mod_cast Nat.pos_of_ne_zero hD
      have hs : ∑ Q ∈ D, ∫ ω, dzPrime nu n m h Q ω ^ 4 ∂P.toMeasure ≤ D.card * (C * μ) ^ 4 := by
        have := Finset.sum_le_card_nsmul D _ _ hcube
        simpa only [nsmul_eq_mul] using this
      rw [inv_mul_le_iff₀ hDpos]
      exact hs
  calc _ ≤ ((C * μ) ^ 4) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow hnn havg (by norm_num)
    _ = C * μ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-! ## Satisfiability -/

/-- The hypotheses of `dzp_moment` are met: `d = 2`, the Dirac law at the zero shell
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
          ∫ ω, dzPrime (1 : ℝ) ((⌊((1000000 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) -
            100 * Real.logb 3 ((1 : ℝ)⁻¹ * ((1000000 : ℕ) : ℝ))⌋₊ : ℕ)) 1000000 1 Q ω ^ 4
            ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw 2).toMeasure) ^
        ((1 : ℝ) / 4) ≤ C * ((1000000 : ℕ) : ℝ) ^ (-(100 : ℝ)) := by
  obtain ⟨C, hC, H⟩ := dzp_moment 2
  refine ⟨C, hC, ?_⟩
  exact H 1 one_pos le_rfl _
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw le_rfl)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw
    1000000 1 _ _ le_rfl (by norm_num) le_rfl (by norm_num) rfl

end SuperdiffusionCLT.Section5
