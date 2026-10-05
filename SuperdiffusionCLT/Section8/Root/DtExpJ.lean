/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpI

/-!
# The fourth moment of the process on the good event

The fourth moment bound for times at least one, on the event that the growth scale is at most
`√t`, with the constant polynomial in the gradient constant of the process input.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Filter Topology
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open scoped Matrix.Norms.Elementwise ENNReal NNReal

variable {d : ℕ} [NeZero d] {nu : ℝ}

/-- **The fourth moment of the process, for `K ≤ √t`.** -/
theorem dtExp_fourth_bound {omega : ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega)) {C K : ℝ} (hK : 27 ≤ K)
    (hg : ∀ x : Vec d, matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
      C * Real.log (K ^ 2 + vecNormSq x) ^ ((2 : ℝ) * (1 + 1)))
    {t : ℝ} (ht : 10 ≤ t) (hKt : K ≤ Real.sqrt t) :
    ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0) ≤
      ENNReal.ofReal (crudeMomL_const d nu (Real.sqrt (max C 0))
        (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) 2 *
        (2 * Real.log t) ^ 16 * t ^ 2) := by
  have hK2 : (2 : ℝ) ≤ K := by linarith only [hK]
  have hk := crudeMomL_opNorm_le (σ := 1) hK2 hg
  have hceil : ⌈(1 : ℝ) + 1⌉₊ = 2 := by norm_num
  rw [hceil] at hk
  have h1 : (1 : ℝ≥0) ≤ t.toNNReal := by
    rw [show (1 : ℝ≥0) = Real.toNNReal 1 by simp]
    exact Real.toNNReal_le_toNNReal (by linarith only [ht])
  have h := fieldMoment_fourth_large D (Real.sqrt_nonneg _) hK2 (le_refl 2) hk h1
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have ht0 : 0 < t := by linarith only [ht]
  have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht0.le
  rw [hcoe]
  have hL : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le ht0]
    have := Real.exp_one_lt_d9
    linarith only [this, ht]
  have hlog : Real.log (K ^ 2 + t) ≤ 2 * Real.log t := by
    have h2 : K ^ 2 ≤ t := by
      calc K ^ 2 ≤ (Real.sqrt t) ^ 2 := pow_le_pow_left₀ (by linarith only [hK]) hKt 2
        _ = t := Real.sq_sqrt ht0.le
    have h3 : Real.log (K ^ 2 + t) ≤ Real.log (2 * t) :=
      Real.log_le_log (by positivity) (by linarith only [h2])
    rw [Real.log_mul (by norm_num) ht0.ne'] at h3
    have : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith only [this]
    linarith only [h3, this, hL]
  have hpos : 0 ≤ Real.log (K ^ 2 + t) :=
    Real.log_nonneg (by nlinarith only [hK, sq_nonneg t, ht])
  have hM := crudeMomL_const_nonneg (d := d) nu (Real.sqrt (max C 0))
    (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) 2
  have : Real.log (K ^ 2 + t) ^ (8 * 2) ≤ (2 * Real.log t) ^ 16 := by
    calc Real.log (K ^ 2 + t) ^ (8 * 2) ≤ (2 * Real.log t) ^ (8 * 2) :=
          pow_le_pow_left₀ hpos hlog _
      _ = _ := by norm_num
  gcongr

/-- **The fourth moment constant is polynomial in the inverse freezing amplitude.** -/
theorem dtExp_const_poly (hnu : 0 < nu) {c0 : ℝ} (hc0 : 0 ≤ c0) (n : ℕ) :
    ∃ K0 : ℝ, 1 ≤ K0 ∧ ∀ amp : ℝ, 0 < amp → amp ≤ 1 →
      crudeMomL_const d nu c0 amp n ≤ K0 * (amp⁻¹) ^ (8 * n * d) := by
  set Cc := crudeMomL_Cc d nu with hCc
  set Lam := crudeMomL_Lam1 nu c0 n with hLam
  set r1 := crudeMomL_r1 d nu with hr1
  set kap := crudeMomL_kap d nu c0 n with hkap
  have hCc0 : 0 ≤ Cc := crudeMomL_Cc_nonneg hnu
  have hLam0 := crudeMomL_Lam1_pos hnu hc0 n
  have hkap0 := crudeMomL_kap_pos (d := d) hnu hc0 n
  set G : ℝ := Lam * (1 + 4 * (n : ℝ)) ^ n + 4 with hG
  have hG0 : 0 ≤ G := by positivity
  set Y : ℝ := ((4 * n + 4 * n * d : ℕ) : ℝ) + d with hY
  have hY0 : 0 ≤ Y := by positivity
  set Kc : ℝ := max 1 ((Cc * G * (4 * (1 + 2 * (d : ℝ))) ^ d + Y) / kap) with hKc
  set Q : ℝ := 1 + 2 * Real.log (1 + 2 * (d : ℝ)) with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ Real.log (1 + 2 * (d : ℝ)) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith only [this])
    linarith only [this]
  have hB0 := crudeMomL_budget_nonneg kap
  refine ⟨14641 * ((Kc * Q) ^ (8 * n) + 8 * Real.exp 1 * crudeMomL_budget kap), ?_, ?_⟩
  · have h1 : 1 ≤ Kc := le_max_left _ _
    have h2 : 1 ≤ (Kc * Q) ^ (8 * n) := one_le_pow₀ (by nlinarith only [h1, hQ1])
    have h3 : 0 ≤ 8 * Real.exp 1 * crudeMomL_budget kap := by positivity
    nlinarith only [h2, h3]
  · intro amp hamp hamp1
    set u : ℝ := amp⁻¹ with hu
    have hu1 : 1 ≤ u := one_le_inv_iff₀.2 ⟨hamp, hamp1⟩
    have hud : 1 ≤ u ^ d := one_le_pow₀ hu1
    have hcut : crudeMomL_cut d nu c0 amp n ≤ Kc * u ^ d := by
      unfold crudeMomL_cut crudeMomL_W0
      rw [← hCc, ← hLam, ← hr1]
      have e1 : (4 * ((1 + 2 * (d : ℝ)) / amp)) ^ d = (4 * (1 + 2 * (d : ℝ))) ^ d * u ^ d := by
        rw [← mul_pow, hu]; congr 1; ring
      have hk' : crudeMomL_kappa n Lam r1 = kap := rfl
      rw [hk', e1, ← hG, add_assoc, ← hY]
      refine max_le ?_ ?_
      · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) hud
      · have h1 : Cc * G * ((4 * (1 + 2 * (d : ℝ))) ^ d * u ^ d) + Y ≤
            (Cc * G * (4 * (1 + 2 * (d : ℝ))) ^ d + Y) * u ^ d := by
          have : Y ≤ Y * u ^ d := le_mul_of_one_le_right hY0 hud
          nlinarith only [this]
        calc (Cc * G * ((4 * (1 + 2 * (d : ℝ))) ^ d * u ^ d) + Y) / kap
            ≤ ((Cc * G * (4 * (1 + 2 * (d : ℝ))) ^ d + Y) * u ^ d) / kap :=
              div_le_div_of_nonneg_right h1 hkap0.le
          _ = ((Cc * G * (4 * (1 + 2 * (d : ℝ))) ^ d + Y) / kap) * u ^ d := by ring
          _ ≤ Kc * u ^ d := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hcut0 : 0 ≤ crudeMomL_cut d nu c0 amp n := (one_le_crudeMomL_cut nu c0 amp n).trans' zero_le_one
    unfold crudeMomL_const
    rw [← hkap]
    have h1 : (crudeMomL_cut d nu c0 amp n * (1 + 2 * Real.log (1 + 2 * (d : ℝ)))) ^ (8 * n) ≤
        (Kc * Q) ^ (8 * n) * u ^ (8 * n * d) := by
      have : crudeMomL_cut d nu c0 amp n * Q ≤ (Kc * Q) * u ^ d := by nlinarith only [hcut, hQ1]
      calc (crudeMomL_cut d nu c0 amp n * Q) ^ (8 * n) ≤ ((Kc * Q) * u ^ d) ^ (8 * n) :=
            pow_le_pow_left₀ (by positivity) this _
        _ = (Kc * Q) ^ (8 * n) * u ^ (8 * n * d) := by rw [mul_pow, ← pow_mul]; ring_nf
    have h2 : 8 * Real.exp 1 * crudeMomL_budget kap ≤
        8 * Real.exp 1 * crudeMomL_budget kap * u ^ (8 * n * d) :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hu1)
    nlinarith only [h1, h2]

omit [NeZero d] in
/-- The inverse of the freezing amplitude is at most linear in the gradient constant. -/
theorem dtExp_amp_inv {k : Vec d → Mat d} (D : FieldInputData d nu k) (δ : ℝ) (hδ : 0 < δ) :
    (D.freezingAmplitude δ)⁻¹ ≤ 1 + (1 + 3 * ((d : ℝ) * D.gradConst)) / (δ * nu) := by
  have hg := D.gradConst_nonneg
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hden : 0 < 1 + 3 * ((d : ℝ) * D.gradConst) := by positivity
  have hnu := D.nu_pos
  unfold FieldInputData.freezingAmplitude
  rcases min_choice 1 (δ * nu / (1 + 3 * ((d : ℝ) * D.gradConst))) with h | h
  · rw [h]; simp only [inv_one]
    have : 0 ≤ (1 + 3 * ((d : ℝ) * D.gradConst)) / (δ * nu) := by positivity
    linarith only [this]
  · rw [h, inv_div]
    linarith only [show (0 : ℝ) ≤ 1 by norm_num]

/-- **The fourth moment constant is polynomial in the gradient constant.** -/
theorem dtExp_const_grad (hnu : 0 < nu) {c0 : ℝ} (hc0 : 0 ≤ c0) :
    ∃ K3 : ℝ, 1 ≤ K3 ∧ ∀ {k : Vec d → Mat d} (D : FieldInputData d nu k) {s : ℝ}, 1 ≤ s →
      D.gradConst ≤ s →
      crudeMomL_const d nu c0 (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) 2 ≤
        K3 * s ^ (16 * d) := by
  obtain ⟨K0, hK0, hK⟩ := dtExp_const_poly (d := d) hnu hc0 2
  set δ0 := smallContrastThreshold d (1 / 2 : ℝ) with hδ0
  have hδ : 0 < δ0 := fieldInput_smallContrastThreshold_half_pos d
  set K2 : ℝ := 1 + (1 + 3 * (d : ℝ)) / (δ0 * nu) with hK2
  have hK21 : 1 ≤ K2 := by
    have : 0 ≤ (1 + 3 * (d : ℝ)) / (δ0 * nu) := by positivity
    linarith only [this]
  refine ⟨K0 * (2 * K2) ^ (8 * 2 * d), ?_, fun D s hs1 hs => ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hK0 (one_le_pow₀ (by linarith only [hK21]))
  · have hamp0 : 0 < D.freezingAmplitude δ0 := D.freezingAmplitude_pos hδ
    have hamp1 := D.freezingAmplitude_le_one δ0
    refine (hK _ hamp0 hamp1).trans ?_
    have hinv := dtExp_amp_inv D δ0 hδ
    have hu : (D.freezingAmplitude δ0)⁻¹ ≤ 2 * K2 * s := by
      refine hinv.trans ?_
      have hg := D.gradConst_nonneg
      have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have h1 : (1 + 3 * ((d : ℝ) * D.gradConst)) / (δ0 * nu) ≤ (1 + 3 * (d : ℝ)) / (δ0 * nu) * s := by
        rw [div_mul_eq_mul_div]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith only [hs, hs1, hd, hg, mul_nonneg hd hg]
      have h2 : 0 ≤ (1 + 3 * (d : ℝ)) / (δ0 * nu) := by positivity
      nlinarith only [h1, h2, hs1, hK21]
    have hpos : 0 ≤ (D.freezingAmplitude δ0)⁻¹ := inv_nonneg.2 hamp0.le
    calc K0 * ((D.freezingAmplitude δ0)⁻¹) ^ (8 * 2 * d) ≤ K0 * (2 * K2 * s) ^ (8 * 2 * d) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos hu _) (by linarith only [hK0])
      _ = K0 * (2 * K2) ^ (8 * 2 * d) * s ^ (16 * d) := by
          rw [mul_pow]; ring_nf

end SuperdiffusionCLT.Section8
