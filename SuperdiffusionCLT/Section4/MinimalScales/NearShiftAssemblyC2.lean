/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyC
public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePolyB

/-!
# Near-scale assembly, probabilistic part (II): the cap

`srootNS_cap_final`: the numerical side of the capped product. For `U = O_{Γ₁}(A)`,
`V = O_{Γ_{1/3}}(Bv)` and the crude bound `G = O_{Γ_{1/2}}(D₀ (1+m)^{10})`, the condition
`A · Bv ≤ m^{-4900}` gives `min (U V) G = O_{Γ_{1/3}}(κ m^{-2000})` as soon as `16384 D₀ ≤ κ²`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Homogenization.IndependentSums

noncomputable section

/-- The cap condition `16 A Bv D ≤ δ²` with `D = D₀ (1+m)^10`, `δ = κ m^{-2000}`. -/
theorem srootNS_cap_condition {A Bv D0 κ m : ℝ} (hm : 1 ≤ m)
    (hD0 : 0 < D0) (hAB : A * Bv ≤ m ^ (-(4900 : ℝ))) (hκ : 16384 * D0 ≤ κ ^ 2) :
    16 * (A * Bv) * (D0 * (1 + m) ^ (10 : ℝ)) ≤ (κ * m ^ (-(2000 : ℝ))) ^ 2 := by
  have hm0 : 0 < m := by linarith only [hm]
  have h1 : (1 + m) ^ (10 : ℝ) ≤ 1024 * m ^ (10 : ℝ) := by
    have h2 : (1 + m) ^ (10 : ℝ) ≤ (2 * m) ^ (10 : ℝ) :=
      Real.rpow_le_rpow (by linarith only [hm0]) (by linarith only [hm]) (by norm_num)
    rw [Real.mul_rpow (by norm_num) hm0.le] at h2
    have h3 : (2 : ℝ) ^ (10 : ℝ) = 1024 := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rwa [h3] at h2
  have h4 : m ^ (-(4900 : ℝ)) * m ^ (10 : ℝ) ≤ m ^ (-(4000 : ℝ)) := by
    rw [← Real.rpow_add hm0]
    exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have h5 : (κ * m ^ (-(2000 : ℝ))) ^ 2 = κ ^ 2 * m ^ (-(4000 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (m ^ (-(2000 : ℝ))) 2, ← Real.rpow_mul hm0.le]
    norm_num
  rw [h5]
  have hmp : 0 < m ^ (10 : ℝ) := Real.rpow_pos_of_pos hm0 _
  have hmq : 0 < m ^ (-(4000 : ℝ)) := Real.rpow_pos_of_pos hm0 _
  have h6 : 16 * (A * Bv) * (D0 * (1 + m) ^ (10 : ℝ)) ≤
      16 * m ^ (-(4900 : ℝ)) * (D0 * (1024 * m ^ (10 : ℝ))) := by
    have hD : D0 * (1 + m) ^ (10 : ℝ) ≤ D0 * (1024 * m ^ (10 : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 hD0.le
    have hD' : 0 ≤ D0 * (1 + m) ^ (10 : ℝ) := by positivity
    have := mul_le_mul (mul_le_mul_of_nonneg_left hAB (by norm_num : (0 : ℝ) ≤ 16)) hD hD'
      (by positivity)
    exact this
  have h7 : 16 * m ^ (-(4900 : ℝ)) * (D0 * (1024 * m ^ (10 : ℝ))) =
      16384 * D0 * (m ^ (-(4900 : ℝ)) * m ^ (10 : ℝ)) := by ring
  have h8 : 16384 * D0 * (m ^ (-(4900 : ℝ)) * m ^ (10 : ℝ)) ≤ 16384 * D0 * m ^ (-(4000 : ℝ)) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h9 : 16384 * D0 * m ^ (-(4000 : ℝ)) ≤ κ ^ 2 * m ^ (-(4000 : ℝ)) :=
    mul_le_mul_of_nonneg_right hκ hmq.le
  linarith only [h6, h7, h8, h9]

/-- From the threshold `lNaught C M (1/2) ≤ m`: `ν⁻¹ ≤ m` (and `ν⁻⁴ ≤ m`). -/
theorem srootNS_nuInv_le_of_lNaught {C M cStar nu K : ℝ} {m : ℝ} (hC : 1 ≤ C) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (hc : 0 < cStar) (hc2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hm : SuperdiffusionCLT.Frozen.Section4.lNaught C M (1 / 2) cStar nu K ≤ m) :
    nu⁻¹ ≤ m := by
  have h := srootD4_lNaught_ge_nu_inv hC hM hK hc hc2 hnu hnu1
  have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith only [this]
  have hp : (0.69 : ℝ) ^ 12 ≤ Real.log 2 ^ 12 := pow_le_pow_left₀ (by norm_num) hl2 12
  have hc0 : (1 : ℝ) ≤ (512 * Real.log 2 ^ 12) ^ 2 := by
    have : (1 : ℝ) ≤ 512 * Real.log 2 ^ 12 := by
      have h0 : (0.69 : ℝ) ^ 12 * 512 ≥ 1 := by norm_num
      nlinarith only [hp, h0]
    nlinarith only [this]
  have hi1 : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have h4 : nu⁻¹ ≤ (nu⁻¹) ^ 4 := by
    nlinarith only [hi1, pow_le_pow_right₀ hi1 (by norm_num : 1 ≤ 4)]
  have h5 : (nu⁻¹) ^ 4 ≤ (512 * Real.log 2 ^ 12) ^ 2 * (nu⁻¹) ^ 4 := by
    nlinarith only [hc0, pow_nonneg (le_trans zero_le_one hi1) 4]
  linarith only [h, h4, h5, hm]

/-- **C3 (final cap).** -/
theorem srootNS_cap_final {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {U V G : Ω → ℝ} {A Bv D0 κ m : ℝ} (hm : 1 ≤ m) (hA : 0 < A) (hBv : 0 < Bv) (hD0 : 0 < D0)
    (hκ0 : 0 < κ) (hU0 : ∀ ω, 0 ≤ U ω) (hV0 : ∀ ω, 0 ≤ V ω) (hG0 : ∀ ω, 0 ≤ G ω)
    (hU : IsBigO μ (gammaSigma 1) U A) (hV : IsBigO μ (gammaSigma (1 / 3)) V Bv)
    (hG : IsBigO μ (gammaSigma (1 / 2)) G (D0 * (1 + m) ^ (10 : ℝ)))
    (hAB : A * Bv ≤ m ^ (-(4900 : ℝ))) (hκ : 16384 * D0 ≤ κ ^ 2) :
    IsBigO μ (gammaSigma (1 / 3)) (fun ω => min (U ω * V ω) (G ω)) (κ * m ^ (-(2000 : ℝ))) := by
  have hm0 : 0 < m := by linarith only [hm]
  exact srootNS_isBigO_min_mul_cap hA hBv (by positivity)
    (mul_pos hκ0 (Real.rpow_pos_of_pos hm0 _)) hU0 hV0 hG0 hU hV hG
    (srootNS_cap_condition hm hD0 hAB hκ)

/-- Satisfiability: `U = V = G = 0` on `[0,1]`, all amplitudes `1`, `m = 1`, `κ = 128 `. -/
example : IsBigO (volume.restrict (Set.Icc (0 : ℝ) 1)) (gammaSigma (1 / 3))
    (fun ω => min ((fun _ : ℝ => (0 : ℝ)) ω * (fun _ : ℝ => (0 : ℝ)) ω) ((fun _ : ℝ => (0 : ℝ)) ω))
    (128 * (1 : ℝ) ^ (-(2000 : ℝ))) := by
  have h0 : ∀ σ : ℝ, 0 < σ → ∀ A : ℝ, 0 ≤ A →
      IsBigO (volume.restrict (Set.Icc (0 : ℝ) 1)) (gammaSigma σ) (fun _ : ℝ => (0 : ℝ)) A := by
    intro σ hσ A hA t ht
    have h : upperTailEvent (fun ω : ℝ => |(fun _ : ℝ => (0 : ℝ)) ω|) (A * t) = ∅ := by
      ext ω; simp [upperTailEvent]; nlinarith only [ht, hA]
    rw [h]; simp; positivity
  exact srootNS_cap_final (U := fun _ : ℝ => 0) (V := fun _ : ℝ => 0) (G := fun _ : ℝ => 0)
    (A := 1) (Bv := 1) (D0 := 1) (κ := 128) (m := 1) le_rfl one_pos one_pos one_pos (by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (h0 1 one_pos 1 zero_le_one)
    (h0 _ (by norm_num) 1 zero_le_one) (h0 _ (by norm_num) _ (by positivity)) (by norm_num)
    (by norm_num)

end

end SuperdiffusionCLT.Section4.MinimalScales
