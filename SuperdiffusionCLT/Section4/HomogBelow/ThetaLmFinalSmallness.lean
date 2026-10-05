/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmM3Headroom
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmOmegaSeq
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmFinalInflateR
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmLNaughtGeLinear

/-!
**The smallness lemma** `ω_h² ≤ Υ₁⁻¹` in the proof of `p.homog.below`:
the `(a+b+c)² ≤ 3(a²+b²+c²)`
split of `ω_h = K₃·(T₁+T₂+T₃)`, each term's bound in terms of a free
inflation ratio `r` and the caller's own `Kappa3` (the `m₃`-headroom
constant), and the exact thresholds `r`, `Lthresh` making each squared term
`≤ Υ₁⁻¹/3`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

/-- `x^{1/2}·x^{1/2} = x` for `x ≥ 0` (the `A`-side rpow identity `T₁²`
needs). -/
private theorem homogBelow_rpow_half_sq {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) = x := by
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)]
    ring
  · rw [← Real.rpow_add hpos]
    norm_num

/-- `x^{-1}·x^{-1} = x^{-2}` for `x > 0` (the `S`-side rpow identity `T₁²`
needs). -/
private theorem homogBelow_rpow_neg_one_sq {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 : ℝ)) * x ^ (-(1 : ℝ)) = x ^ (-(2 : ℝ)) := by
  rw [← Real.rpow_add hx]
  norm_num

/-- **`T₁² ≤ Cmix·Kappa3/r`** (the `T1²` bound). `A`
stands for `(L-h)`, `Lr` for `L^α·log³L`, `S` for `shom_{L,*}(cu_h)`. -/
private theorem homogBelow_T1_sq_le
    {Cmix r M Lr Kappa3 A S : ℝ}
    (hCmix1 : 1 ≤ Cmix) (hr : 0 < r) (hM1 : 1 ≤ M) (hLrpos : 0 < Lr)
    (_hKappa3 : 0 ≤ Kappa3) (hA0 : 0 ≤ A) (hSpos : 0 < S)
    (hAbound : A ≤ Kappa3 * M * Lr)
    (hSsq : r * Cmix * M * Lr ≤ S ^ (2 : ℝ)) :
    (Cmix * A ^ ((1 : ℝ) / 2) * S ^ (-(1 : ℝ))) ^ 2 ≤ Cmix * Kappa3 / r := by
  have hCmixpos : 0 < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hXpos : 0 < r * Cmix * M * Lr := by positivity
  have hSsqpos : 0 < S ^ (2 : ℝ) := Real.rpow_pos_of_pos hSpos _
  have hinv : (S ^ (2 : ℝ))⁻¹ ≤ (r * Cmix * M * Lr)⁻¹ := (inv_le_inv₀ hSsqpos hXpos).2 hSsq
  have hSneg2 : S ^ (-(2 : ℝ)) = (S ^ (2 : ℝ))⁻¹ := Real.rpow_neg hSpos.le 2
  have hexpand : (Cmix * A ^ ((1 : ℝ) / 2) * S ^ (-(1 : ℝ))) ^ 2 =
      Cmix ^ 2 * (A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 2)) * (S ^ (-(1 : ℝ)) * S ^ (-(1 : ℝ))) := by
    ring
  rw [hexpand, homogBelow_rpow_half_sq hA0, homogBelow_rpow_neg_one_sq hSpos, hSneg2]
  have hr' : r ≠ 0 := hr.ne'
  have hCmix' : Cmix ≠ 0 := hCmixpos.ne'
  have hM' : M ≠ 0 := hMpos.ne'
  have hLr' : Lr ≠ 0 := hLrpos.ne'
  have heq : Cmix ^ 2 * (Kappa3 * M * Lr) * (r * Cmix * M * Lr)⁻¹ = Cmix * Kappa3 / r := by
    field_simp
  have hstep1 : Cmix ^ 2 * A * (S ^ (2 : ℝ))⁻¹ ≤ Cmix ^ 2 * A * (r * Cmix * M * Lr)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have hstep2 : Cmix ^ 2 * A * (r * Cmix * M * Lr)⁻¹ ≤
      Cmix ^ 2 * (Kappa3 * M * Lr) * (r * Cmix * M * Lr)⁻¹ :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAbound (by positivity)) (by positivity)
  rw [← heq]
  linarith only [hstep1, hstep2]

/-- **`T₂ ≤ Kappa3/r`** (the `T2` bound; no `rpow` split
is needed, unlike `T1`). -/
private theorem homogBelow_T2_le
    {Cmix r M Lr Kappa3 A S : ℝ}
    (hCmix1 : 1 ≤ Cmix) (hr : 0 < r) (hM1 : 1 ≤ M) (hLrpos : 0 < Lr)
    (hA0 : 0 ≤ A) (hSpos : 0 < S)
    (hAbound : A ≤ Kappa3 * M * Lr)
    (hSsq : r * Cmix * M * Lr ≤ S ^ (2 : ℝ)) :
    Cmix * A * S ^ (-(2 : ℝ)) ≤ Kappa3 / r := by
  have hCmixpos : 0 < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hXpos : 0 < r * Cmix * M * Lr := by positivity
  have hSsqpos : 0 < S ^ (2 : ℝ) := Real.rpow_pos_of_pos hSpos _
  have hinv : (S ^ (2 : ℝ))⁻¹ ≤ (r * Cmix * M * Lr)⁻¹ := (inv_le_inv₀ hSsqpos hXpos).2 hSsq
  have hSneg2 : S ^ (-(2 : ℝ)) = (S ^ (2 : ℝ))⁻¹ := Real.rpow_neg hSpos.le 2
  rw [hSneg2]
  have hr' : r ≠ 0 := hr.ne'
  have hCmix' : Cmix ≠ 0 := hCmixpos.ne'
  have hM' : M ≠ 0 := hMpos.ne'
  have hLr' : Lr ≠ 0 := hLrpos.ne'
  have heq : Cmix * (Kappa3 * M * Lr) * (r * Cmix * M * Lr)⁻¹ = Kappa3 / r := by
    field_simp
  have hstep1 : Cmix * A * (S ^ (2 : ℝ))⁻¹ ≤ Cmix * A * (r * Cmix * M * Lr)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have hstep2 : Cmix * A * (r * Cmix * M * Lr)⁻¹ ≤
      Cmix * (Kappa3 * M * Lr) * (r * Cmix * M * Lr)⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAbound hCmixpos.le) (by positivity)
  rw [← heq]
  linarith only [hstep1, hstep2]

/-- **`T₃ ≤ 1/(3·K3·Ups1)`** (the `T3` bound), once
`max 1 h` clears a threshold `Lthresh` with `9·Cmix·K3·Ups1 ≤ Lthresh`. -/
private theorem homogBelow_T3_le
    {Cmix K3 Ups1 Lthresh : ℝ} (hCmix1 : 1 ≤ Cmix) (hK3 : 0 < K3) (hUps1 : 1 ≤ Ups1)
    (hLthresh_ge : 9 * Cmix * K3 * Ups1 ≤ Lthresh) (h : ℕ)
    (hbase : Lthresh ≤ max 1 (h : ℝ)) :
    3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ)) ≤ 1 / (3 * K3 * Ups1) := by
  have hCmixpos : 0 < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have hmax1h1 : (1 : ℝ) ≤ max 1 (h : ℝ) := le_max_left _ _
  have hmax1hpos : (0 : ℝ) < max 1 (h : ℝ) := lt_of_lt_of_le zero_lt_one hmax1h1
  have hXpos9 : (0 : ℝ) < 9 * Cmix * K3 * Ups1 := by positivity
  have hLthreshpos : 0 < Lthresh := lt_of_lt_of_le hXpos9 hLthresh_ge
  have hcrude : (max 1 (h : ℝ)) ^ (-(3000 : ℝ)) ≤ (max 1 (h : ℝ)) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hmax1h1 (by norm_num)
  have hrpowneg1 : (max 1 (h : ℝ)) ^ (-(1 : ℝ)) = (max 1 (h : ℝ))⁻¹ := by
    rw [Real.rpow_neg hmax1hpos.le, Real.rpow_one]
  have hinv : (max 1 (h : ℝ))⁻¹ ≤ Lthresh⁻¹ := (inv_le_inv₀ hmax1hpos hLthreshpos).2 hbase
  have hstep : 3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ)) ≤ 3 * Cmix / Lthresh := by
    have h1 : 3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ)) ≤ 3 * Cmix * (max 1 (h : ℝ))⁻¹ := by
      rw [← hrpowneg1]
      exact mul_le_mul_of_nonneg_left hcrude (by positivity)
    have h2 : 3 * Cmix * (max 1 (h : ℝ))⁻¹ ≤ 3 * Cmix * Lthresh⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have h3 : 3 * Cmix * Lthresh⁻¹ = 3 * Cmix / Lthresh := (div_eq_mul_inv _ _).symm
    linarith only [h1, h2, h3.le, h3.ge]
  have hfinal : 3 * Cmix / Lthresh ≤ 1 / (3 * K3 * Ups1) := by
    rw [div_le_div_iff₀ hLthreshpos (by positivity)]
    nlinarith only [hLthresh_ge]
  linarith only [hstep, hfinal]

/-- **The "3 thirds" combination**: from `T1² ≤ a`,
`T2 ≤ b`, `T3 ≤ c` with `3·K3²·a ≤ Ups1⁻¹/3`, `3·K3²·b² ≤ Ups1⁻¹/3`,
`3·K3²·c² ≤ Ups1⁻¹/3`, conclude `(K3·(T1+T2+T3))² ≤ Ups1⁻¹`, via
`(T1+T2+T3)² ≤ 3(T1²+T2²+T3²)`. -/
private theorem homogBelow_omega_sq_le_of_three_bounds
    {K3 Ups1 T1 T2 T3 a b c : ℝ} (_hK3 : 0 < K3)
    (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3)
    (hT1sq : T1 ^ 2 ≤ a) (hT2le : T2 ≤ b) (hT3le : T3 ≤ c)
    (hB1 : 3 * K3 ^ 2 * a ≤ Ups1⁻¹ / 3)
    (hB2 : 3 * K3 ^ 2 * b ^ 2 ≤ Ups1⁻¹ / 3)
    (hB3 : 3 * K3 ^ 2 * c ^ 2 ≤ Ups1⁻¹ / 3) :
    (K3 * (T1 + T2 + T3)) ^ 2 ≤ Ups1⁻¹ := by
  have hT2sq : T2 ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hT2 hT2le 2
  have hT3sq : T3 ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hT3 hT3le 2
  have hB1' : 3 * K3 ^ 2 * T1 ^ 2 ≤ Ups1⁻¹ / 3 := by nlinarith only [hT1sq, hB1, sq_nonneg K3]
  have hB2' : 3 * K3 ^ 2 * T2 ^ 2 ≤ Ups1⁻¹ / 3 := by nlinarith only [hT2sq, hB2, sq_nonneg K3]
  have hB3' : 3 * K3 ^ 2 * T3 ^ 2 ≤ Ups1⁻¹ / 3 := by nlinarith only [hT3sq, hB3, sq_nonneg K3]
  nlinarith only [hB1', hB2', hB3', sq_nonneg (T1 - T2), sq_nonneg (T2 - T3), sq_nonneg (T1 - T3),
    sq_nonneg K3]

/-- The scaled `T1²`-bound clears the `/3` threshold once `r` is past
`9·K3²·Cmix·Kappa3·Ups1` (the first summand of the threshold on `r`). -/
private theorem homogBelow_B1_le
    {K3 Cmix Kappa3 Ups1 r : ℝ} (hUps1pos : 0 < Ups1) (hr : 0 < r)
    (hrge : 9 * K3 ^ 2 * Cmix * Kappa3 * Ups1 ≤ r) :
    3 * K3 ^ 2 * (Cmix * Kappa3 / r) ≤ Ups1⁻¹ / 3 := by
  have heq : 3 * K3 ^ 2 * (Cmix * Kappa3 / r) = (3 * K3 ^ 2 * Cmix * Kappa3) / r := by ring
  have hUps1eq : Ups1⁻¹ / 3 = 1 / (3 * Ups1) := by
    rw [inv_eq_one_div, div_div, mul_comm]
  rw [heq, hUps1eq, div_le_div_iff₀ hr (by positivity)]
  nlinarith only [hrge]

/-- The scaled `T2²`-bound clears the `/3` threshold once `r` is past
`3·K3·Kappa3·Ups1` (the second summand of the threshold on `r`; no square
root of `Ups1` is needed since `Ups1² ≥ Ups1`). -/
private theorem homogBelow_B2_le
    {K3 Kappa3 Ups1 r : ℝ} (hK3 : 0 < K3) (hKappa3 : 0 ≤ Kappa3) (hUps1 : 1 ≤ Ups1)
    (hr : 0 < r) (hrge : 3 * K3 * Kappa3 * Ups1 ≤ r) :
    3 * K3 ^ 2 * (Kappa3 / r) ^ 2 ≤ Ups1⁻¹ / 3 := by
  have hUps1pos : 0 < Ups1 := lt_of_lt_of_le zero_lt_one hUps1
  have hprodnonneg : 0 ≤ 3 * K3 * Kappa3 * Ups1 := by positivity
  have hrsq : (3 * K3 * Kappa3 * Ups1) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hprodnonneg hrge 2
  have hrsq' : 9 * K3 ^ 2 * Kappa3 ^ 2 * Ups1 ^ 2 ≤ r ^ 2 := by nlinarith only [hrsq]
  have hUps1sq : Ups1 ≤ Ups1 ^ 2 := by nlinarith only [hUps1]
  have hstep : 9 * K3 ^ 2 * Kappa3 ^ 2 * Ups1 ≤ 9 * K3 ^ 2 * Kappa3 ^ 2 * Ups1 ^ 2 :=
    mul_le_mul_of_nonneg_left hUps1sq (by positivity)
  have hfinal : 9 * K3 ^ 2 * Kappa3 ^ 2 * Ups1 ≤ r ^ 2 := le_trans hstep hrsq'
  have heq : 3 * K3 ^ 2 * (Kappa3 / r) ^ 2 = (3 * K3 ^ 2 * Kappa3 ^ 2) / r ^ 2 := by ring
  have hUps1eq : Ups1⁻¹ / 3 = 1 / (3 * Ups1) := by
    rw [inv_eq_one_div, div_div, mul_comm]
  rw [heq, hUps1eq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hfinal]

/-- The `T3²`-bound clears the `/3` threshold unconditionally:
`3·K3²·(1/(3·K3·Ups1))² = 1/(3·Ups1²) ≤ 1/(3·Ups1) = Ups1⁻¹/3`
since `Ups1² ≥ Ups1`. -/
private theorem homogBelow_B3_le
    {K3 Ups1 : ℝ} (hK3 : 0 < K3) (hUps1 : 1 ≤ Ups1) :
    3 * K3 ^ 2 * (1 / (3 * K3 * Ups1)) ^ 2 ≤ Ups1⁻¹ / 3 := by
  have hUps1pos : 0 < Ups1 := lt_of_lt_of_le zero_lt_one hUps1
  have hUps1sq : Ups1 ≤ Ups1 ^ 2 := by nlinarith only [hUps1]
  have heq : 3 * K3 ^ 2 * (1 / (3 * K3 * Ups1)) ^ 2 = 1 / (3 * Ups1 ^ 2) := by
    field_simp
  have hUps1eq : Ups1⁻¹ / 3 = 1 / (3 * Ups1) := by
    rw [inv_eq_one_div, div_div, mul_comm]
  rw [heq, hUps1eq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hUps1sq]

/-- `K3 := gammaTriangleConst(1/3) > 0` (mirrors `ThetaLmOmegaSeq.lean`'s
inline computation, exposed here as its own lemma for reuse). -/
private theorem homogBelow_K3_pos :
    0 < Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) := by
  have hgc2 : (2 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    Homogenization.IndependentSums.two_le_gammaGrowthConst _
  have hgcpos : 0 < Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    lt_of_lt_of_le (by norm_num) hgc2
  unfold Homogenization.IndependentSums.gammaTriangleConst
  have h12 := Real.rpow_pos_of_pos hgcpos (12 : ℝ)
  linarith only [h12]

variable {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu) (L : ℕ) (Cmix : ℝ)
  (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4 in
/-- **The smallness bound, `h ∈ [L/2, L]` case**: given
the `S(h)²` lower bound from [AK, Theorem 6.1] at inflation ratio `r`, the `m₃`-headroom
constant `Kappa3` bounding `(L-h)`, and the two threshold facts on `r` and
`Lthresh`, `ω_h² ≤ Ups1⁻¹`. -/
theorem homogBelow_smallness_core
    (hCmix1 : 1 ≤ Cmix)
    {K3 Ups1 Kappa3 r Lthresh M alpha : ℝ}
    (hUps1 : 1 ≤ Ups1) (hKappa3 : 0 ≤ Kappa3)
    (hr : 0 < r) (hM1 : 1 ≤ M)
    (hLrpos : 0 < (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))
    (hK3eq : K3 = Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3))
    (hrgeA : 9 * K3 ^ 2 * Cmix * Kappa3 * Ups1 ≤ r)
    (hrgeB : 3 * K3 * Kappa3 * Ups1 ≤ r)
    (hLthresh_ge : 9 * Cmix * K3 * Ups1 ≤ Lthresh)
    (h : ℕ) (hbaseL : Lthresh ≤ max 1 (h : ℝ))
    (hAbound : ((L - h : ℕ) : ℝ) ≤
      Kappa3 * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)))
    (hSsq : r * Cmix * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ)) :
    homogBelow_omegaSeq nu L Cmix P h ^ 2 ≤ Ups1⁻¹ := by
  have hCmixpos : 0 < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  have hK3pos : 0 < K3 := hK3eq ▸ homogBelow_K3_pos
  have hSpos := homogBelow_sigmaBarStarScalar_pos nu hnu L P hPrefix hJ2 hJ3 hJ4 h
  have hA0 : (0 : ℝ) ≤ ((L - h : ℕ) : ℝ) := by positivity
  have hT1sq := homogBelow_T1_sq_le (Cmix := Cmix) (r := r) (M := M)
    (Lr := (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) (Kappa3 := Kappa3)
    (A := ((L - h : ℕ) : ℝ))
    (S := SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
    hCmix1 hr hM1 hLrpos hKappa3 hA0 hSpos hAbound hSsq
  have hT2le := homogBelow_T2_le (Cmix := Cmix) (r := r) (M := M)
    (Lr := (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) (Kappa3 := Kappa3)
    (A := ((L - h : ℕ) : ℝ))
    (S := SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))))
    hCmix1 hr hM1 hLrpos hA0 hSpos hAbound hSsq
  have hT3le := homogBelow_T3_le hCmix1 hK3pos hUps1 hLthresh_ge h hbaseL
  have hB1 := homogBelow_B1_le (K3 := K3) (Cmix := Cmix) (Kappa3 := Kappa3) (Ups1 := Ups1)
    (r := r) (lt_of_lt_of_le zero_lt_one hUps1) hr hrgeA
  have hB2 := homogBelow_B2_le hK3pos hKappa3 hUps1 hr hrgeB
  have hB3 := homogBelow_B3_le hK3pos hUps1
  have hT2nonneg : (0 : ℝ) ≤ Cmix * ((L - h : ℕ) : ℝ) *
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(2 : ℝ)) := by
    have := (Real.rpow_pos_of_pos hSpos (-(2 : ℝ))).le
    positivity
  have hT3nonneg : (0 : ℝ) ≤
      3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ)) := by
    have hmax1hpos : (0 : ℝ) < max 1 (h : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have := (Real.rpow_pos_of_pos hmax1hpos (-(3000 : ℝ))).le
    positivity
  have hcomb := homogBelow_omega_sq_le_of_three_bounds hK3pos hT2nonneg hT3nonneg
    hT1sq hT2le hT3le hB1 hB2 hB3
  have hrw : homogBelow_omegaSeq nu L Cmix P h =
      K3 * (Cmix * ((L - h : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(1 : ℝ)) +
        Cmix * ((L - h : ℕ) : ℝ) *
            SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (-(2 : ℝ)) +
          3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ))) := by
    unfold homogBelow_omegaSeq
    rw [hK3eq]
    ring
  rw [hrw]
  linarith only [hcomb]

/-- **The smallness bound, `L ≤ h` case**: once
`h ≥ L`, the `ℕ`-truncated `(L-h)` collapses to `0`, so `ω_h = K3·T3` and the
same `T3`-bound alone (no `S(h)` positivity, no `r` needed) already gives
`ω_h² ≤ Ups1⁻¹`. -/
theorem homogBelow_smallness_far
    (hCmix1 : 1 ≤ Cmix)
    {K3 Ups1 Lthresh : ℝ} (hUps1 : 1 ≤ Ups1)
    (hK3eq : K3 = Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3))
    (hLthresh_ge : 9 * Cmix * K3 * Ups1 ≤ Lthresh)
    (h : ℕ) (hLh : L ≤ h) (hbaseL : Lthresh ≤ max 1 (h : ℝ)) :
    homogBelow_omegaSeq nu L Cmix P h ^ 2 ≤ Ups1⁻¹ := by
  have hK3pos : 0 < K3 := hK3eq ▸ homogBelow_K3_pos
  have hUps1pos : 0 < Ups1 := lt_of_lt_of_le zero_lt_one hUps1
  have hT3le := homogBelow_T3_le hCmix1 hK3pos hUps1 hLthresh_ge h hbaseL
  have hT3nonneg : (0 : ℝ) ≤ 3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ)) := by
    have hmax1hpos : (0 : ℝ) < max 1 (h : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have := (Real.rpow_pos_of_pos hmax1hpos (-(3000 : ℝ))).le
    positivity
  have hLhnat : (L - h : ℕ) = 0 := by omega
  have hrw : homogBelow_omegaSeq nu L Cmix P h =
      K3 * (3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ))) := by
    unfold homogBelow_omegaSeq
    rw [hK3eq, hLhnat]
    simp only [Nat.cast_zero]
    rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)]
    ring
  rw [hrw]
  have hT3sq : (3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ))) ^ 2 ≤ (1 / (3 * K3 * Ups1)) ^ 2 :=
    pow_le_pow_left₀ hT3nonneg hT3le 2
  have hstep1 : K3 ^ 2 * (3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ))) ^ 2 ≤
      K3 ^ 2 * (1 / (3 * K3 * Ups1)) ^ 2 :=
    mul_le_mul_of_nonneg_left hT3sq (by positivity)
  have heq1 : K3 ^ 2 * (1 / (3 * K3 * Ups1)) ^ 2 = 1 / (9 * Ups1 ^ 2) := by
    field_simp
    ring
  rw [heq1] at hstep1
  have hUps1sq : Ups1 ≤ Ups1 ^ 2 := by nlinarith only [hUps1]
  have hfinal : 1 / (9 * Ups1 ^ 2) ≤ Ups1⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hUps1pos]
    nlinarith only [hUps1sq]
  have heq2 : (K3 * (3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ)))) ^ 2 =
      K3 ^ 2 * (3 * Cmix * (max 1 (h : ℝ)) ^ (-(3000 : ℝ))) ^ 2 := by ring
  rw [heq2]
  linarith only [hstep1, hfinal]

/-- **The smallness lemma**: for
every `Ups1 ≥ 1` (`:= Υ₁`, the constant of [AK, Theorem 6.1]) and `Kappa3 ≥ 0` (the
`m₃`-headroom constant from `homogBelow_m3_headroom`'s `hm3ge`), a threshold
`C1` and inflation ratio `r` such that for every outer `C ≥ C1`, every valid
parameter tuple, every `L` clearing `lNaught`, and every `m3 h : ℕ` with
`L/2 ≤ m3` and `m3 + 1 ≤ h` (the real headroom on `m3`), `ω_h² ≤ Ups1⁻¹`. -/
theorem homogBelow_smallness
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cmix : ℝ) (hCmix1 : 1 ≤ Cmix) :
    ∀ Ups1 : ℝ, 1 ≤ Ups1 → ∀ Kappa3 : ℝ, 0 ≤ Kappa3 →
    ∃ C1 r : ℝ, 1 ≤ C1 ∧ 0 < r ∧ ∀ C : ℝ, C1 ≤ C →
      ∀ M alpha cStar nu K : ℝ, 1 ≤ M → 0 ≤ alpha → alpha < 1 →
        0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 → 0 ≤ K →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
      ∀ L : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
      ∀ m3 h : ℕ, L / 2 ≤ m3 → m3 + 1 ≤ h →
        (L : ℝ) - (m3 : ℝ) ≤ Kappa3 * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) →
        homogBelow_omegaSeq nu L Cmix P h ^ 2 ≤ Ups1⁻¹ := by
  intro Ups1 hUps1 Kappa3 hKappa3
  obtain ⟨c, C₀, hcpos, hC01, _hC0_Cmix, _hC0_c, hThreshBody⟩ :=
    homogBelow_thresholdHyps d hd Cmix hCmix1
  obtain ⟨Clin, _hClin1, hlin⟩ := homogBelow_lNaught_ge_linear
  have hK3pos : 0 < Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) :=
    homogBelow_K3_pos
  set K3 : ℝ := Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) with hK3def
  have hUps1pos : 0 < Ups1 := lt_of_lt_of_le zero_lt_one hUps1
  have hCmixpos : 0 < Cmix := lt_of_lt_of_le zero_lt_one hCmix1
  set r : ℝ := 9 * K3 ^ 2 * Cmix * Kappa3 * Ups1 + 3 * K3 * Kappa3 * Ups1 + 1 with hrdef
  have hAnonneg : 0 ≤ 9 * K3 ^ 2 * Cmix * Kappa3 * Ups1 := by positivity
  have hBnonneg : 0 ≤ 3 * K3 * Kappa3 * Ups1 := by positivity
  have hrpos : 0 < r := by rw [hrdef]; linarith only [hAnonneg, hBnonneg]
  have hrgeA : 9 * K3 ^ 2 * Cmix * Kappa3 * Ups1 ≤ r := by rw [hrdef]; linarith only [hBnonneg]
  have hrgeB : 3 * K3 * Kappa3 * Ups1 ≤ r := by rw [hrdef]; linarith only [hAnonneg]
  set Lthresh : ℝ := 9 * Cmix * K3 * Ups1 + 1 with hLthreshdef
  have hLthresh_ge : 9 * Cmix * K3 * Ups1 ≤ Lthresh := by rw [hLthreshdef]; linarith only []
  have hLthresh_ge1 : 1 ≤ Lthresh := by
    have h9 : (0 : ℝ) ≤ 9 * Cmix * K3 * Ups1 := by positivity
    rw [hLthreshdef]; linarith only [h9]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2pow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  set CLthresh : ℝ := 4 * (2 * Lthresh + 1) / (Real.log 2) ^ (12 : ℝ) with hCLthreshdef
  have hCLthreshnonneg : 0 ≤ CLthresh := by
    rw [hCLthreshdef]; positivity
  refine ⟨max 1 (max (C₀ / min (1 : ℝ) (c / r)) (max Clin CLthresh)), r, le_max_left _ _,
    hrpos, ?_⟩
  intro C hC M alpha cStar nu K hM1 halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK
    P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hL m3 h hm3half hm3lth hm3ge
  have hC1' : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) hC
  have hCrest := le_trans (le_max_right (1 : ℝ) _) hC
  have hminpos : (0 : ℝ) < min (1 : ℝ) (c / r) := lt_min (by norm_num) (div_pos hcpos hrpos)
  have hC0mn : C₀ / min (1 : ℝ) (c / r) ≤ C := le_trans (le_max_left _ _) hCrest
  have hCClin : Clin ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCrest
  have hCLthresh_le : CLthresh ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCrest
  have hC0nonneg : (0 : ℝ) ≤ C := le_trans zero_le_one hC1'
  -- Step (i): the inflation, at ratio r.
  obtain ⟨hMthr1, _hCthrleC, hcMthrger, hLthr⟩ := homogBelow_inflateMR
    (C := C) (M := M) (c := c) (r := r) (alpha := alpha) (cStar := cStar) (nu := nu) (K := K)
    hC0nonneg hM1 hcpos hrpos halpha1 hcStar hnu hK hL
  -- Step (ii): C₀ ≤ Cthr.
  have hC0leCthr : C₀ ≤ C * min (1 : ℝ) (c / r) := by
    have hstep : C₀ / min (1 : ℝ) (c / r) * min (1 : ℝ) (c / r) ≤ C * min (1 : ℝ) (c / r) :=
      mul_le_mul_of_nonneg_right hC0mn hminpos.le
    rwa [div_mul_cancel₀ C₀ hminpos.ne'] at hstep
  -- Step (iii): the sstar threshold fact, at (c, Mthr).
  obtain ⟨_, hSstarApplied, _, _⟩ :=
    hThreshBody (C * min (1 : ℝ) (c / r)) hC0leCthr (M * max (1 : ℝ) (r / c)) alpha cStar nu K
      hMthr1 halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hLthr
  -- Step (iv): L ≥ 2·Lthresh+1.
  have hCMge1 : (1 : ℝ) ≤ C * M := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ C * M := mul_le_mul hC1' hM1 (by norm_num) (by linarith only [hC1'])
  have hLge := hlin C hCClin (C * M) hCMge1 alpha halpha0 halpha1 cStar hcStar hcStar2
    nu hnu hnu1 K hK
  have hLgeReal : (Real.log 2) ^ (12 : ℝ) / 4 * C ≤ (L : ℝ) := le_trans hLge hL
  have hL2Lthresh1 : 2 * Lthresh + 1 ≤ (L : ℝ) := by
    have hstep : (4 : ℝ) * (2 * Lthresh + 1) ≤ (Real.log 2) ^ (12 : ℝ) * C := by
      rw [hCLthreshdef, div_le_iff₀ hlog2pow_pos] at hCLthresh_le
      nlinarith only [hCLthresh_le]
    have hstep2 : 2 * Lthresh + 1 ≤ (Real.log 2) ^ (12 : ℝ) / 4 * C := by
      have heq : (Real.log 2) ^ (12 : ℝ) / 4 * C = (Real.log 2) ^ (12 : ℝ) * C / 4 := by ring
      rw [heq, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      linarith only [hstep]
    linarith only [hstep2, hLgeReal]
  -- Step (v): L ≥ 3, log L ≥ 1, hence Lr > 0.
  have hL3R : (3 : ℝ) ≤ (L : ℝ) := by linarith only [hL2Lthresh1, hLthresh_ge1]
  have hlogL_gt1 : (1 : ℝ) < Real.log (L : ℝ) := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hlt : Real.exp 1 < (L : ℝ) := lt_of_lt_of_le he3 hL3R
    have hh := Real.log_lt_log (Real.exp_pos 1) hlt
    rwa [Real.log_exp] at hh
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith only [hL3R]
  have hLrpos : (0 : ℝ) < (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hLpos alpha)
      (Real.rpow_pos_of_pos (by linarith only [hlogL_gt1]) 3)
  -- Step (vi): m3-real headroom is enough for h too, real subtraction monotone.
  have hm3R : (m3 : ℝ) ≤ (h : ℝ) - 1 := by
    have : m3 + 1 ≤ h := hm3lth
    have : (m3 : ℝ) + 1 ≤ (h : ℝ) := by exact_mod_cast this
    linarith only [this]
  -- Step (vii): case split h ≤ L vs L < h.
  rcases le_or_gt h L with hhL | hhL
  · -- main case.
    have hL2h_nat : L ≤ 2 * h := by omega
    have hL2h_real : (L : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hL2h_nat
    have hbaseL : Lthresh ≤ max 1 (h : ℝ) :=
      le_trans (by linarith only [hL2Lthresh1, hL2h_real]) (le_max_right _ _)
    have hAcast : ((L - h : ℕ) : ℝ) = (L : ℝ) - (h : ℝ) := by
      have := Nat.cast_sub (R := ℝ) hhL
      simpa using this
    have hAbound : ((L - h : ℕ) : ℝ) ≤
        Kappa3 * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by
      rw [hAcast]
      linarith only [hm3ge, hm3R]
    have hSsq : r * Cmix * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
          (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ) := by
      have hraw := hSstarApplied h hL2h_real hhL
      have hLrnonneg : (0 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := hLrpos.le
      have hchain : r * Cmix * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) ≤
          c * (Cmix * (M * max (1 : ℝ) (r / c))) * (L : ℝ) ^ alpha *
            Real.log (L : ℝ) ^ (3 : ℝ) := by
        have hmulr : r * (Cmix * M) ≤ (c * max (1 : ℝ) (r / c)) * (Cmix * M) :=
          mul_le_mul_of_nonneg_right hcMthrger (by positivity)
        nlinarith only [hmulr, hLrnonneg]
      linarith only [hchain, hraw]
    exact homogBelow_smallness_core nu hnu L Cmix P hPrefix hJ2 hJ3 hJ4 hCmix1
      hUps1 hKappa3 hrpos hM1 hLrpos hK3def.symm hrgeA hrgeB hLthresh_ge h hbaseL hAbound hSsq
  · -- far case.
    have hbaseL : Lthresh ≤ max 1 (h : ℝ) := by
      have hLh_real : (L : ℝ) ≤ (h : ℝ) := by exact_mod_cast hhL.le
      exact le_trans (by linarith only [hL2Lthresh1, hLh_real]) (le_max_right _ _)
    exact homogBelow_smallness_far nu L Cmix P hCmix1 hUps1 hK3def.symm hLthresh_ge h hhL.le hbaseL

end SuperdiffusionCLT.Section4.HomogBelow
