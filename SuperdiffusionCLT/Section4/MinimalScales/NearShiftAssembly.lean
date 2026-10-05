/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.SkeletonMathcalE

/-!
# Near-scale assembly: the weighted geometric sums and the constant bookkeeping

Deterministic arithmetic for the near-scale bound `hNear` (the near-scale estimate and the
recentering step in the proof of `p.new.mixing.attempt`). The weight of
depth `l` in `srootE_term` is `Homogenization.geometricWeight s 2 l = (1 - 3^{-2s}) 3^{-2sl}`.

* `srootNS_css_ge`: `s / 2 ≤ 1 - 3^{-2s}` for `0 < s ≤ 1`.
* `srootNS_weight_sum_le_one`, `srootNS_weight_sum_mul_le`, `srootNS_weight_sum_mul_cube_le`:
  `Σ w_l ≤ 1`, `Σ w_l l ≤ 2 / s`, `Σ w_l l³ ≤ 12 / s³`.
* `srootNS_weighted_bookkeeping`: the weighted sum of the pathwise near bound is at most
  `Cp (2 cH + 22) C1 s⁻¹ K σ⁻² log² m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

private theorem srootNS_log_three_ge_one : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith only [this]

/-- The geometric normalization is at least `s / 2`. -/
theorem srootNS_css_ge {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    s / 2 ≤ Homogenization.geometricDiscount s 2 := by
  unfold Homogenization.geometricDiscount
  have hl3 := srootNS_log_three_ge_one
  set x : ℝ := 2 * s * Real.log 3 with hx
  have hx2 : 2 * s ≤ x := by
    have : s * 1 ≤ s * Real.log 3 := mul_le_mul_of_nonneg_left hl3 hs0.le
    rw [hx]; linarith only [this]
  have hxpos : 0 < x := by linarith only [hx2, hs0]
  have hr : Real.rpow (3 : ℝ) (-s * 2) = Real.exp (-x) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    rw [hx]; ring
  rw [hr, Real.exp_neg]
  have hE : 1 + x ≤ Real.exp x := by linarith only [Real.add_one_le_exp x]
  have hEpos : 0 < Real.exp x := Real.exp_pos x
  have key : 1 ≤ (1 - s / 2) * Real.exp x := by
    have h1 : (1 - s / 2) * (1 + x) ≤ (1 - s / 2) * Real.exp x :=
      mul_le_mul_of_nonneg_left hE (by linarith only [hs1])
    have h2 : s * x ≤ x := by
      have := mul_le_mul_of_nonneg_right hs1 hxpos.le
      linarith only [this]
    have h3 : 1 ≤ (1 - s / 2) * (1 + x) := by nlinarith only [h2, hx2, hs0]
    linarith only [h1, h3]
  have : (Real.exp x)⁻¹ ≤ 1 - s / 2 := by
    have h1 := mul_le_mul_of_nonneg_left key (inv_nonneg.2 hEpos.le)
    have h2 : (Real.exp x)⁻¹ * ((1 - s / 2) * Real.exp x) = 1 - s / 2 := by
      field_simp
    linarith only [h1, h2]
  linarith only [this]

private theorem srootNS_rpow_neg (s : ℝ) :
    Real.rpow (3 : ℝ) (-s * 2) = Real.exp (-(2 * (s * Real.log 3))) := by
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

private theorem srootNS_weight_eq (s : ℝ) (l : ℕ) :
    Homogenization.geometricWeight s 2 l =
      (1 - Real.exp (-(2 * (s * Real.log 3)))) *
        (Real.exp (-(s * Real.log 3))) ^ (2 * l) := by
  unfold Homogenization.geometricWeight Homogenization.geometricDiscount
  rw [srootNS_rpow_neg]
  congr 1
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (by norm_num), ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Total weight at most one. -/
theorem srootNS_weight_sum_le_one {s : ℝ} (hs0 : 0 < s) (N : ℕ) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l ≤ 1 := by
  have hl3 := srootNS_log_three_ge_one
  set t : ℝ := s * Real.log 3 with ht
  have htpos : 0 < t := by
    have : s * 1 ≤ s * Real.log 3 := mul_le_mul_of_nonneg_left hl3 hs0.le
    rw [ht]; linarith only [this, hs0]
  set ρ : ℝ := Real.exp (-t) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρ]; exact by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith only [htpos])
  have hr : Real.exp (-(2 * t)) = ρ ^ 2 := by
    rw [hρ, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have heq : ∀ l : ℕ, Homogenization.geometricWeight s 2 l = (1 - ρ ^ 2) * (ρ ^ 2) ^ l := by
    intro l
    rw [srootNS_weight_eq, hr, pow_mul]
  simp_rw [heq]
  rw [← Finset.mul_sum]
  have h := geom_sum_mul_neg (ρ ^ 2) N
  have hpn : 0 ≤ (ρ ^ 2) ^ N := by positivity
  rw [mul_comm]
  linarith only [h, hpn]

/-- Bound on `l^k r^l`: with `ρ = exp(-t)`, `l^k ρ^{2l} ≤ k!/t^k ρ^l`. -/
private theorem srootNS_pow_mul_le {t : ℝ} (ht : 0 < t) (k l : ℕ) :
    (l : ℝ) ^ k * (Real.exp (-t)) ^ (2 * l) ≤
      (k.factorial : ℝ) / t ^ k * (Real.exp (-t)) ^ l := by
  have h1 := Real.pow_div_factorial_le_exp (x := t * l) (by positivity) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have htk : (0 : ℝ) < t ^ k := by positivity
  have hpl : (Real.exp (-t)) ^ (2 * l) = Real.exp (-(t * l)) * Real.exp (-(t * l)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hpl2 : (Real.exp (-t)) ^ l = Real.exp (-(t * l)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hpl, hpl2]
  have hEpos : 0 < Real.exp (-(t * l)) := Real.exp_pos _
  have hmul : Real.exp (t * l) * Real.exp (-(t * l)) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : (l : ℝ) ^ k = (t * l) ^ k / t ^ k := by
    rw [mul_pow]; field_simp
  rw [h2]
  have h3 : (t * l) ^ k / t ^ k ≤ (k.factorial : ℝ) * Real.exp (t * l) / t ^ k := by
    apply div_le_div_of_nonneg_right _ htk.le
    rw [div_le_iff₀ hfac] at h1
    linarith only [h1]
  calc (t * l) ^ k / t ^ k * (Real.exp (-(t * l)) * Real.exp (-(t * l)))
      ≤ (k.factorial : ℝ) * Real.exp (t * l) / t ^ k *
          (Real.exp (-(t * l)) * Real.exp (-(t * l))) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = (k.factorial : ℝ) / t ^ k * Real.exp (-(t * l)) *
          (Real.exp (t * l) * Real.exp (-(t * l))) := by ring
    _ = (k.factorial : ℝ) / t ^ k * Real.exp (-(t * l)) := by rw [hmul, mul_one]

private theorem srootNS_weight_sum_mul_pow_le {s : ℝ} (hs0 : 0 < s) (k N : ℕ) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ^ k ≤
      2 * ((k.factorial : ℝ) / (s * Real.log 3) ^ k) := by
  have hl3 := srootNS_log_three_ge_one
  set t : ℝ := s * Real.log 3 with ht
  have htpos : 0 < t := by
    have : s * 1 ≤ s * Real.log 3 := mul_le_mul_of_nonneg_left hl3 hs0.le
    rw [ht]; linarith only [this, hs0]
  set ρ : ℝ := Real.exp (-t) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by rw [hρ]; exact by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith only [htpos])
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hc : 0 ≤ (k.factorial : ℝ) / t ^ k := by positivity
  have hterm : ∀ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ^ k ≤
      (1 - ρ ^ 2) * ((k.factorial : ℝ) / t ^ k) * ρ ^ l := by
    intro l _
    have h1 := srootNS_pow_mul_le htpos k l
    have h2 : (1 - ρ ^ 2) ≥ 0 := by nlinarith only [hρ0, hρ1]
    rw [srootNS_weight_eq]
    calc (1 - Real.exp (-(2 * (s * Real.log 3)))) * ρ ^ (2 * l) * (l : ℝ) ^ k
        = (1 - ρ ^ 2) * ((l : ℝ) ^ k * ρ ^ (2 * l)) := by
          have : Real.exp (-(2 * (s * Real.log 3))) = ρ ^ 2 := by
            rw [hρ, ← Real.exp_nat_mul]; congr 1; push_cast; rw [ht]; ring
          rw [this]; ring
      _ ≤ (1 - ρ ^ 2) * ((k.factorial : ℝ) / t ^ k * ρ ^ l) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have h := geom_sum_mul_neg ρ N
  have hpn : 0 ≤ ρ ^ N := by positivity
  have hgeo : (∑ i ∈ Finset.range N, ρ ^ i) * (1 - ρ) ≤ 1 := by linarith only [h, hpn]
  have hsum_le : (1 - ρ ^ 2) * (∑ i ∈ Finset.range N, ρ ^ i) ≤ 1 + ρ := by
    have : (1 - ρ ^ 2) * (∑ i ∈ Finset.range N, ρ ^ i) =
        (1 + ρ) * ((∑ i ∈ Finset.range N, ρ ^ i) * (1 - ρ)) := by ring
    rw [this]
    calc (1 + ρ) * ((∑ i ∈ Finset.range N, ρ ^ i) * (1 - ρ)) ≤ (1 + ρ) * 1 :=
          mul_le_mul_of_nonneg_left hgeo (by linarith only [hρ0])
      _ = 1 + ρ := by ring
  calc (1 - ρ ^ 2) * ((k.factorial : ℝ) / t ^ k) * ∑ i ∈ Finset.range N, ρ ^ i
      = ((1 - ρ ^ 2) * ∑ i ∈ Finset.range N, ρ ^ i) * ((k.factorial : ℝ) / t ^ k) := by ring
    _ ≤ 2 * ((k.factorial : ℝ) / t ^ k) :=
        mul_le_mul_of_nonneg_right (by linarith only [hsum_le, hρ1]) hc

/-- `Σ_{l<N} w_l · l ≤ 2 / s`. -/
theorem srootNS_weight_sum_mul_le {s : ℝ} (hs0 : 0 < s) (N : ℕ) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ≤ 2 / s := by
  have h := srootNS_weight_sum_mul_pow_le hs0 1 N
  have hl3 := srootNS_log_three_ge_one
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h
  refine le_trans h ?_
  have : s ≤ s * Real.log 3 := by nlinarith only [hl3, hs0]
  have h2 : 1 / (s * Real.log 3) ≤ 1 / s := one_div_le_one_div_of_le hs0 this
  calc 2 * (1 / (s * Real.log 3)) ≤ 2 * (1 / s) := by linarith only [h2]
    _ = 2 / s := by ring

/-- `Σ_{l<N} w_l · l³ ≤ 12 / s³`. -/
theorem srootNS_weight_sum_mul_cube_le {s : ℝ} (hs0 : 0 < s) (N : ℕ) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ^ 3 ≤ 12 / s ^ 3 := by
  have h := srootNS_weight_sum_mul_pow_le hs0 3 N
  have hl3 := srootNS_log_three_ge_one
  have hfac : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h
  refine le_trans h ?_
  have : s ≤ s * Real.log 3 := by nlinarith only [hl3, hs0]
  have h3 : s ^ 3 ≤ (s * Real.log 3) ^ 3 := pow_le_pow_left₀ hs0.le this 3
  have h2 : 6 / (s * Real.log 3) ^ 3 ≤ 6 / s ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h3
  calc 2 * (6 / (s * Real.log 3) ^ 3) ≤ 2 * (6 / s ^ 3) := by linarith only [h2]
    _ = 12 / s ^ 3 := by ring

/-- The weighted near-scale bookkeeping. Here `S` stands for `σ⁻²`, `H` for the deterministic
skew-average bound `cH K log m log(2h)` (`lg = log m`, `lg2 = log (2h)`), `L2` for `log² L`
and `Kp ≤ 4 C1 s⁻¹ K` for the shifted-window constant. -/
theorem srootNS_weighted_bookkeeping {Cp cH S s K C1 lg lg2 H h L2 Kp : ℝ} (N : ℕ)
    (hCp : 0 ≤ Cp) (hcH : 0 ≤ cH) (hS : 0 ≤ S) (hs0 : 0 < s) (hs1 : s ≤ 1) (hK : 1 ≤ K)
    (hC1 : 1 ≤ C1) (hlg : 1 ≤ lg) (hlg2le : lg2 ≤ 2 * lg) (hH0 : 0 ≤ H)
    (hH : H ≤ cH * (K * lg * lg2)) (hh0 : 0 ≤ h) (hh : h ≤ 2 * K * lg) (hL20 : 0 ≤ L2)
    (hL2 : L2 ≤ 4 * lg ^ 2) (hKp0 : 0 ≤ Kp) (hKp : Kp ≤ 4 * C1 * s⁻¹ * K) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (Cp * S * (H + 2 * h + (l : ℝ) + Kp * L2)) ≤
      Cp * (2 * cH + 22) * C1 * s⁻¹ * K * S * lg ^ 2 := by
  set c : ℝ := H + 2 * h + Kp * L2 with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hw0 : ∀ l : ℕ, 0 ≤ Homogenization.geometricWeight s 2 l := by
    intro l
    rw [srootNS_weight_eq]
    have hρ1 : Real.exp (-(2 * (s * Real.log 3))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith only [srootNS_log_three_ge_one, hs0])
    exact mul_nonneg (by linarith only [hρ1]) (by positivity)
  have hsum : ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (Cp * S * (H + 2 * h + (l : ℝ) + Kp * L2)) =
      Cp * S * (c * ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l +
        ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ)) := by
    have hl : ∀ l : ℕ, Homogenization.geometricWeight s 2 l *
        (Cp * S * (H + 2 * h + (l : ℝ) + Kp * L2)) =
        Cp * S * (c * Homogenization.geometricWeight s 2 l +
          Homogenization.geometricWeight s 2 l * (l : ℝ)) := by
      intro l; rw [hc]; ring
    simp_rw [hl]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := srootNS_weight_sum_le_one hs0 N
  have h2 := srootNS_weight_sum_mul_le hs0 N
  have hs1inv : 1 ≤ s⁻¹ := (one_le_inv₀ hs0).2 hs1
  have hsum0 : 0 ≤ ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l :=
    Finset.sum_nonneg fun l _ => hw0 l
  have hA : c * ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l ≤ c := by
    calc _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1 hc0
      _ = c := mul_one c
  have hsinv2 : 2 / s = 2 * s⁻¹ := by rw [div_eq_mul_inv]
  set Q : ℝ := C1 * s⁻¹ * K * lg ^ 2 with hQ
  have hQ1 : 1 ≤ Q := by
    have h1' : 1 ≤ C1 * s⁻¹ := by nlinarith only [hC1, hs1inv]
    have h2' : 1 ≤ C1 * s⁻¹ * K := by nlinarith only [h1', hK]
    have h3' : 1 ≤ lg ^ 2 := by nlinarith only [hlg]
    rw [hQ]; nlinarith only [h2', h3']
  have hHb : H ≤ 2 * cH * Q := by
    have : K * lg * lg2 ≤ K * lg * (2 * lg) :=
      mul_le_mul_of_nonneg_left hlg2le (by positivity)
    have h4 : cH * (K * lg * lg2) ≤ cH * (K * lg * (2 * lg)) :=
      mul_le_mul_of_nonneg_left this hcH
    have h5 : K * lg * (2 * lg) = 2 * (K * lg ^ 2) := by ring
    have h6 : K * lg ^ 2 ≤ Q := by
      rw [hQ]
      have h1' : 1 ≤ C1 * s⁻¹ := by nlinarith only [hC1, hs1inv]
      have : K * lg ^ 2 * 1 ≤ K * lg ^ 2 * (C1 * s⁻¹) :=
        mul_le_mul_of_nonneg_left h1' (by positivity)
      nlinarith only [this]
    nlinarith only [hH, h4, h5, h6, hcH]
  have hhb : 2 * h ≤ 4 * Q := by
    have h6 : K * lg ≤ Q := by
      have h1' : 1 ≤ C1 * s⁻¹ := by nlinarith only [hC1, hs1inv]
      have h7 : K * lg ≤ K * lg ^ 2 := by
        have : K * lg * 1 ≤ K * lg * lg := mul_le_mul_of_nonneg_left hlg (by positivity)
        nlinarith only [this]
      have : K * lg ^ 2 * 1 ≤ K * lg ^ 2 * (C1 * s⁻¹) :=
        mul_le_mul_of_nonneg_left h1' (by positivity)
      rw [hQ]; nlinarith only [this, h7]
    nlinarith only [hh, h6]
  have hKpb : Kp * L2 ≤ 16 * Q := by
    have h7 : Kp * L2 ≤ (4 * C1 * s⁻¹ * K) * (4 * lg ^ 2) :=
      mul_le_mul hKp hL2 hL20 (by positivity)
    rw [hQ]; nlinarith only [h7]
  have hl : ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ≤ 2 * Q := by
    have : s⁻¹ ≤ Q := by
      have h1' : 1 ≤ C1 := hC1
      have h8 : 1 ≤ K * lg ^ 2 := by nlinarith only [hlg, hK]
      have : s⁻¹ * 1 ≤ s⁻¹ * (C1 * (K * lg ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith only [h1', h8]
      rw [hQ]; nlinarith only [this]
    rw [hsinv2] at h2
    linarith only [h2, this]
  have hfin : c * ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l +
      ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ≤
      (2 * cH + 22) * Q := by
    rw [hc] at hA
    nlinarith only [hA, hl, hHb, hhb, hKpb]
  rw [hsum]
  calc Cp * S * (c * ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l +
        ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ))
      ≤ Cp * S * ((2 * cH + 22) * Q) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = Cp * (2 * cH + 22) * C1 * s⁻¹ * K * S * lg ^ 2 := by rw [hQ]; ring

/-- Satisfiability: every hypothesis of the weighted bookkeeping is met at `s = 1`, all constants
`1` and `N = 3`. -/
example : ∑ l ∈ Finset.range 3, Homogenization.geometricWeight 1 2 l *
        ((1 : ℝ) * 1 * (1 + 2 * 1 + (l : ℝ) + 4 * 4)) ≤
      1 * (2 * 1 + 22) * 1 * (1 : ℝ)⁻¹ * 1 * 1 * 1 ^ 2 :=
  srootNS_weighted_bookkeeping (Cp := 1) (cH := 1) (S := 1) (s := 1) (K := 1) (C1 := 1)
    (lg := 1) (lg2 := 1) (H := 1) (h := 1) (L2 := 4) (Kp := 4) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : 1 / 2 ≤ Homogenization.geometricDiscount 1 2 := srootNS_css_ge one_pos le_rfl

example : ∑ l ∈ Finset.range 5, Homogenization.geometricWeight 1 2 l * (l : ℝ) ^ 3 ≤ 12 / 1 ^ 3 :=
  srootNS_weight_sum_mul_cube_le one_pos 5

end

end SuperdiffusionCLT.Section4.MinimalScales
