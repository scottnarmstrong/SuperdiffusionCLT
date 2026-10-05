/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.NearShiftAssemblyA2

/-!
# Near-scale assembly: deterministic bookkeeping of the weighted sum

* `srootNSD_weight_sum_sq_le`: `Σ_{l<N} w_l l² ≤ 7 / s²`.
* `srootNSD_weighted_poly_le`: `Σ w_l (c₀ + c₁ l + c₂ l²) ≤ c₀ + 2 c₁ / s + 7 c₂ / s²`.
* `srootNSD_det_bound`: the weighted sum of the deterministic part of the pathwise near bound,
  including the centering `α_l log N_l` of the maximum over the window and the descendants, is at
  most a main term `s⁻¹ K σ⁻² log² m` and a term `s⁻² K σ⁻² log m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

private theorem srootNSD_w_nonneg {s : ℝ} (hs0 : 0 < s) (l : ℕ) :
    0 ≤ Homogenization.geometricWeight s 2 l :=
  Homogenization.geometricWeight_nonneg l (by linarith only [hs0])

/-- `Σ_{l<N} w_l · l² ≤ 7 / s²`. -/
theorem srootNSD_weight_sum_sq_le {s : ℝ} (hs0 : 0 < s) (N : ℕ) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ^ 2 ≤ 7 / s ^ 2 := by
  have h1 := srootNS_weight_sum_mul_le hs0 N
  have h3 := srootNS_weight_sum_mul_cube_le hs0 N
  have hpt : ∀ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l * (l : ℝ) ^ 2 ≤
      (s / 2) * (Homogenization.geometricWeight s 2 l * (l : ℝ) ^ 3) +
        (1 / (2 * s)) * (Homogenization.geometricWeight s 2 l * (l : ℝ)) := by
    intro l _
    have hw := srootNSD_w_nonneg hs0 l
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have key : (l : ℝ) ^ 2 ≤ (s / 2) * (l : ℝ) ^ 3 + (1 / (2 * s)) * (l : ℝ) := by
      have h : 0 ≤ (l : ℝ) * (s * (l : ℝ) - 1) ^ 2 / (2 * s) := by positivity
      have e : (l : ℝ) * (s * (l : ℝ) - 1) ^ 2 / (2 * s) =
          (s / 2) * (l : ℝ) ^ 3 + (1 / (2 * s)) * (l : ℝ) - (l : ℝ) ^ 2 := by
        field_simp
        ring
      linarith only [h, e]
    have := mul_le_mul_of_nonneg_left key hw
    linarith only [this]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e1 : s / 2 * (12 / s ^ 3) = 6 / s ^ 2 := by
    field_simp
    norm_num
  have e2 : 1 / (2 * s) * (2 / s) = 1 / s ^ 2 := by field_simp
  have a1 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ s / 2)
  have a2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (2 * s))
  have e3 : (7 : ℝ) / s ^ 2 = 6 / s ^ 2 + 1 / s ^ 2 := by ring
  linarith only [a1, a2, e1, e2, e3]

/-- `Σ_{l<N} w_l (c₀ + c₁ l + c₂ l²) ≤ c₀ + 2 c₁ / s + 7 c₂ / s²` for nonnegative `c_i`. -/
theorem srootNSD_weighted_poly_le {s c0 c1 c2 : ℝ} (hs0 : 0 < s) (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (hc2 : 0 ≤ c2) (N : ℕ) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (c0 + c1 * (l : ℝ) + c2 * (l : ℝ) ^ 2) ≤ c0 + c1 * (2 / s) + c2 * (7 / s ^ 2) := by
  have e : ∀ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (c0 + c1 * (l : ℝ) + c2 * (l : ℝ) ^ 2) =
      c0 * Homogenization.geometricWeight s 2 l +
        c1 * (Homogenization.geometricWeight s 2 l * (l : ℝ)) +
        c2 * (Homogenization.geometricWeight s 2 l * (l : ℝ) ^ 2) := fun l _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have a0 := mul_le_mul_of_nonneg_left (srootNS_weight_sum_le_one hs0 N) hc0
  have a1 := mul_le_mul_of_nonneg_left (srootNS_weight_sum_mul_le hs0 N) hc1
  have a2 := mul_le_mul_of_nonneg_left (srootNSD_weight_sum_sq_le hs0 N) hc2
  linarith only [a0, a1, a2]

/-- The weighted deterministic part of the near bound together with the centering of the maximum.
`S = σ⁻²`; `H0 ≤ cH K log m log (2h)`; `h ≤ 2 K lg`; `L2 ≤ 4 lg²`; `Kp ≤ 4 C1 s⁻¹ K`; the
centering of depth `l` is `(2 h + l + 2 Kp lg) (2 lg + 2 D l)`. -/
theorem srootNSD_det_bound {Cp cH S s K C1 lg lg2 H0 h L2 Kp D : ℝ} (N : ℕ)
    (hCp : 0 ≤ Cp) (hcH : 0 ≤ cH) (hS : 0 ≤ S) (hs0 : 0 < s) (hs1 : s ≤ 1) (hK : 1 ≤ K)
    (hC1 : 1 ≤ C1) (hlg : 1 ≤ lg) (hD : 0 ≤ D) (hlg2 : lg2 ≤ 2 * lg) (hH0 : 0 ≤ H0)
    (hH : H0 ≤ cH * (K * lg * lg2)) (hh0 : 0 ≤ h) (hh : h ≤ 2 * K * lg) (hL20 : 0 ≤ L2)
    (hL2 : L2 ≤ 4 * lg ^ 2) (hKp0 : 0 ≤ Kp) (hKp : Kp ≤ 4 * C1 * s⁻¹ * K) :
    ∑ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (Cp * S * (H0 + 2 * h + (l : ℝ) + Kp * L2) +
          Cp * S * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ))) ≤
      Cp * (2 * cH + 44) * C1 * s⁻¹ * K * S * lg ^ 2 +
        Cp * (6 + 62 * D) * C1 * (s⁻¹) ^ 2 * K * S * lg := by
  set t : ℝ := s⁻¹ with ht
  have ht1 : 1 ≤ t := by rw [ht]; exact one_le_inv₀ hs0 |>.2 hs1
  have hCt : 1 ≤ C1 * t := by nlinarith only [hC1, ht1]
  have hu : 1 ≤ K * lg := by nlinarith only [hK, hlg]
  have hu0 : 0 ≤ K * lg := by linarith only [hu]
  have hlgK : lg ≤ K * lg := by nlinarith only [hK, hlg]
  have hKplg : Kp * lg ≤ 4 * C1 * t * (K * lg) := by
    have := mul_le_mul_of_nonneg_right hKp (by linarith only [hlg] : (0 : ℝ) ≤ lg)
    linarith only [this]
  have hu' : K * lg ≤ C1 * t * (K * lg) := by nlinarith only [hCt, hu0]
  have ha : 2 * h + 2 * Kp * lg ≤ 12 * C1 * t * (K * lg) := by
    nlinarith only [hh, hKplg, hu', hlg]
  have hK2 : 0 ≤ K * lg ^ 2 := by positivity
  have hu2 : K * lg ≤ K * lg ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlg hu0
    have e : K * lg * lg = K * lg ^ 2 := by ring
    linarith only [this, e]
  have hw : K * lg ^ 2 ≤ C1 * t * (K * lg ^ 2) := by
    have := mul_le_mul_of_nonneg_right hCt hK2
    linarith only [this]
  have hP0a : H0 ≤ 2 * cH * (C1 * t * (K * lg ^ 2)) := by
    have h1 : H0 ≤ cH * (K * lg * (2 * lg)) := by
      refine hH.trans (mul_le_mul_of_nonneg_left ?_ hcH)
      exact mul_le_mul_of_nonneg_left hlg2 hu0
    have h2 : cH * (K * lg * (2 * lg)) = 2 * cH * (K * lg ^ 2) := by ring
    have h3 := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 2 * cH)
    linarith only [h1, h2, h3]
  have hP0b : 2 * h ≤ 4 * (C1 * t * (K * lg ^ 2)) := by nlinarith only [hh, hu2, hw]
  have hP0c : Kp * L2 ≤ 16 * (C1 * t * (K * lg ^ 2)) := by
    have h1 : Kp * L2 ≤ Kp * (4 * lg ^ 2) := mul_le_mul_of_nonneg_left hL2 hKp0
    have h2 : Kp * (4 * lg ^ 2) = 4 * (Kp * lg) * lg := by ring
    have h3 : 4 * (Kp * lg) * lg ≤ 4 * (4 * C1 * t * (K * lg)) * lg :=
      mul_le_mul_of_nonneg_right (by linarith only [hKplg]) (by linarith only [hlg])
    have h4 : 4 * (4 * C1 * t * (K * lg)) * lg = 16 * (C1 * t * (K * lg ^ 2)) := by ring
    linarith only [h1, h2, h3, h4]
  have hP0d : (2 * h + 2 * Kp * lg) * (2 * lg) ≤ 24 * (C1 * t * (K * lg ^ 2)) := by
    have h1 : (2 * h + 2 * Kp * lg) * (2 * lg) ≤ 12 * C1 * t * (K * lg) * (2 * lg) :=
      mul_le_mul_of_nonneg_right ha (by linarith only [hlg])
    have h4 : 12 * C1 * t * (K * lg) * (2 * lg) = 24 * (C1 * t * (K * lg ^ 2)) := by ring
    linarith only [h1, h4]
  have hP0 : H0 + 2 * h + Kp * L2 + (2 * h + 2 * Kp * lg) * (2 * lg) ≤
      (2 * cH + 44) * (C1 * t * (K * lg ^ 2)) := by
    linarith only [hP0a, hP0b, hP0c, hP0d]
  have hP1 : 1 + (2 * h + 2 * Kp * lg) * (2 * D) + 2 * lg ≤
      (3 + 24 * D) * (C1 * t * (K * lg)) := by
    have h1 : (2 * h + 2 * Kp * lg) * (2 * D) ≤ 12 * C1 * t * (K * lg) * (2 * D) :=
      mul_le_mul_of_nonneg_right ha (by linarith only [hD])
    have h4 : 12 * C1 * t * (K * lg) * (2 * D) = 24 * D * (C1 * t * (K * lg)) := by ring
    have h5 : 2 * lg ≤ 2 * (C1 * t * (K * lg)) := by linarith only [hlgK, hu']
    have h6 : (1 : ℝ) ≤ C1 * t * (K * lg) := by linarith only [hu, hu']
    nlinarith only [h1, h4, h5, h6, hD]
  have hP1' : 0 ≤ 1 + (2 * h + 2 * Kp * lg) * (2 * D) + 2 * lg := by positivity
  have hpt : ∀ l ∈ Finset.range N, Homogenization.geometricWeight s 2 l *
        (Cp * S * (H0 + 2 * h + (l : ℝ) + Kp * L2) +
          Cp * S * (2 * h + (l : ℝ) + 2 * Kp * lg) * (2 * lg + 2 * D * (l : ℝ))) =
      Homogenization.geometricWeight s 2 l * ((Cp * S * (H0 + 2 * h + Kp * L2 +
          (2 * h + 2 * Kp * lg) * (2 * lg))) +
        (Cp * S * (1 + (2 * h + 2 * Kp * lg) * (2 * D) + 2 * lg)) * (l : ℝ) +
        (Cp * S * (2 * D)) * (l : ℝ) ^ 2) := fun l _ => by ring
  rw [Finset.sum_congr rfl hpt]
  have hCS : 0 ≤ Cp * S := mul_nonneg hCp hS
  have hha : 0 ≤ 2 * h + 2 * Kp * lg := by positivity
  refine le_trans (srootNSD_weighted_poly_le hs0 ?_ ?_ ?_ N) ?_
  · exact mul_nonneg hCS (by positivity)
  · exact mul_nonneg hCS hP1'
  · exact mul_nonneg hCS (by linarith only [hD])
  have e2 : (2 : ℝ) / s = 2 * t := by rw [ht]; ring
  have e7 : (7 : ℝ) / s ^ 2 = 7 * t ^ 2 := by rw [ht]; field_simp
  rw [e2, e7]
  have b0 := mul_le_mul_of_nonneg_left hP0 hCS
  have b1 := mul_le_mul_of_nonneg_left hP1 hCS
  have b1' : Cp * S * (1 + (2 * h + 2 * Kp * lg) * (2 * D) + 2 * lg) * (2 * t) ≤
      Cp * S * ((3 + 24 * D) * (C1 * t * (K * lg))) * (2 * t) :=
    mul_le_mul_of_nonneg_right b1 (by linarith only [ht1])
  have hlast : Cp * S * (2 * D) * (7 * t ^ 2) ≤
      Cp * S * (14 * D) * (C1 * t ^ 2 * (K * lg)) := by
    have h1 : (1 : ℝ) ≤ C1 * (K * lg) := by nlinarith only [hC1, hu]
    have h2 : 0 ≤ Cp * S * (14 * D) * t ^ 2 := by positivity
    nlinarith only [h1, h2]
  calc _ ≤ Cp * S * ((2 * cH + 44) * (C1 * t * (K * lg ^ 2))) +
        Cp * S * ((3 + 24 * D) * (C1 * t * (K * lg))) * (2 * t) +
        Cp * S * (14 * D) * (C1 * t ^ 2 * (K * lg)) := by linarith only [b0, b1', hlast]
    _ = _ := by ring

end

end SuperdiffusionCLT.Section4.MinimalScales
