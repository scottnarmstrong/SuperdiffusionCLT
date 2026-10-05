/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyRatioAlg
public import SuperdiffusionCLT.Section4.NewMixing.AssemblyScaleFacts

/-!
# Folding the pieces of the reference comparison

Real-variable lemmas: the bounds on `σ δ` and `σ³ δ`, the bound on the `n^{-3000}` term, and the
final combination of the homogenization errors at the two cutoffs with the lower-block
comparison.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

noncomputable section

/-- `L^k L^{-e} ≤ 1` for `L ≥ 1` and `k ≤ e`. -/
theorem newMixAsm_pow_mul_rpow_le_one {L e : ℝ} {k : ℕ} (hL : 1 ≤ L) (hk : (k : ℝ) ≤ e) :
    L ^ k * L ^ (-e) ≤ 1 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
  exact Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith only [hk])

/-- The two products `σ δ` and `σ³ δ`, with `σ ≤ 3 Cc C₃ L²` and `δ ≤ Cst C₃ L q`, `q = L^{-200}`. -/
theorem newMixAsm_sigma_delta {σ δ L q Cc Cst C3 Cp : ℝ} (hσ0 : 0 ≤ σ) (hδ0 : 0 ≤ δ)
    (hL1 : 1 ≤ L) (hq0 : 0 ≤ q) (hCc : 0 ≤ Cc) (hCst : 0 ≤ Cst) (hC3 : 0 ≤ C3)
    (hσle : σ ≤ 3 * Cc * C3 * L ^ 2) (hδle : δ ≤ Cst * (C3 * L) * q)
    (h7 : L ^ 7 * q ≤ 1) (h4 : L ^ 4 * q ≤ 1)
    (hΛ : 8 * Cc * Cst * C3 ^ 2 ≤ Cp) (hLCp : Cp ≤ L) :
    σ ^ 3 * δ ≤ 27 * Cc ^ 3 * Cst * C3 ^ 4 ∧ σ * δ ≤ 3 / 8 := by
  have hL0 : 0 ≤ L := by linarith only [hL1]
  constructor
  · have h1 : σ ^ 3 ≤ (3 * Cc * C3 * L ^ 2) ^ 3 := pow_le_pow_left₀ hσ0 hσle 3
    have h2 := mul_le_mul h1 hδle hδ0 (by positivity)
    have h3 : (3 * Cc * C3 * L ^ 2) ^ 3 * (Cst * (C3 * L) * q) =
        27 * Cc ^ 3 * Cst * C3 ^ 4 * (L ^ 7 * q) := by ring
    have h5 : 0 ≤ 27 * Cc ^ 3 * Cst * C3 ^ 4 := by positivity
    have h6 := mul_le_mul_of_nonneg_left h7 h5
    linarith only [h2, h3, h6]
  · have h1 := mul_le_mul hσle hδle hδ0 (by positivity)
    have hσδ : σ * δ ≤ 3 * (Cc * Cst * C3 ^ 2) * (L ^ 3 * q) := by
      calc σ * δ ≤ 3 * Cc * C3 * L ^ 2 * (Cst * (C3 * L) * q) := h1
        _ = 3 * (Cc * Cst * C3 ^ 2) * (L ^ 3 * q) := by ring
    have hΛ' : 8 * (Cc * Cst * C3 ^ 2) ≤ L := by
      have : 8 * (Cc * Cst * C3 ^ 2) = 8 * Cc * Cst * C3 ^ 2 := by ring
      rw [this]; exact le_trans hΛ hLCp
    have hL3q : 0 ≤ L ^ 3 * q := by positivity
    have h5 : 8 * (Cc * Cst * C3 ^ 2) * (L ^ 3 * q) ≤ L * (L ^ 3 * q) :=
      mul_le_mul_of_nonneg_right hΛ' hL3q
    have h6 : L * (L ^ 3 * q) = L ^ 4 * q := by ring
    nlinarith only [hσδ, h4, h5, h6]

/-- The `n^{-3000}` term against `σ^{-2}`. -/
theorem newMixAsm_w_bound {σ u w n L Chom B8 Cc C3 : ℝ} (hσ0 : 0 ≤ σ) (hw0 : 0 ≤ w) (hu : u * σ ^ 2 = 1)
    (hu0 : 0 ≤ u) (hL1 : 1 ≤ L) (hChom1 : 1 ≤ Chom) (hB8 : 0 ≤ B8)
    (hwdef : w = Chom * n ^ (-(3000 : ℝ)))
    (hσle : σ ≤ 3 * Cc * C3 * L ^ 2)
    (hn3 : n ^ (-(3000 : ℝ)) ≤ B8 * L ^ (-(99 : ℝ)))
    (h99 : L ^ 4 * L ^ (-(99 : ℝ)) ≤ 1) :
    8 * w ≤ u * (72 * Chom * B8 * Cc ^ 2 * C3 ^ 2) := by
  have hL0 : 0 ≤ L := by linarith only [hL1]
  have hp0 : 0 ≤ L ^ (-(99 : ℝ)) := Real.rpow_nonneg hL0 _
  have hσ2 : σ ^ 2 ≤ (3 * Cc * C3 * L ^ 2) ^ 2 := pow_le_pow_left₀ hσ0 hσle 2
  have hChom0 : 0 ≤ Chom := by linarith only [hChom1]
  have h1 : σ ^ 2 * (8 * w) ≤ 72 * Chom * B8 * Cc ^ 2 * C3 ^ 2 := by
    have h2 : 8 * w ≤ 8 * Chom * (B8 * L ^ (-(99 : ℝ))) := by
      rw [hwdef]
      have := mul_le_mul_of_nonneg_left hn3 hChom0
      linarith only [this]
    have h3 : σ ^ 2 * (8 * w) ≤ (3 * Cc * C3 * L ^ 2) ^ 2 * (8 * Chom * (B8 * L ^ (-(99 : ℝ)))) :=
      mul_le_mul hσ2 h2 (by positivity) (by positivity)
    have h4 : (3 * Cc * C3 * L ^ 2) ^ 2 * (8 * Chom * (B8 * L ^ (-(99 : ℝ)))) =
        72 * Chom * B8 * Cc ^ 2 * C3 ^ 2 * (L ^ 4 * L ^ (-(99 : ℝ))) := by ring
    have h5 : 0 ≤ 72 * Chom * B8 * Cc ^ 2 * C3 ^ 2 := by positivity
    have h6 := mul_le_mul_of_nonneg_left h99 h5
    linarith only [h3, h4, h6]
  have h7 := mul_le_mul_of_nonneg_left h1 hu0
  have h8 : u * (σ ^ 2 * (8 * w)) = 8 * w := by
    rw [← mul_assoc, hu, one_mul]
  linarith only [h7, h8]

/-- The final combination of the two homogenization errors and the lower-block comparison. -/
theorem newMixAsm_final_fold {σ s A A' Be Br E R Chom c1 c2 c3 Cref X w δ : ℝ} (hσ : 0 < σ)
    (hs : 0 < s) (hChom1 : 1 ≤ Chom) (hc1 : 1 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hCref : Cref = 40 * Chom * c1 + c2 + 4 * c3) (hX1 : 1 ≤ X)
    (hEdef : E = |s⁻¹ * A - 1| + |s * Be - 1|)
    (hRdef : R = |σ⁻¹ * A' - 1| + |σ * Br - 1|)
    (hE : E ≤ Chom * s ^ (-(2 : ℝ)) * (c1 * X) + w) (hEs : E ≤ 1 / 8)
    (hR : R ≤ Chom * σ ^ (-(2 : ℝ)) * (c1 * X) + w) (hRs : R ≤ 1 / 8)
    (hStar : |Be - Br| ≤ δ) (hδ0 : 0 ≤ δ) (hσδ : σ * δ ≤ 3 / 8) (hσ3δ : σ ^ 3 * δ ≤ c3)
    (hw : 8 * w ≤ σ ^ (-(2 : ℝ)) * c2) :
    |σ⁻¹ * A - 1| + |σ * Be - 1| ≤ Cref * σ ^ (-(2 : ℝ)) * X := by
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hrneg : ∀ x : ℝ, 0 < x → x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
    intro x hx
    rw [Real.rpow_neg hx.le, Real.rpow_two]
  obtain ⟨hT, hσs⟩ := newMixAsm_ratio_algebra (σ := σ) (s := s) (A := A) (B := Be) (B' := Br)
    (e1 := E) (e2 := E) (e3 := R) (δ := δ) hσ hs hE0 hR0 hδ0 (by linarith only [hEs])
    (by linarith only [hEs]) (by linarith only [hRs, hσδ])
    (by rw [hEdef]; exact le_add_of_nonneg_right (abs_nonneg _))
    (by rw [hEdef]; exact le_add_of_nonneg_left (abs_nonneg _))
    (by rw [hRdef]; exact le_add_of_nonneg_left (abs_nonneg _)) hStar
  set u : ℝ := σ ^ (-(2 : ℝ)) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hσ _
  have huσ : u * σ ^ 2 = 1 := by
    rw [hudef, hrneg σ hσ]
    exact inv_mul_cancel₀ (by positivity)
  have hs2 : s ^ (-(2 : ℝ)) ≤ 9 * u := by
    have h1 : σ / 3 ≤ s := by linarith only [hσs]
    have h2 : s ^ (-(2 : ℝ)) ≤ (σ / 3) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    have h3 : (σ / 3) ^ (-(2 : ℝ)) = 9 * u := by
      rw [hrneg (σ / 3) (by positivity), hudef, hrneg σ hσ, div_pow]
      field_simp
      norm_num
    linarith only [h2, h3]
  have hX0 : 0 ≤ X := by linarith only [hX1]
  have hσδ' : 4 * (σ * δ) ≤ u * (4 * c3) := by
    have h1 : σ * δ = u * (σ ^ 3 * δ) := by
      have : u * σ ^ 3 = σ := by
        calc u * σ ^ 3 = (u * σ ^ 2) * σ := by ring
          _ = σ := by rw [huσ, one_mul]
      calc σ * δ = (u * σ ^ 3) * δ := by rw [this]
        _ = u * (σ ^ 3 * δ) := by ring
    rw [h1]
    have := mul_le_mul_of_nonneg_left hσ3δ hu0.le
    linarith only [this]
  have hE' : E ≤ 9 * (Chom * u * (c1 * X)) + w := by
    have h1 : Chom * s ^ (-(2 : ℝ)) * (c1 * X) ≤ Chom * (9 * u) * (c1 * X) := by
      have hcx : 0 ≤ c1 * X := mul_nonneg (by linarith only [hc1]) hX0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs2 (by linarith only [hChom1])) hcx
    have h2 : Chom * (9 * u) * (c1 * X) = 9 * (Chom * u * (c1 * X)) := by ring
    linarith only [hE, h1, h2]
  have hcu : Cref * u * X = 40 * (Chom * u * (c1 * X)) + c2 * u * X + 4 * c3 * u * X := by
    rw [hCref]; ring
  have h2u : u * c2 ≤ c2 * u * X := by
    have : u * c2 * 1 ≤ u * c2 * X := mul_le_mul_of_nonneg_left hX1 (mul_nonneg hu0.le hc2)
    nlinarith only [this]
  have h4u : u * (4 * c3) ≤ 4 * c3 * u * X := by
    have : u * (4 * c3) * 1 ≤ u * (4 * c3) * X :=
      mul_le_mul_of_nonneg_left hX1 (mul_nonneg hu0.le (by positivity))
    nlinarith only [this]
  linarith only [hT, hE', hR, hw, hσδ', hcu, h2u, h4u]

end
end SuperdiffusionCLT.Section4.NewMixing
