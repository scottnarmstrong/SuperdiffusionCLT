/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real


/-!
# The `t ≤ 1/2` threshold for the annealed-comparison amplitude

`mixFin_annealedComparison` (`AnnealedFinal.lean`) bounds the difference of the `L`- and
`ell`-annealed bilinear forms at the amplitude
`g2 * (Cg * (L-ell)^(1/2) * σ^(-1)) + g1 * (Cg * (L-ell) * σ^(-2)) + g3 * (g4 * (2 * (Cg * m^(-5000))))`,
where `σ = sigmaBarStarScalar nu L P (cubeSet (originCube d n))` and `Cg ≥ 1` is the *fixed*
amplitude coefficient of the two witnesses it consumes.

`mixBase_amplitude_le_half` shows this is at most `1/2`, with the order of quantifiers
`∃ C₀, ∀ C ≥ C₀`: the coefficient `Cg` and the four moment constants are fixed first, and the
smallness comes only from the outer small-gap constant `C` through
`(L - n) ≤ C⁻¹ σ²` and `σ ≤ B ν⁻¹ L`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

/-- Auxiliary: `sqrt u / σ ≤ 1 / sqrt C` from `C * u ≤ σ²`. -/
private theorem mixBaseW_sqrt_div_le {C u σ : ℝ} (hC : 0 < C) (hσ : 0 < σ)
    (h : C * u ≤ σ ^ 2) : Real.sqrt u * σ⁻¹ ≤ (Real.sqrt C)⁻¹ := by
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.2 hC
  have h1 : Real.sqrt C * Real.sqrt u ≤ σ := by
    rw [← Real.sqrt_mul hC.le]
    calc Real.sqrt (C * u) ≤ Real.sqrt (σ ^ 2) := Real.sqrt_le_sqrt h
      _ = σ := Real.sqrt_sq hσ.le
  rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ hσ hsC]
  nlinarith only [h1, Real.sqrt_nonneg u]

/-- The threshold. The hypotheses on `(C, ν, σ, L, n, ell, m)` are exactly the ones available at
the `hBase` call site: the small gap `L - n ≤ C⁻¹ σ²`, the envelope bound `σ ≤ B ν⁻¹ L`, and the
lower margin `10 K₀ log (ν⁻¹ L) ≤ m - n`. -/
theorem mixBase_amplitude_le_half {a1 a2 a3 a4 Cg B K0 : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (ha3 : 0 ≤ a3) (ha4 : 0 ≤ a4) (hCg : 1 ≤ Cg) (hB : 1 ≤ B) (hK0 : 1 ≤ K0) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C → ∀ (nu σ : ℝ), 0 < nu → nu ≤ 1 → 0 < σ →
      ∀ L n ell m : ℕ, 1 ≤ n → n ≤ ell → ell < L → n ≤ m →
        σ ≤ B * (nu⁻¹ * (L : ℝ)) →
        (L : ℝ) - (n : ℝ) ≤ C⁻¹ * σ ^ 2 →
        10 * K0 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((m - n : ℕ) : ℝ) →
        a1 * (Cg * (((L - ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) +
            a2 * (Cg * ((L - ell : ℕ) : ℝ) * σ ^ (-(2 : ℝ))) +
            a3 * (a4 * (2 * (Cg * (m : ℝ) ^ (-(5000 : ℝ))))) ≤ 1 / 2 := by
  set T : ℝ := 6 * (a3 * (a4 * (2 * Cg))) with hT
  have hT0 : 0 ≤ T := by positivity
  set R : ℝ := max (max 1 (6 * (a1 + a2) * Cg)) (B * Real.exp (T / 10)) with hR
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR2 : 6 * (a1 + a2) * Cg ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR3 : B * Real.exp (T / 10) ≤ R := le_max_right _ _
  refine ⟨R ^ 2, by nlinarith only [hR1], ?_⟩
  intro C hCR nu σ hnu hnu1 hσ L n ell m hn hnell hellL hnm hσB hgap hmargin
  have hC1 : 1 ≤ C := le_trans (by nlinarith only [hR1]) hCR
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC1
  have hsR : R ≤ Real.sqrt C := by
    rw [show R = Real.sqrt (R ^ 2) from (Real.sqrt_sq (by linarith only [hR1])).symm]
    exact Real.sqrt_le_sqrt hCR
  set s : ℝ := Real.sqrt C with hs
  have hs1 : 1 ≤ s := le_trans hR1 hsR
  have hs0 : 0 < s := by linarith only [hs1]
  have hss : s ^ 2 = C := Real.sq_sqrt hC0.le
  -- the gap in the reals
  have hu1 : (1 : ℝ) ≤ ((L - ell : ℕ) : ℝ) := by
    have : 1 ≤ L - ell := by omega
    exact_mod_cast this
  have hule : ((L - ell : ℕ) : ℝ) ≤ (L : ℝ) - (n : ℝ) := by
    have hnat : L - ell ≤ L - n := by omega
    have hcast : ((L - n : ℕ) : ℝ) = (L : ℝ) - (n : ℝ) := by
      rw [Nat.cast_sub (by omega)]
    rw [← hcast]
    exact_mod_cast hnat
  have hCu : C * ((L - ell : ℕ) : ℝ) ≤ σ ^ 2 := by
    have h1 : ((L - ell : ℕ) : ℝ) ≤ C⁻¹ * σ ^ 2 := le_trans hule hgap
    calc C * ((L - ell : ℕ) : ℝ) ≤ C * (C⁻¹ * σ ^ 2) := mul_le_mul_of_nonneg_left h1 hC0.le
      _ = σ ^ 2 := by field_simp
  set u : ℝ := ((L - ell : ℕ) : ℝ) with hu
  have hu0 : 0 ≤ u := by linarith only [hu1]
  -- term 1
  have hsq1 : u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)) ≤ s⁻¹ := by
    rw [← Real.sqrt_eq_rpow, Real.rpow_neg_one]
    exact mixBaseW_sqrt_div_le hC0 hσ hCu
  -- term 2
  have hsq2 : u * σ ^ (-(2 : ℝ)) ≤ s⁻¹ := by
    have h2 : σ ^ (-(2 : ℝ)) = (σ ^ 2)⁻¹ := by
      rw [Real.rpow_neg hσ.le]; norm_cast
    have hu' : u ≤ C⁻¹ * σ ^ 2 := le_trans hule hgap
    have hsC : s ≤ C := by nlinarith only [hs1, hss]
    rw [h2, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    calc u ≤ C⁻¹ * σ ^ 2 := hu'
      _ ≤ s⁻¹ * σ ^ 2 :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hs0 hsC) (by positivity)
  -- bound the first two terms
  have hCg0 : 0 < Cg := lt_of_lt_of_le one_pos hCg
  have hA : a1 * (Cg * u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) ≤ a1 * Cg * s⁻¹ := by
    calc a1 * (Cg * u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ)))
        = a1 * Cg * (u ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) := by ring
      _ ≤ a1 * Cg * s⁻¹ := mul_le_mul_of_nonneg_left hsq1 (by positivity)
  have hA2 : a2 * (Cg * u * σ ^ (-(2 : ℝ))) ≤ a2 * Cg * s⁻¹ := by
    calc a2 * (Cg * u * σ ^ (-(2 : ℝ))) = a2 * Cg * (u * σ ^ (-(2 : ℝ))) := by ring
      _ ≤ a2 * Cg * s⁻¹ := mul_le_mul_of_nonneg_left hsq2 (by positivity)
  have hsum12 : a1 * Cg * s⁻¹ + a2 * Cg * s⁻¹ ≤ 1 / 3 := by
    have hk : (a1 + a2) * Cg * s⁻¹ ≤ 1 / 6 := by
      rw [inv_eq_one_div, mul_one_div, div_le_div_iff₀ hs0 (by norm_num)]
      nlinarith only [hR2, hsR]
    nlinarith only [hk]
  -- term 3
  have hsB : s / B ≤ nu⁻¹ * (L : ℝ) := by
    have hσs : s ≤ σ := by
      have hLn : (1 : ℝ) ≤ (L : ℝ) - (n : ℝ) := by
        have : (n : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ L)
        linarith only [this]
      have h1 : C ≤ σ ^ 2 := by
        have : C * 1 ≤ C * ((L : ℝ) - (n : ℝ)) := mul_le_mul_of_nonneg_left hLn hC0.le
        have h2 : C * ((L : ℝ) - (n : ℝ)) ≤ σ ^ 2 := by
          calc C * ((L : ℝ) - (n : ℝ)) ≤ C * (C⁻¹ * σ ^ 2) :=
                mul_le_mul_of_nonneg_left hgap hC0.le
            _ = σ ^ 2 := by field_simp
        linarith only [this, h2]
      rw [hs]
      calc Real.sqrt C ≤ Real.sqrt (σ ^ 2) := Real.sqrt_le_sqrt h1
        _ = σ := Real.sqrt_sq hσ.le
    rw [div_le_iff₀ (by linarith only [hB])]
    linarith only [hσs, hσB, mul_comm B (nu⁻¹ * (L : ℝ))]
  have hexp : Real.exp (T / 10) ≤ nu⁻¹ * (L : ℝ) := by
    have hBpos : 0 < B := by linarith only [hB]
    have h1 : B * Real.exp (T / 10) ≤ s := le_trans hR3 hsR
    have h2 : Real.exp (T / 10) ≤ s / B := by
      rw [le_div_iff₀ hBpos]; linarith only [h1, mul_comm B (Real.exp (T / 10))]
    exact h2.trans hsB
  have hlog : T / 10 ≤ Real.log (nu⁻¹ * (L : ℝ)) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hexp)).2 hexp
  have hlog0 : 0 ≤ Real.log (nu⁻¹ * (L : ℝ)) := le_trans (by positivity) hlog
  have hmT : T ≤ (m : ℝ) := by
    have h1 : ((m - n : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m n
    nlinarith only [hmargin, h1, hlog, hK0, hlog0, mul_nonneg (sub_nonneg.2 hK0) hlog0]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_trans hn hnm
  have hmpow : (m : ℝ) ^ (-(5000 : ℝ)) ≤ (m : ℝ)⁻¹ := by
    have := Real.rpow_le_rpow_of_exponent_le hm1 (show (-(5000 : ℝ)) ≤ -1 by norm_num)
    rwa [Real.rpow_neg_one] at this
  have hm0 : 0 < (m : ℝ) := by linarith only [hm1]
  have hA3 : a3 * (a4 * (2 * (Cg * (m : ℝ) ^ (-(5000 : ℝ))))) ≤ 1 / 6 := by
    have h1 : a3 * (a4 * (2 * (Cg * (m : ℝ) ^ (-(5000 : ℝ))))) ≤
        a3 * (a4 * (2 * (Cg * (m : ℝ)⁻¹))) := by
      gcongr
    have h2 : a3 * (a4 * (2 * (Cg * (m : ℝ)⁻¹))) = (T / 6) * (m : ℝ)⁻¹ := by
      rw [hT]; ring
    have h3 : (T / 6) * (m : ℝ)⁻¹ ≤ 1 / 6 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hm0]
      linarith only [hmT]
    linarith only [h1, h2, h3]
  linarith only [hA, hA2, hsum12, hA3]

/-- Satisfiability: for every `C ≥ C₀` the hypotheses of `mixBase_amplitude_le_half` are met by
actual data (`ν = 1`, `σ = √C`, `n = ell = L - 1`, `L = ⌈√C⌉ + 1`, `m = n + ⌈10 log L⌉`), at
unit constants `a₁ = a₂ = a₃ = a₄ = Cg = B = K₀ = 1`; the conclusion is then a genuine bound. -/
example : ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C → ∃ (nu σ : ℝ) (L n ell m : ℕ),
    0 < nu ∧ nu ≤ 1 ∧ 0 < σ ∧ 1 ≤ n ∧ n ≤ ell ∧ ell < L ∧ n ≤ m ∧
      σ ≤ 1 * (nu⁻¹ * (L : ℝ)) ∧ (L : ℝ) - (n : ℝ) ≤ C⁻¹ * σ ^ 2 ∧
      10 * 1 * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((m - n : ℕ) : ℝ) ∧
      1 * (1 * (((L - ell : ℕ) : ℝ)) ^ ((1 : ℝ) / 2) * σ ^ (-(1 : ℝ))) +
            1 * (1 * ((L - ell : ℕ) : ℝ) * σ ^ (-(2 : ℝ))) +
            1 * (1 * (2 * (1 * (m : ℝ) ^ (-(5000 : ℝ))))) ≤ 1 / 2 := by
  obtain ⟨C0, hC01, hC0⟩ := mixBase_amplitude_le_half (a1 := 1) (a2 := 1) (a3 := 1) (a4 := 1)
    (Cg := 1) (B := 1) (K0 := 1) zero_le_one zero_le_one zero_le_one zero_le_one le_rfl le_rfl
    le_rfl
  refine ⟨C0, hC01, fun C hC => ?_⟩
  have hC1 : 1 ≤ C := le_trans hC01 hC
  have hC0pos : 0 < C := lt_of_lt_of_le one_pos hC1
  have hs1 : 1 ≤ Real.sqrt C := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hC1
  have hs0 : 0 < Real.sqrt C := by linarith only [hs1]
  have hceil1 : 1 ≤ ⌈Real.sqrt C⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hs0).ne'
  set L : ℕ := ⌈Real.sqrt C⌉₊ + 1 with hL
  have hL2 : 2 ≤ L := by omega
  have hLR : Real.sqrt C ≤ (L : ℝ) := by
    have := Nat.le_ceil (Real.sqrt C)
    rw [hL]; push_cast; linarith only [this]
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  set m : ℕ := (L - 1) + ⌈10 * Real.log (1⁻¹ * (L : ℝ))⌉₊ with hm
  have hmn : m - (L - 1) = ⌈10 * Real.log (1⁻¹ * (L : ℝ))⌉₊ := by omega
  have hLsub : (((L - 1 : ℕ) : ℝ)) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  refine ⟨1, Real.sqrt C, L, L - 1, L - 1, m, one_pos, le_rfl, hs0, by omega, le_rfl,
    by omega, by omega, ?_, ?_, ?_, ?_⟩
  · simpa using hLR
  · rw [hLsub, Real.sq_sqrt hC0pos.le, inv_mul_cancel₀ hC0pos.ne']; linarith only
  · rw [hmn, mul_one]; exact Nat.le_ceil _
  · exact hC0 C hC 1 (Real.sqrt C) one_pos le_rfl hs0 L (L - 1) (L - 1) m (by omega) le_rfl
      (by omega) (by omega) (by simpa using hLR)
      (by rw [hLsub, Real.sq_sqrt hC0pos.le, inv_mul_cancel₀ hC0pos.ne']; linarith only)
      (by rw [hmn, mul_one]; exact Nat.le_ceil _)

end SuperdiffusionCLT.Section4.Mixing
