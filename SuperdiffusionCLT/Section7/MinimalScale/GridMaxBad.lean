/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxCount
public import SuperdiffusionCLT.Section7.MinimalScale.StretchedSum
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The bad events at scale `K` and their union bound

`badK` is the event that some translate `X0 y`, `y` on the scale-`K` grid, exceeds `3^{n_K}`.
Its probability is at most `1500^d K^b` times the pointwise tail `exp(-(c n_K)^σ)`; this is then
bounded by a summable quantity `D K^{-2} exp(-(aK)^σ / 2)` with `a = log 3 / (2A)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The scale-`K` bad event. -/
def badK (d : ℕ) (N : ℝ) (X0 : Vec d → Ω → ℝ) (K : ℕ) : Set Ω :=
  {ω | ∃ y ∈ gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)), (3 : ℝ) ^ (nK N K) < X0 y ω}

theorem measurableSet_badK (N : ℝ) {X0 : Vec d → Ω → ℝ} (hX0 : ∀ y, Measurable (X0 y)) (K : ℕ) :
    MeasurableSet (badK d N X0 K) := by
  have : badK d N X0 K =
      ⋃ y ∈ gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)),
        {ω | (3 : ℝ) ^ (nK N K) < X0 y ω} := by
    ext ω; simp [badK]
  rw [this]
  exact Finset.measurableSet_biUnion _ fun y _ => measurableSet_lt measurable_const (hX0 y)

omit [MeasurableSpace Ω] in
/-- Off the bad event the grid maximum is at most `3^{n_K}`. -/
theorem X0max_le_of_not_mem_badK {N : ℝ} {X0 : Vec d → Ω → ℝ} {K : ℕ} {ω : Ω}
    (h : ω ∉ badK d N X0 K) :
    X0max (fun y => X0 y ω) ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)) ≤ (3 : ℝ) ^ (nK N K) := by
  rw [X0max_le_iff _ _ (by positivity)]
  intro y hy
  by_contra hlt
  exact h ⟨y, hy, not_le.1 hlt⟩

/-- **Union bound at scale `K`.** -/
theorem measureReal_badK_le (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℝ} (hN : 0 ≤ N)
    {σ A : ℝ} {X0 : Vec d → Ω → ℝ} (hA : 0 < A)
    (hO : ∀ y, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (fun ω => Real.log (X0 y ω)) A)
    {K : ℕ} (hK : (4 * N + 2) ^ 2 ≤ (K : ℝ))
    (ht : 1 ≤ Real.log 3 / A * (nK N K : ℝ)) :
    μ.real (badK d N X0 K) ≤
      (1500 : ℝ) ^ d * (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) *
        Real.exp (-((Real.log 3 / A * (nK N K : ℝ)) ^ σ)) := by
  set t := Real.log 3 / A * (nK N K : ℝ) with htdef
  have hsub : badK d N X0 K ⊆
      ⋃ y ∈ gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)),
        Homogenization.IndependentSums.absTailEvent (fun ω => Real.log (X0 y ω)) (A * t) := by
    intro ω ⟨y, hy, hlt⟩
    refine Set.mem_iUnion₂.2 ⟨y, hy, ?_⟩
    rw [Homogenization.IndependentSums.mem_absTailEvent]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (nK N K) := by positivity
    have hlog : Real.log ((3 : ℝ) ^ (nK N K)) < Real.log (X0 y ω) := Real.log_lt_log h3 hlt
    rw [Real.log_pow] at hlog
    have : A * t = (nK N K : ℝ) * Real.log 3 := by
      rw [htdef]; field_simp
    rw [this]
    exact lt_of_lt_of_le hlog (le_abs_self _)
  have hcard := card_grid_le_poly d hN hK
  calc μ.real (badK d N X0 K)
      ≤ μ.real (⋃ y ∈ gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)),
          Homogenization.IndependentSums.absTailEvent (fun ω => Real.log (X0 y ω)) (A * t)) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ y ∈ gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)),
          μ.real (Homogenization.IndependentSums.absTailEvent
            (fun ω => Real.log (X0 y ω)) (A * t)) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2)), Real.exp (-(t ^ σ)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        exact (Homogenization.IndependentSums.isBigO_gammaSigma_iff.1 (hO y)) ht
    _ = ((gridPts d ((nK N K : ℤ) - 3) ((3 : ℝ) ^ (K + 2))).card : ℝ) * Real.exp (-(t ^ σ)) := by
        simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le

/-- **The summable bound.** With `a = log 3 / (2A)`, for `K ≥ 2A` and `K ≥ (4N+2)^2`. -/
theorem measureReal_badK_le_summable (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℝ}
    (hN : 0 ≤ N) {σ A : ℝ} (hσ : 0 < σ) {X0 : Vec d → Ω → ℝ}
    (hA : 1 ≤ A)
    (hO : ∀ y, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (fun ω => Real.log (X0 y ω)) A)
    {C₂ : ℝ}
    (hterm : ∀ (a : ℝ), 0 < a → ∀ K : ℕ, 1 ≤ K →
      (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) * Real.exp (-((a * K) ^ σ)) ≤
        C₂ * a ^ (-((d : ℝ) * (N * Real.log 3) + 2)) * ((K : ℝ) ^ 2)⁻¹ *
          Real.exp (-((a * K) ^ σ / 2))) :
    ∀ K : ℕ, (4 * N + 2) ^ 2 ≤ (K : ℝ) → 2 * A ≤ K →
      μ.real (badK d N X0 K) ≤
        (1500 : ℝ) ^ d * C₂ * (Real.log 3 / (2 * A)) ^ (-((d : ℝ) * (N * Real.log 3) + 2)) *
          ((K : ℝ) ^ 2)⁻¹ * Real.exp (-((Real.log 3 / (2 * A) * K) ^ σ / 2)) := by
  intro K hK hK2
  have hA0 : 0 < A := by linarith only [hA]
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  set a := Real.log 3 / (2 * A) with hadef
  have ha : 0 < a := by positivity
  have hK1 : (1 : ℝ) ≤ K := by nlinarith only [sq_nonneg N, hK, hN]
  have hKnat : 1 ≤ K := by exact_mod_cast hK1
  have hnk := nK_ge_half hN hK
  have hc : a * K ≤ Real.log 3 / A * (nK N K : ℝ) := by
    have : Real.log 3 / A * (nK N K : ℝ) ≥ Real.log 3 / A * ((K : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hnk (by positivity)
    have e : a * K = Real.log 3 / A * ((K : ℝ) / 2) := by rw [hadef]; field_simp
    linarith only [this, e]
  have h1 : 1 ≤ a * K := by
    rw [hadef, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : 2 * A ≤ K := hK2
    nlinarith only [hlog3, this, hA0]
  have ht : 1 ≤ Real.log 3 / A * (nK N K : ℝ) := h1.trans hc
  have hbad := measureReal_badK_le μ hN hA0 hO hK ht
  have hmono : Real.exp (-((Real.log 3 / A * (nK N K : ℝ)) ^ σ)) ≤
      Real.exp (-((a * K) ^ σ)) := by
    refine Real.exp_le_exp.2 ?_
    have := Real.rpow_le_rpow (by positivity) hc hσ.le
    linarith only [this]
  have hT := hterm a ha K hKnat
  calc μ.real (badK d N X0 K)
      ≤ (1500 : ℝ) ^ d * (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) *
          Real.exp (-((Real.log 3 / A * (nK N K : ℝ)) ^ σ)) := hbad
    _ ≤ (1500 : ℝ) ^ d * (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) *
          Real.exp (-((a * K) ^ σ)) := by gcongr
    _ = (1500 : ℝ) ^ d * ((K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) *
          Real.exp (-((a * K) ^ σ))) := by ring
    _ ≤ (1500 : ℝ) ^ d * (C₂ * a ^ (-((d : ℝ) * (N * Real.log 3) + 2)) * ((K : ℝ) ^ 2)⁻¹ *
          Real.exp (-((a * K) ^ σ / 2))) := by gcongr
    _ = _ := by ring

end

end SuperdiffusionCLT.Section7
