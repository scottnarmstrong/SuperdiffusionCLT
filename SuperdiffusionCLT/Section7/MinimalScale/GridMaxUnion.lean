/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxBad

/-!
# The random scale over all `K`, and its tail

`scaleBadSup` is the supremum over `K ≥ K₀` of `3^{n_K+1}` on the bad event `badK K`, valued in
`ℝ≥0∞`.  Its upper tail beyond `3^k` is controlled by the summable bounds of `GridMaxBad`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

open scoped Classical in
/-- The random scale `sup_{K ≥ K₀} 3^{n_K + 1} 1_{bad K}`, in `ℝ≥0∞`. -/
def scaleBadSup (d : ℕ) (N : ℝ) (K0 : ℕ) (X0 : Vec d → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ K : ℕ, if K0 ≤ K ∧ ω ∈ badK d N X0 K then (3 : ℝ≥0∞) ^ (nK N K + 1) else 0

theorem measurable_scaleBadSup (N : ℝ) (K0 : ℕ) {X0 : Vec d → Ω → ℝ}
    (hX0 : ∀ y, Measurable (X0 y)) : Measurable (scaleBadSup d N K0 X0) := by
  refine Measurable.iSup fun K => ?_
  have hS : MeasurableSet {ω | K0 ≤ K ∧ ω ∈ badK d N X0 K} := by
    by_cases hK : K0 ≤ K
    · simpa [hK] using measurableSet_badK N hX0 K
    · simp [hK]
  exact Measurable.ite hS measurable_const measurable_const

omit [MeasurableSpace Ω] in
theorem le_scaleBadSup {N : ℝ} {K0 : ℕ} {X0 : Vec d → Ω → ℝ} {K : ℕ} {ω : Ω} (hK : K0 ≤ K)
    (hω : ω ∈ badK d N X0 K) : (3 : ℝ≥0∞) ^ (nK N K + 1) ≤ scaleBadSup d N K0 X0 ω := by
  refine le_iSup_of_le K ?_
  simp [hK, hω]

omit [MeasurableSpace Ω] in
theorem lt_scaleBadSup {N : ℝ} {K0 k : ℕ} {X0 : Vec d → Ω → ℝ} {ω : Ω}
    (h : (3 : ℝ≥0∞) ^ k < scaleBadSup d N K0 X0 ω) :
    ∃ K, K0 ≤ K ∧ k ≤ K ∧ ω ∈ badK d N X0 K := by
  obtain ⟨K, hK⟩ := lt_iSup_iff.1 h
  by_cases hc : K0 ≤ K ∧ ω ∈ badK d N X0 K
  · refine ⟨K, hc.1, ?_, hc.2⟩
    simp only [hc, and_self, ↓reduceIte] at hK
    have : k < nK N K + 1 := by
      by_contra hle
      push Not at hle
      have : (3 : ℝ≥0∞) ^ (nK N K + 1) ≤ (3 : ℝ≥0∞) ^ k :=
        pow_le_pow_right₀ (by norm_num) hle
      exact absurd hK (not_lt.2 this)
    exact (Nat.lt_succ_iff.1 this).trans (nK_le N K)
  · simp only [hc, ↓reduceIte] at hK
    exact absurd hK (by simp)

/-- The union of the bad events from `m` on. -/
def badFrom (d : ℕ) (N : ℝ) (X0 : Vec d → Ω → ℝ) (m : ℕ) : Set Ω :=
  ⋃ K : ℕ, if m ≤ K then badK d N X0 K else ∅

omit [MeasurableSpace Ω] in
theorem scaleBadSup_gt_subset {N : ℝ} {K0 k : ℕ} {X0 : Vec d → Ω → ℝ} :
    {ω | (3 : ℝ≥0∞) ^ k < scaleBadSup d N K0 X0 ω} ⊆ badFrom d N X0 (max K0 k) := by
  intro ω hω
  obtain ⟨K, h1, h2, h3⟩ := lt_scaleBadSup hω
  refine Set.mem_iUnion.2 ⟨K, ?_⟩
  have hmk : max K0 k ≤ K := max_le h1 h2
  simp only [hmk, ↓reduceIte]
  exact h3

/-- **Tail of the union of bad events.** -/
theorem measureReal_badFrom_le (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℝ} (hN : 0 ≤ N)
    {σ A : ℝ} (hσ : 0 < σ) {X0 : Vec d → Ω → ℝ} (hX0 : ∀ y, Measurable (X0 y))
    (hA : 1 ≤ A)
    (hO : ∀ y, Homogenization.IndependentSums.IsBigO μ
      (Homogenization.IndependentSums.gammaSigma σ) (fun ω => Real.log (X0 y ω)) A)
    {C₂ : ℝ} (hC₂ : 0 ≤ C₂)
    (hterm : ∀ (a : ℝ), 0 < a → ∀ K : ℕ, 1 ≤ K →
      (K : ℝ) ^ ((d : ℝ) * (N * Real.log 3)) * Real.exp (-((a * K) ^ σ)) ≤
        C₂ * a ^ (-((d : ℝ) * (N * Real.log 3) + 2)) * ((K : ℝ) ^ 2)⁻¹ *
          Real.exp (-((a * K) ^ σ / 2))) :
    ∀ m : ℕ, 1 ≤ m → (4 * N + 2) ^ 2 ≤ (m : ℝ) → 2 * A ≤ m →
      μ.real (badFrom d N X0 m) ≤
        2 * ((1500 : ℝ) ^ d * C₂ * (Real.log 3 / (2 * A)) ^ (-((d : ℝ) * (N * Real.log 3) + 2))) *
          Real.exp (-((Real.log 3 / (2 * A) * m) ^ σ / 2)) := by
  have hbad := measureReal_badK_le_summable μ hN hσ hA hO hterm
  intro m hm hm1 hm2
  set a := Real.log 3 / (2 * A) with hadef
  have hA0 : 0 < A := by linarith only [hA]
  have hlog3 : 1 < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have ha : 0 < a := by positivity
  set D := (1500 : ℝ) ^ d * C₂ * a ^ (-((d : ℝ) * (N * Real.log 3) + 2)) with hD
  have hD0 : 0 ≤ D := by positivity
  set g : ℕ → ℝ := fun K => if m ≤ K then D * ((K : ℝ) ^ 2)⁻¹ * Real.exp (-((a * m) ^ σ / 2))
    else 0 with hg
  have hmeas : ∀ K, MeasurableSet (if m ≤ K then badK d N X0 K else (∅ : Set Ω)) := by
    intro K
    split_ifs
    · exact measurableSet_badK N hX0 K
    · exact MeasurableSet.empty
  have hterm : ∀ K : ℕ, μ.real (if m ≤ K then badK d N X0 K else (∅ : Set Ω)) ≤ g K := by
    intro K
    by_cases hmK : m ≤ K
    · simp only [hmK, ↓reduceIte, hg]
      have hKm : (m : ℝ) ≤ K := by exact_mod_cast hmK
      have := hbad K (hm1.trans hKm) (hm2.trans hKm)
      refine this.trans ?_
      have hexp : Real.exp (-((a * K) ^ σ / 2)) ≤ Real.exp (-((a * m) ^ σ / 2)) := by
        refine Real.exp_le_exp.2 ?_
        have : (a * m) ^ σ ≤ (a * K) ^ σ :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hKm ha.le) hσ.le
        linarith only [this]
      calc _ = D * ((K : ℝ) ^ 2)⁻¹ * Real.exp (-((a * K) ^ σ / 2)) := by rw [hD]
        _ ≤ _ := by gcongr
    · simp [hmK, g]
  have hsum : ∑' K : ℕ, μ (if m ≤ K then badK d N X0 K else (∅ : Set Ω)) ≤
      ENNReal.ofReal (2 * D * Real.exp (-((a * m) ^ σ / 2))) := by
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    have h1 : ∀ K, μ (if m ≤ K then badK d N X0 K else (∅ : Set Ω)) ≤ ENNReal.ofReal (g K) := by
      intro K
      rw [← ofReal_measureReal (μ := μ) (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (hterm K)
    calc ∑ K ∈ Finset.range n, μ (if m ≤ K then badK d N X0 K else (∅ : Set Ω))
        ≤ ∑ K ∈ Finset.range n, ENNReal.ofReal (g K) := Finset.sum_le_sum fun K _ => h1 K
      _ = ENNReal.ofReal (∑ K ∈ Finset.range n, g K) :=
          (ENNReal.ofReal_sum_of_nonneg fun K _ => by
            simp only [hg]; split_ifs <;> positivity).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          exact sum_tail_le σ D a m n hm hD0
  have hU : μ (badFrom d N X0 m) ≤ ENNReal.ofReal (2 * D * Real.exp (-((a * m) ^ σ / 2))) :=
    (measure_iUnion_le _).trans hsum
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hU
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  simpa [Measure.real, hD] using this

end

end SuperdiffusionCLT.Section7
