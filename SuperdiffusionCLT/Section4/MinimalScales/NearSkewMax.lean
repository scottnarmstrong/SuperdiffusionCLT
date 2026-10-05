/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.GammaCenteredMax
public import Homogenization.Book.Ch04.Theorems.Concentration
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Maximal bound for partial sums of independent centered `Γ₂` increments

For independent mean-zero `Γ₂(c)` summands `X r` and a window `(m, m + h]`, the
maximum over `q ≤ m + h` of `|∑_{r ∈ (m, q]} X r|` is at most
`C √h c (log (2h))^{1/2}` plus a nonnegative variable that is `O_{Γ₂}(C √h c)`.
The maximal estimate is obtained from the centered finite maximum
(`gammaSigma_centered_Icc`) applied to the `h` fixed-`q` partial sums, which carry
the concentration bound `isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.IndependentSums

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A `Γ_σ` scale on a probability space is nonnegative. -/
theorem srootNS_isBigO_scale_nonneg {μ : Measure Ω} [IsProbabilityMeasure μ] {σ : ℝ}
    {X : Ω → ℝ} {A : ℝ} (h : IsBigO μ (gammaSigma σ) X A) : 0 ≤ A := by
  by_contra hneg
  replace hneg := not_le.1 hneg
  have h1 : μ.real (upperTailEvent (fun ω => |X ω|) (A * 1)) ≤ (gammaSigma σ 1)⁻¹ :=
    h (t := 1) le_rfl
  have hset : upperTailEvent (fun ω => |X ω|) (A * 1) = Set.univ := by
    ext ω
    simp only [mem_upperTailEvent, Set.mem_univ, iff_true]
    linarith only [hneg, abs_nonneg (X ω)]
  rw [hset] at h1
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, gammaSigma_apply,
    Real.one_rpow] at h1
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith only [this]
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2 : 1 ≤ (Real.exp 1)⁻¹ := h1
  rw [le_inv_comm₀ (by norm_num) hpos] at h2
  simp only [inv_one] at h2
  linarith only [h2, he]

/-- **Maximal form.** Independent, mean-zero, `O_{Γ₂}(c)` increments `X r` on the
window `(m, m + h]`: the running sums satisfy a uniform bound with a centering term
`C √h c (log 2h)^{1/2}` and a nonnegative remainder `O_{Γ₂}(C √h c)`. The constant
`C = gammaSigmaIndependentSumConst 2` is also returned nonnegative. -/
theorem srootNS_walk_tail_max {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 < c)
    (hind : iIndepFun X μ) (hmeas : ∀ r, Measurable (X r))
    (m h : ℕ) (hh : 1 ≤ h)
    (hX : ∀ r, m < r → r ≤ m + h → IsBigO μ (gammaSigma 2) (X r) c)
    (hmean : ∀ r, ∫ ω, X r ω ∂μ = 0) :
    0 ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 ∧
    ∃ Y : Ω → ℝ, Measurable Y ∧ (∀ ω, 0 ≤ Y ω) ∧
      IsBigO μ (gammaSigma 2) Y
        (Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) * c) ∧
      ∀ ω, ∀ q, q ≤ m + h → |∑ r ∈ Finset.Ioc m q, X r ω| ≤
        Book.Ch04.gammaSigmaIndependentSumConst 2 * Real.sqrt (h : ℝ) * c *
          Real.log (2 * (h : ℝ)) ^ ((2 : ℝ)⁻¹) + Y ω := by
  set C0 : ℝ := Book.Ch04.gammaSigmaIndependentSumConst 2 with hC0
  have hsum : ∀ q, m < q → q ≤ m + h →
      IsBigO μ (gammaSigma 2) (fun ω => |∑ r ∈ Finset.Ioc m q, X r ω|)
        (C0 * Real.sqrt ((q - m : ℕ) : ℝ) * c) := by
    intro q hmq hqh
    have hne : (Finset.Ioc m q).Nonempty := ⟨q, Finset.mem_Ioc.2 ⟨hmq, le_rfl⟩⟩
    have hs := Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := μ) (X := X) (s := Finset.Ioc m q) (σ := 2) (K := c) hind hmeas hne
      (by norm_num) (by norm_num) hc
      (fun r hr => hX r (Finset.mem_Ioc.1 hr).1 ((Finset.mem_Ioc.1 hr).2.trans hqh))
      (fun r _ => hmean r)
    rw [Nat.card_Ioc] at hs
    exact hs.of_abs_le (fun ω => by rw [abs_abs])
  have hC0nn : 0 ≤ C0 := by
    have h1 := hsum (m + 1) (Nat.lt_succ_self m) (by omega)
    have h2 := srootNS_isBigO_scale_nonneg h1
    have h3 : ((m + 1 - m : ℕ) : ℝ) = 1 := by
      rw [show m + 1 - m = 1 by omega]; norm_num
    rw [h3, Real.sqrt_one, mul_one] at h2
    by_contra hneg
    replace hneg := not_le.1 hneg
    have : C0 * c < 0 := mul_neg_of_neg_of_pos hneg hc
    linarith only [h2, this]
  refine ⟨hC0nn, ?_⟩
  set Kc : ℝ := C0 * Real.sqrt (h : ℝ) * c with hKc
  have hKcnn : 0 ≤ Kc := by positivity
  have hmeasQ : ∀ q ∈ Finset.Icc (m + 1) (m + h),
      Measurable (fun ω => |∑ r ∈ Finset.Ioc m q, X r ω|) := fun q _ =>
    (Finset.measurable_sum _ fun r _ => hmeas r).abs
  have hbigQ : ∀ q ∈ Finset.Icc (m + 1) (m + h),
      IsBigO μ (gammaSigma 2) (fun ω => |∑ r ∈ Finset.Ioc m q, X r ω|) Kc := by
    intro q hq
    have hq' := Finset.mem_Icc.1 hq
    refine (hsum q (by omega) hq'.2).mono_scale ?_
    rw [hKc]
    have hcard : ((q - m : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast (by omega : q - m ≤ h)
    have hsq : Real.sqrt ((q - m : ℕ) : ℝ) ≤ Real.sqrt (h : ℝ) := Real.sqrt_le_sqrt hcard
    have := mul_le_mul_of_nonneg_left hsq hC0nn
    exact mul_le_mul_of_nonneg_right this hc.le
  obtain ⟨Y, hYm, hYnn, hYO, hYb⟩ := gammaSigma_centered_Icc (μ := μ) (σ := 2) (A := Kc)
    (by norm_num) hKcnn (a := m + 1) (b := m + h) (by omega)
    (fun q => fun ω => |∑ r ∈ Finset.Ioc m q, X r ω|) hmeasQ hbigQ
  refine ⟨Y, hYm, hYnn, hYO, ?_⟩
  intro ω q hq
  have hN : (m + h + 1 - (m + 1) : ℕ) = h := by omega
  rw [hN] at hYb
  have hlog : 0 ≤ Kc * Real.log (2 * (h : ℝ)) ^ ((2 : ℝ)⁻¹) := by
    have : (1 : ℝ) ≤ 2 * (h : ℝ) := by
      have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
      linarith only [this]
    have := Real.log_nonneg this
    positivity
  by_cases hqm : q ≤ m
  · have hempty : Finset.Ioc m q = ∅ := Finset.Ioc_eq_empty_of_le hqm
    rw [hempty, Finset.sum_empty, abs_zero]
    have := hYnn ω
    linarith only [hlog, this]
  · have hmem : q ∈ Finset.Icc (m + 1) (m + h) :=
      Finset.mem_Icc.2 ⟨by omega, hq⟩
    have h1 := Finset.le_sup' (f := fun i => |∑ r ∈ Finset.Ioc m i, X r ω|) hmem
    have h2 := hYb ω
    linarith only [h1, h2]

end SuperdiffusionCLT.Section4.MinimalScales
