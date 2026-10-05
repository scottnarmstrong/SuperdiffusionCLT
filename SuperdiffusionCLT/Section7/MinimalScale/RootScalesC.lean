/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.RootScalesB
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Tails of the root scales

* `ms_scale_tail`: for `log X₀ = O_{Γ_ρ}(Λ)` and `σ ∈ (0, ρ]`, the scale `C₀ 3^{m⋆}` satisfies
  `P[t ≤ C₀ 3^{m⋆}] ≤ C exp(-C⁻¹ (log t)^σ)` for all `t ≥ 1`.
* `ms_scale_consumer`: every `n ≥ m⋆` satisfies the two conditions of the interior lemma.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open MeasureTheory

/-- **Tail of the Hölder-root scale.** -/
theorem ms_scale_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X₀ : Ω → ℝ} {Λ ρ σ N₀ L C₀ : ℝ} (hX : ∀ ω, 1 ≤ X₀ ω) (hΛ : 0 < Λ) (hσ : 0 < σ)
    (hσρ : σ ≤ ρ) (hN : 0 ≤ N₀) (hL : 0 ≤ L) (hC₀ : 1 ≤ C₀)
    (hO : Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma ρ)
      (fun ω => Real.log (X₀ ω)) Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      μ.real {ω | t ≤ C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω)} ≤
        C * Real.exp (-(C⁻¹ * (Real.log t) ^ σ)) := by
  have hT := ms_tail_mono_exp μ hσρ (ms_tail_of_isBigO hO) zero_le_one
  have hC0 : 0 < C₀ := by linarith only [hC₀]
  refine ms_transfer μ (W := fun ω => C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω))
    (f := fun ω => |Real.log (X₀ ω)|) (a := 2) (A := Λ)
    (b0 := Real.log C₀ + 2 * (ms_j0 N₀ + 2 * L + 2)) (B := 1) (σ := σ) (by norm_num) hΛ ?_ hσ
    (fun ω => ?_) hT
  · have : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
    have : (0 : ℝ) ≤ ms_j0 N₀ := by positivity
    positivity
  · have hb := ms_star_le_bound (L := L) hN hL (hX ω)
    have h1 : Real.log (C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω)) =
        Real.log C₀ + (ms_star N₀ L (X₀ ω) : ℝ) * Real.log 3 := by
      rw [Real.log_mul hC0.ne' (by positivity), Real.log_pow]
    have h2 : Real.log (X₀ ω) ≤ |Real.log (X₀ ω)| := le_abs_self _
    show Real.log (C₀ * (3 : ℝ) ^ ms_star N₀ L (X₀ ω)) ≤ 2 * |Real.log (X₀ ω)| + _
    linarith only [h1, hb, h2]

/-- **Consumer form.** If `3^{m⋆} ≤ 3^n` then `n` satisfies the interior-lemma conditions. -/
theorem ms_scale_consumer {N₀ L X₀ : ℝ} (hN : 0 ≤ N₀) (hX : 1 ≤ X₀) {n : ℕ}
    (hn : (3 : ℝ) ^ ms_star N₀ L X₀ ≤ (3 : ℝ) ^ n) :
    ms_j0 N₀ ≤ n ∧ L ≤ (ms_e N₀ n : ℝ) ∧ X₀ ≤ (3 : ℝ) ^ (ms_e N₀ n) :=
  ms_star_persist hN hX ((pow_le_pow_iff_right₀ (by norm_num)).1 hn)

/-- Real-scale form: if `r ≥ C₀ 3^{m⋆}`, the scale `n = ⌊log₃ (r / C₀)⌋₊` is at least `m⋆`. -/
theorem ms_scale_consumer_real {N₀ L X₀ C₀ r : ℝ} (hN : 0 ≤ N₀) (hX : 1 ≤ X₀) (hC₀ : 1 ≤ C₀)
    (hr : C₀ * (3 : ℝ) ^ ms_star N₀ L X₀ ≤ r) :
    ms_star N₀ L X₀ ≤ ⌊Real.logb 3 (r / C₀)⌋₊ ∧
      ms_j0 N₀ ≤ ⌊Real.logb 3 (r / C₀)⌋₊ ∧
      L ≤ (ms_e N₀ ⌊Real.logb 3 (r / C₀)⌋₊ : ℝ) ∧
      X₀ ≤ (3 : ℝ) ^ (ms_e N₀ ⌊Real.logb 3 (r / C₀)⌋₊) := by
  have hC0 : 0 < C₀ := by linarith only [hC₀]
  have h1 : (3 : ℝ) ^ ms_star N₀ L X₀ ≤ r / C₀ := by
    rw [le_div_iff₀ hC0]; linarith only [hr]
  have h2 : (ms_star N₀ L X₀ : ℝ) ≤ Real.logb 3 (r / C₀) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le (by positivity) h1)]
    simpa using h1
  have h3 : ms_star N₀ L X₀ ≤ ⌊Real.logb 3 (r / C₀)⌋₊ := Nat.le_floor h2
  exact ⟨h3, ms_star_persist hN hX h3⟩

/-- Satisfiability witness: `X₀ ≡ 1` on a Dirac measure. -/
example {Ω : Type*} [MeasurableSpace Ω] (ω₀ : Ω) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      (MeasureTheory.Measure.dirac ω₀).real
        {ω | t ≤ (1 : ℝ) * (3 : ℝ) ^ ms_star 1 1 ((fun _ : Ω => (1 : ℝ)) ω)} ≤
        C * Real.exp (-(C⁻¹ * (Real.log t) ^ (1 / 2 : ℝ))) := by
  refine ms_scale_tail (MeasureTheory.Measure.dirac ω₀) (X₀ := fun _ : Ω => (1 : ℝ))
    (Λ := 1) (ρ := 1) (σ := 1 / 2) (N₀ := 1) (L := 1) (C₀ := 1) (fun _ => le_rfl)
    one_pos (by norm_num) (by norm_num) zero_le_one zero_le_one le_rfl ?_
  rw [Homogenization.IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have h : Homogenization.IndependentSums.absTailEvent (fun _ : Ω => Real.log (1 : ℝ)) (1 * t) =
      ∅ := by
    ext ω
    simp only [Homogenization.IndependentSums.mem_absTailEvent, Real.log_one, abs_zero,
      Set.mem_empty_iff_false, iff_false, not_lt]
    linarith only [ht]
  rw [h]
  simp only [measureReal_empty]
  exact (Real.exp_pos _).le

end SuperdiffusionCLT.Section7
