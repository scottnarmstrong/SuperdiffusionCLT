/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Neumann.NeumannInputC
public import SuperdiffusionCLT.Section5.Response.Assembly

/-!
# The Neumann input: the limit `K → ∞`

The energy error of `lem.response` carries the factor `(1 + (Kc - m))^{2/5} 3^{-(2/5)(Kc - m)}`,
which tends to zero (`tendsto_tail`); the finiteness of the annealed energy follows from the
`L⁸` clause (`lintegral_sq_ne_top_of_lintegral_pow_eight`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Filter Topology

theorem tendsto_tail :
    Tendsto (fun x : ℝ => (1 + x) ^ ((2 : ℝ) / 5) * (3 : ℝ) ^ (-((2 : ℝ) / 5 * x)))
      atTop (𝓝 0) := by
  have hc : (0 : ℝ) < (2 : ℝ) / 5 * Real.log 3 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    positivity
  have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2 : ℝ) / 5)
    ((2 : ℝ) / 5 * Real.log 3) hc).comp (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have h2 := h1.const_mul (Real.exp ((2 : ℝ) / 5 * Real.log 3))
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply, id]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← mul_assoc, mul_comm _ ((1 + x) ^ _),
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem lintegral_sq_ne_top_of_lintegral_pow_eight {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w z x : Ω → ENNReal) (hxz : ∀ ω, x ω ≤ z ω)
    {c : ENNReal} (hc : c ≠ ⊤)
    (hA : (∫⁻ ω, (w ω ^ (8 : ℕ) + z ω ^ (8 : ℕ)) ∂μ) ^ ((1 : ℝ) / 8) ≤ c) :
    ∫⁻ ω, x ω ^ (2 : ℕ) ∂μ ≠ ⊤ := by
  have hfin : ∫⁻ ω, (w ω ^ (8 : ℕ) + z ω ^ (8 : ℕ)) ∂μ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by norm_num)] at hA
    exact hc (top_le_iff.1 hA)
  have hpt : ∀ ω, x ω ^ (2 : ℕ) ≤ 1 + (w ω ^ (8 : ℕ) + z ω ^ (8 : ℕ)) := by
    intro ω
    have h2 : x ω ^ (2 : ℕ) ≤ z ω ^ (2 : ℕ) := pow_le_pow_left' (hxz ω) 2
    rcases le_total (z ω) 1 with hz | hz
    · calc x ω ^ (2 : ℕ) ≤ z ω ^ (2 : ℕ) := h2
        _ ≤ 1 := pow_le_one' hz 2
        _ ≤ _ := le_self_add
    · calc x ω ^ (2 : ℕ) ≤ z ω ^ (2 : ℕ) := h2
        _ ≤ z ω ^ (8 : ℕ) := pow_le_pow_right' hz (by norm_num)
        _ ≤ _ := le_add_self.trans le_add_self
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hfin⟩

end SuperdiffusionCLT.Section5
