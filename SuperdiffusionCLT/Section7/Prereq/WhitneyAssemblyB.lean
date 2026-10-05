/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.WhitneyAssembly

/-!
# The gradient of the replaced interpolant

On every cell of `Zg` the gradient of the interpolant is bounded by the differences of the
neighbouring values, which are bounded by the oscillations of `u` on the averaging cubes of `Zg`.
Summing over the cells with the bounded overlap gives `∫ |∇A|² ≤ C d³ 27^d h⁻² ∑ osc`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

/-- The gradient estimate on one cell of `Zg`. -/
theorem wh3_interp_grad_cell {h r : ℝ} (hh : 0 < h) (hr : 5 * h / 2 ≤ r)
    {Zg : Finset (Fin d → ℤ)} {k₀ : Fin d → ℤ} (hk₀ : k₀ ∈ Zg) (c : (Fin d → ℤ) → ℝ)
    (u : Vec d → ℝ) (hu : AEMeasurable u (volume.restrict (wh1_box (wh1_pt h k₀) r))) :
    ∫⁻ x in wh3_cell h k₀, ENNReal.ofReal (∑ i,
        (lipGradient (wh1_A h (Zg.biUnion wh1_nbhd) (fun k => c (wh3_sig Zg k))) x i) ^ 2) ≤
      ENNReal.ofReal ((d : ℝ) ^ 3 * 3 ^ d / h ^ 2) *
        (2 * (∑ k ∈ wh1_nbhd k₀, wh1_osc h r u c (wh3_sig Zg k) +
          3 ^ d * wh1_osc h r u c k₀)) := by
  have hZ' : wh1_nbhd k₀ ⊆ Zg.biUnion wh1_nbhd :=
    fun k hk => Finset.mem_biUnion.2 ⟨k₀, hk₀, hk⟩
  refine (wh1_lintegral_grad_le hh hZ' (fun k => c (wh3_sig Zg k))).trans ?_
  have e : (d : ℝ) ^ 3 * 3 ^ d * h ^ d / h ^ 2 *
      ∑ k ∈ wh1_nbhd k₀, ((fun k => c (wh3_sig Zg k)) k - (fun k => c (wh3_sig Zg k)) k₀) ^ 2 =
      (d : ℝ) ^ 3 * 3 ^ d / h ^ 2 * (∑ k ∈ wh1_nbhd k₀,
        h ^ d * (c (wh3_sig Zg k) - c k₀) ^ 2) := by
    simp only [wh3_sig_of_mem hk₀, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, ENNReal.ofReal_mul (by positivity)]
  gcongr
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
  have hterm : ∀ k ∈ wh1_nbhd k₀, ENNReal.ofReal (h ^ d * (c (wh3_sig Zg k) - c k₀) ^ 2) ≤
      2 * (wh1_osc h r u c (wh3_sig Zg k) + wh1_osc h r u c k₀) := by
    intro k hk
    have hkZ : k ∈ Zg.biUnion wh1_nbhd := hZ' hk
    have hs := (wh3_sig_mem hkZ).2
    have := wh3_sq_diff_le hh hr (k₀ := k₀) (a := wh3_sig Zg k) (fun i => wh3_near_two hk hs i) c u hu
    rw [ENNReal.ofReal_mul (by positivity), mul_comm]
    exact this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, wh1_card_nbhd, nsmul_eq_mul]
  push_cast
  rfl

/-- The `L²` gradient estimate over the cells of `Zg`. -/
theorem wh3_interp_grad {h r : ℝ} (hh : 0 < h) (hr : 5 * h / 2 ≤ r)
    (Zg : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (u : Vec d → ℝ)
    (hu : ∀ k₀ ∈ Zg, AEMeasurable u (volume.restrict (wh1_box (wh1_pt h k₀) r))) :
    ∫⁻ x in ⋃ k₀ ∈ Zg, wh3_cell h k₀, ENNReal.ofReal (∑ i,
        (lipGradient (wh1_A h (Zg.biUnion wh1_nbhd) (fun k => c (wh3_sig Zg k))) x i) ^ 2) ≤
      ENNReal.ofReal (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2) * ∑ a ∈ Zg, wh1_osc h r u c a := by
  refine (wh1_lintegral_biUnion_le Zg _ _).trans ?_
  refine (Finset.sum_le_sum fun k₀ hk₀ => wh3_interp_grad_cell hh hr hk₀ c u (hu k₀ hk₀)).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := wh3_sum_sig_le Zg fun a => wh1_osc h r u c a
  have e : ENNReal.ofReal (4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2) =
      ENNReal.ofReal ((d : ℝ) ^ 3 * 3 ^ d / h ^ 2) * (4 * 9 ^ d) := by
    have : 4 * (d : ℝ) ^ 3 * 27 ^ d / h ^ 2 = (d : ℝ) ^ 3 * 3 ^ d / h ^ 2 * (4 * 9 ^ d) := by
      have h27 : (27 : ℝ) ^ d = 3 ^ d * 9 ^ d := by
        rw [← mul_pow]; norm_num
      rw [h27]; ring
    rw [this, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h3 : (3 : ℝ≥0∞) ^ d ≤ 9 ^ d := by gcongr; norm_num
  have key : 2 * (∑ k₀ ∈ Zg, ∑ k ∈ wh1_nbhd k₀, wh1_osc h r u c (wh3_sig Zg k) +
        3 ^ d * ∑ k₀ ∈ Zg, wh1_osc h r u c k₀) ≤ 4 * 9 ^ d * ∑ a ∈ Zg, wh1_osc h r u c a := by
    calc 2 * (∑ k₀ ∈ Zg, ∑ k ∈ wh1_nbhd k₀, wh1_osc h r u c (wh3_sig Zg k) +
        3 ^ d * ∑ k₀ ∈ Zg, wh1_osc h r u c k₀)
        ≤ 2 * (9 ^ d * ∑ a ∈ Zg, wh1_osc h r u c a + 9 ^ d * ∑ k₀ ∈ Zg, wh1_osc h r u c k₀) := by
          gcongr
      _ = 4 * 9 ^ d * ∑ a ∈ Zg, wh1_osc h r u c a := by ring
  calc _ ≤ ENNReal.ofReal ((d : ℝ) ^ 3 * 3 ^ d / h ^ 2) *
        (4 * 9 ^ d * ∑ a ∈ Zg, wh1_osc h r u c a) := by gcongr
    _ = _ := by rw [e]; ring

end SuperdiffusionCLT.Section7
