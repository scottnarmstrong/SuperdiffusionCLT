/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.LinftyL2Bdry

/-!
# Boundary `L^∞`-`L²` estimate: elementary averaging lemmas

The conversion of the oscillation into the norm on the annulus by a cut cell, the telescoping of
means along a chain of cells, and the absorption of the polynomial ellipticity ratio by the
bottom-scale gain.
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- **Conversion.** If a subcell `q` of `Wa` carries a small share of the norm of `u`, then the
norm of `u` on `Wa` is controlled by its oscillation. -/
theorem linfL2c_conv {Wa q : Set (Vec d)} (hq : q ⊆ Wa) (hW : volume Wa ≠ ⊤)
    (hvq : 0 < (volume q).toReal) {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict Wa))
    {V θ : ℝ} (hV : (volume Wa).toReal / (volume q).toReal ≤ V) (hθ : θ ≤ 1 / 2)
    (hcell : linfL2b_nl2 q u ≤ θ * (h1_l2 Wa u + linfL2b_nl2 Wa u)) :
    linfL2b_nl2 Wa u ≤ (3 + 2 * Real.sqrt V) * h1_l2 Wa u := by
  have hqfin : volume q ≠ ⊤ := ne_top_of_le_ne_top hW (measure_mono hq)
  have hvW : 0 < (volume Wa).toReal :=
    lt_of_lt_of_le hvq (ENNReal.toReal_mono hW (measure_mono hq))
  have huq : MemLp u 2 (volume.restrict q) := hu.mono_measure (Measure.restrict_mono hq le_rfl)
  have h1 := linfL2b_nl2_le_add hW hvW hu
  have h2 := h1_avg_sub_le hq hu hW hvq
  have h3 := linfL2b_avg_abs_le hqfin hvq huq
  have hD : 0 ≤ h1_l2 Wa u := Real.sqrt_nonneg _
  have hY : 0 ≤ linfL2b_nl2 Wa u := linfL2b_nl2_nonneg _ _
  have hsq : Real.sqrt ((volume Wa).toReal / (volume q).toReal) ≤ Real.sqrt V :=
    Real.sqrt_le_sqrt hV
  have h4 : Real.sqrt ((volume Wa).toReal / (volume q).toReal) * h1_l2 Wa u ≤
      Real.sqrt V * h1_l2 Wa u := mul_le_mul_of_nonneg_right hsq hD
  have h5 : |h1_avg Wa u| ≤ |h1_avg q u - h1_avg Wa u| + |h1_avg q u| := by
    have := abs_add_le (h1_avg Wa u - h1_avg q u) (h1_avg q u)
    rw [abs_sub_comm] at this
    simpa using this
  have hsV : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
  have h6 : linfL2b_nl2 Wa u * (1 - θ) ≤ (1 + Real.sqrt V + θ) * h1_l2 Wa u := by
    have h7 : linfL2b_nl2 Wa u ≤ h1_l2 Wa u + Real.sqrt V * h1_l2 Wa u +
        θ * (h1_l2 Wa u + linfL2b_nl2 Wa u) := by
      linarith only [h1, h2, h3, h4, h5, hcell]
    nlinarith only [h7]
  have h8 : linfL2b_nl2 Wa u * (1 / 2) ≤ linfL2b_nl2 Wa u * (1 - θ) :=
    mul_le_mul_of_nonneg_left (by linarith only [hθ]) hY
  have h9 : (1 + Real.sqrt V + θ) * h1_l2 Wa u ≤ (3 / 2 + Real.sqrt V) * h1_l2 Wa u :=
    mul_le_mul_of_nonneg_right (by linarith only [hθ]) hD
  nlinarith only [h6, h8, h9]

/-- **Telescoping of means along a chain of cells.** -/
theorem linfL2c_chain_mean {T : ℕ → Set (Vec d)} {u : Vec d → ℝ} {θ : ℕ → ℝ} {K : ℝ}
    (hmono : ∀ t, T t ⊆ T (t + 1)) (hfin : ∀ t, volume (T t) ≠ ⊤)
    (hpos : ∀ t, 0 < (volume (T t)).toReal) (hL2 : ∀ t, MemLp u 2 (volume.restrict (T t)))
    (hK : ∀ t, (volume (T (t + 1))).toReal ≤ K * (volume (T t)).toReal) {N : ℕ}
    (hosc : ∀ t, t < N → h1_l2 (T (t + 1)) u ≤ θ t) :
    |h1_avg (T 0) u| ≤ Real.sqrt K * ∑ s ∈ Finset.range N, θ s + linfL2b_nl2 (T N) u := by
  have h := linfL2b_chain_abs hmono hfin hpos hL2 hK hosc N le_rfl
  have h2 := linfL2b_avg_abs_le (hfin N) (hpos N) (hL2 N)
  have h3 : |h1_avg (T 0) u| ≤ |h1_avg (T 0) u - h1_avg (T N) u| + |h1_avg (T N) u| := by
    have := abs_add_le (h1_avg (T 0) u - h1_avg (T N) u) (h1_avg (T N) u)
    simpa using this
  linarith only [h, h2, h3]

/-- The geometric sum of the oscillation bounds along the chain. -/
theorem linfL2c_geom_chain (n N m' : ℕ) (hm : n + N + 1 = m') :
    ∑ s ∈ Finset.range N, ((3 : ℝ) ^ (n + s + 1) / (3 : ℝ) ^ m') ≤ 1 / 2 := by
  have h : ∑ s ∈ Finset.range N, ((3 : ℝ) ^ (n + s + 1) / (3 : ℝ) ^ m') =
      ((3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ m') * ∑ s ∈ Finset.range N, (3 : ℝ) ^ s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show n + s + 1 = (n + 1) + s by ring, pow_add]
    ring
  rw [h]
  have h2 := linfL2b_geom_sum N
  have hp : (0 : ℝ) < (3 : ℝ) ^ m' := by positivity
  have hq : 0 ≤ (3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ m' := by positivity
  calc ((3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ m') * ∑ s ∈ Finset.range N, (3 : ℝ) ^ s
      ≤ ((3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ m') * ((3 : ℝ) ^ N / 2) :=
        mul_le_mul_of_nonneg_left h2 hq
    _ = (3 : ℝ) ^ (n + 1 + N) / (3 : ℝ) ^ m' / 2 := by rw [pow_add (3 : ℝ) (n + 1) N]; ring
    _ = 1 / 2 := by
        rw [show n + 1 + N = m' by omega, div_self hp.ne']


theorem linfL2c_log_three : 1 ≤ Real.log 3 := by
  have h := Real.exp_one_lt_d9
  have h2 : Real.exp 1 ≤ 3 := by linarith only [h]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log 3 := Real.log_le_log (Real.exp_pos 1) h2

/-- The bottom-scale gain: `3^{⌈N log m'⌉} ≥ m'^N`. -/
theorem linfL2c_pow_ceil {N : ℝ} (hN : 0 ≤ N) {m' : ℕ} (hm : 1 ≤ m') :
    (m' : ℝ) ^ N ≤ (3 : ℝ) ^ ⌈N * Real.log (m' : ℝ)⌉₊ := by
  have hm1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m' := by linarith only [hm1]
  have hx : 0 ≤ N * Real.log (m' : ℝ) := mul_nonneg hN (Real.log_nonneg hm1)
  have h1 : (3 : ℝ) ^ (N * Real.log (m' : ℝ)) ≤ (3 : ℝ) ^ ⌈N * Real.log (m' : ℝ)⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have h2 : (m' : ℝ) ^ N ≤ (3 : ℝ) ^ (N * Real.log (m' : ℝ)) := by
    rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    refine Real.exp_le_exp.2 ?_
    have := linfL2c_log_three
    nlinarith only [this, hx]
  exact h2.trans h1

/-- **Absorption.** The polynomial ellipticity ratio is absorbed by the bottom-scale gain. -/
theorem linfL2c_absorb {N K0 : ℝ} (hN : 0 ≤ N) (hK0 : 0 ≤ K0) {m' m n c : ℕ} (hm'1 : 1 ≤ m')
    (hmm : m ≤ 2 * m') (hc : c = ⌈(4 * N + 1) * Real.log (m' : ℝ)⌉₊) (hnc : n + c = m')
    (hk : K0 * (2 : ℝ) ^ (4 * N) ≤ (m' : ℝ)) :
    K0 * (((m : ℝ) ^ 4) ^ N) * ((3 : ℝ) ^ n / (3 : ℝ) ^ m') ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'1
  have hm0 : (0 : ℝ) < m' := by linarith only [hm1]
  have hmr : (m : ℝ) ≤ 2 * m' := by exact_mod_cast hmm
  have hmn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpc := linfL2c_pow_ceil (N := 4 * N + 1) (by linarith only [hN]) hm'1
  rw [← hc] at hpc
  have e3 : (3 : ℝ) ^ m' = (3 : ℝ) ^ n * (3 : ℝ) ^ c := by rw [← hnc, pow_add]
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hr : (3 : ℝ) ^ n / (3 : ℝ) ^ m' = 1 / (3 : ℝ) ^ c := by
    rw [e3]; field_simp
  rw [hr]
  have h4 : ((m : ℝ) ^ 4) ^ N ≤ (2 : ℝ) ^ (4 * N) * (m' : ℝ) ^ (4 * N) := by
    have h5 : (m : ℝ) ^ 4 ≤ (2 * m') ^ 4 := pow_le_pow_left₀ hmn hmr 4
    calc ((m : ℝ) ^ 4) ^ N ≤ (((2 : ℝ) * m') ^ 4) ^ N :=
          Real.rpow_le_rpow (by positivity) h5 hN
      _ = ((2 : ℝ) ^ 4 * (m' : ℝ) ^ 4) ^ N := by rw [mul_pow]
      _ = ((2 : ℝ) ^ 4) ^ N * ((m' : ℝ) ^ 4) ^ N :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (4 * N) * (m' : ℝ) ^ (4 * N) := by
          rw [← Real.rpow_natCast (2 : ℝ) 4, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_natCast (m' : ℝ) 4, ← Real.rpow_mul hm0.le]
          norm_num
  have h6 : (m' : ℝ) ^ (4 * N + 1) = (m' : ℝ) ^ (4 * N) * m' := by
    rw [Real.rpow_add hm0, Real.rpow_one]
  have hp4 : 0 < (m' : ℝ) ^ (4 * N) := Real.rpow_pos_of_pos hm0 _
  have hpos : 0 < (3 : ℝ) ^ c := by positivity
  rw [mul_one_div, div_le_one hpos]
  calc K0 * ((m : ℝ) ^ 4) ^ N ≤ K0 * ((2 : ℝ) ^ (4 * N) * (m' : ℝ) ^ (4 * N)) :=
        mul_le_mul_of_nonneg_left h4 hK0
    _ = (K0 * (2 : ℝ) ^ (4 * N)) * (m' : ℝ) ^ (4 * N) := by ring
    _ ≤ (m' : ℝ) * (m' : ℝ) ^ (4 * N) := mul_le_mul_of_nonneg_right hk hp4.le
    _ = (m' : ℝ) ^ (4 * N + 1) := by rw [h6]; ring
    _ ≤ _ := hpc

end SuperdiffusionCLT.Section8
