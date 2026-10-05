/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimate

/-!
# Oscillation and norm conversion for the dual argument

Two real-analysis steps of the duality proof: the pairing of a mean-zero source supported in `B`
against a function is controlled by the oscillation of that function on `B`; and a bound on
`∫ g u` with `g = u - m` yields an `L²` bound on `g`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section7

noncomputable section

variable {d : ℕ}

/-- A source `h` supported in `B ⊆ U` with mean zero: `|∫_U h v| ≤ ‖v - c‖_{L²(B)} ‖h‖_{L²(B)}`. -/
theorem decayEst_pairing_osc (U B : Set (Vec d)) (hU : MeasurableSet U) (hBU : B ⊆ U)
    (h v : Vec d → ℝ) (c : ℝ)
    (hsupp : ∀ x, x ∉ B → h x = 0) (hmean : ∫ x in B, h x = 0)
    (hh : MemLp h 2 (volume.restrict B)) (hhi : Integrable h (volume.restrict B))
    (hv : MemLp (fun x => v x - c) 2 (volume.restrict B)) :
    |∫ x in U, h x * v x| ≤
      Real.sqrt (∫ x in B, (v x - c) ^ 2) * Real.sqrt (∫ x in B, h x ^ 2) := by
  have h1 : ∫ x in U, h x * v x = ∫ x in B, h x * v x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU hBU (fun x hx => by
      rw [hsupp x hx.2, zero_mul])
  have hI : Integrable (fun x => h x * (v x - c)) (volume.restrict B) := hh.integrable_mul hv
  have h2 : ∫ x in B, h x * v x = ∫ x in B, h x * (v x - c) := by
    have : ∀ x, h x * v x = h x * (v x - c) + c * h x := fun x => by ring
    simp only [this]
    rw [integral_add hI (hhi.const_mul c), integral_const_mul, hmean, mul_zero, add_zero]
  rw [h1, h2, mul_comm]
  have := decayEst_cauchy B (fun x => v x - c) h hv hh
  simpa only [mul_comm] using this

/-- If `g` has mean zero on `A` and `|∫_A g (g + m)| ≤ M ‖g‖_{L²(A)}`, then `‖g‖_{L²(A)} ≤ M`. -/
theorem decayEst_l2_of_dual (A : Set (Vec d)) (g : Vec d → ℝ) (m M : ℝ) (hM0 : 0 ≤ M)
    (hg : MemLp g 2 (volume.restrict A)) (hgi : Integrable g (volume.restrict A))
    (hmean : ∫ x in A, g x = 0)
    (hbound : |∫ x in A, g x * (g x + m)| ≤ M * Real.sqrt (∫ x in A, g x ^ 2)) :
    Real.sqrt (∫ x in A, g x ^ 2) ≤ M := by
  have hsq : Integrable (fun x => g x * g x) (volume.restrict A) := hg.integrable_mul hg
  have e : ∫ x in A, g x * (g x + m) = ∫ x in A, g x ^ 2 := by
    have : ∀ x, g x * (g x + m) = g x * g x + m * g x := fun x => by ring
    simp only [this]
    rw [integral_add hsq (hgi.const_mul m), integral_const_mul, hmean, mul_zero, add_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
  rw [e] at hbound
  set I := ∫ x in A, g x ^ 2 with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  rw [abs_of_nonneg hI0] at hbound
  have hs := Real.sq_sqrt hI0
  set s := Real.sqrt I
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  by_cases hz : s = 0
  · rw [hz]; exact hM0
  · have hpos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hz)
    have h3 : s * s ≤ M * s := by linarith only [hs, hbound, sq s]
    exact le_of_mul_le_mul_right h3 hpos

end

end SuperdiffusionCLT.Section8
