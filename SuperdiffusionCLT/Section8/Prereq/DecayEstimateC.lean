/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateB

/-!
# The dual `L²` bound on an annulus

Deterministic assembly of the dual argument: a zero-trace solution `u` of `-∇·(a∇u) = h`, with
`h` of mean zero supported in `B`, and an adjoint zero-trace solution `v` with source
`(u - m) 1_A`; if the adjoint solution has `L²(B)`-oscillation at most `K` times the `L²(A)` norm
of its source, then `‖u - m‖_{L²(A)} ≤ K ‖h‖_{L²(B)}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section7

noncomputable section

variable {d : ℕ}

/-- **Dual `L²` bound** (the step from the duality identity to the oscillation of `u` on `A`,
in the proof of `l.decay.estimate.Linfty`). -/
theorem decayEst_dual_l2 (a : CoeffField d) (U A B : Set (Vec d)) (hU : MeasurableSet U)
    (hA : MeasurableSet A) (hAU : A ⊆ U) (hBU : B ⊆ U)
    (u v : H10Function U) (h : Vec d → ℝ) (m c K : ℝ) (hK : 0 ≤ K)
    (hu : IsWeakSolutionOn a U u.toH1Function h (fun _ => 0))
    (hv : IsWeakSolutionOn (fun x => matTranspose (a x)) U v.toH1Function
      (A.indicator (fun x => u.toH1Function.toFun x - m)) (fun _ => 0))
    (hsupp : ∀ x, x ∉ B → h x = 0) (hmean : ∫ x in B, h x = 0)
    (hh : MemLp h 2 (volume.restrict B)) (hhi : Integrable h (volume.restrict B))
    (hvB : MemLp (fun x => v.toH1Function.toFun x - c) 2 (volume.restrict B))
    (hg : MemLp (fun x => u.toH1Function.toFun x - m) 2 (volume.restrict A))
    (hgi : Integrable (fun x => u.toH1Function.toFun x - m) (volume.restrict A))
    (hgmean : ∫ x in A, (u.toH1Function.toFun x - m) = 0)
    (hdual : Real.sqrt (∫ x in B, (v.toH1Function.toFun x - c) ^ 2) ≤
      K * Real.sqrt (∫ x in A, (u.toH1Function.toFun x - m) ^ 2)) :
    Real.sqrt (∫ x in A, (u.toH1Function.toFun x - m) ^ 2) ≤
      K * Real.sqrt (∫ x in B, h x ^ 2) := by
  set w : Vec d → ℝ := u.toH1Function.toFun
  have hp := decayEst_pairing a U u v h _ hu hv
  have h1 : ∫ x in U, A.indicator (fun x => w x - m) x * w x
      = ∫ x in A, (w x - m) * ((w x - m) + m) := by
    have : ∀ x, A.indicator (fun x => w x - m) x * w x =
        A.indicator (fun x => (w x - m) * ((w x - m) + m)) x := by
      intro x
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    simp only [this]
    rw [setIntegral_indicator hA, Set.inter_eq_right.mpr hAU]
  rw [h1] at hp
  have hosc := decayEst_pairing_osc U B hU hBU h v.toH1Function.toFun c hsupp hmean hh hhi hvB
  have hc : Real.sqrt (∫ x in B, (v.toH1Function.toFun x - c) ^ 2) *
      Real.sqrt (∫ x in B, h x ^ 2) ≤
      K * Real.sqrt (∫ x in A, (w x - m) ^ 2) * Real.sqrt (∫ x in B, h x ^ 2) :=
    mul_le_mul_of_nonneg_right hdual (Real.sqrt_nonneg _)
  refine decayEst_l2_of_dual A (fun x => w x - m) m (K * Real.sqrt (∫ x in B, h x ^ 2)) 
    (mul_nonneg hK (Real.sqrt_nonneg _)) hg hgi hgmean ?_
  rw [hp]
  linarith only [hosc, hc]

/-- Satisfiability: zero data on the empty annulus and source set (identity field). -/
example (U : Set (Vec d)) :
    ∃ (u v : H10Function U),
      IsWeakSolutionOn (fun _ => (1 : Mat d)) U u.toH1Function (fun _ => 0) (fun _ => 0) ∧
      IsWeakSolutionOn (fun x => matTranspose ((fun _ => (1 : Mat d)) x)) U v.toH1Function
        (Set.indicator (∅ : Set (Vec d)) (fun x => u.toH1Function.toFun x - 0)) (fun _ => 0) ∧
      Real.sqrt (∫ x in (∅ : Set (Vec d)), (v.toH1Function.toFun x - 0) ^ 2) ≤
        0 * Real.sqrt (∫ x in (∅ : Set (Vec d)), (u.toH1Function.toFun x - 0) ^ 2) := by
  refine ⟨0, 0, ?_, ?_, by simp⟩ <;>
  · intro φ
    have hg : ∀ x, (H10Function.toH1Function (0 : H10Function U)).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, hg]

end

end SuperdiffusionCLT.Section8
