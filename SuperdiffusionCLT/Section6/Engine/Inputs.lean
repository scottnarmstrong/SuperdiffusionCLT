/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.CaccCube
public import SuperdiffusionCLT.Section6.Engine.PoincCube
public import SuperdiffusionCLT.Section6.Engine.CorrectorCube
public import SuperdiffusionCLT.Section6.Engine.HarmonicCube
public import SuperdiffusionCLT.Section6.Engine.FieldAE
public import SuperdiffusionCLT.Section6.Engine.Params
public import SuperdiffusionCLT.Section6.Engine.SigmaGrowth
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import Mathlib.Order.CompletePartialOrder

/-!
# One-block inputs: deterministic bookkeeping

The recentered field of the origin cube `□_j` (`nu` plus the centered stream field), the
zero lattice shift, the window arithmetic and the monotone constant comparisons used when the
sharp-scale inputs are turned into the one-block inputs of the engine.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The field of the bullets of the sharp-scale inputs at the origin cube `□_j`. -/
noncomputable abbrev ea5_field (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (j : ℕ) :
    CoeffField d :=
  fun x => nu • (1 : Mat d) +
    SuperdiffusionCLT.Section2.Carriers.centeredStreamField omega
      (cubeSet (originCube d (j : ℤ))) x

theorem ea5_shift_eq (n : ℕ) (x : Vec d) :
    (fun i : Fin d => (3 : ℝ) ^ ((n : ℤ) - 3) * (((0 : Fin d → ℤ) i : ℤ) : ℝ)) + x = x := by
  funext i
  simp

theorem ea5_cubeSet_mono {n m : ℕ} (h : n ≤ m) :
    cubeSet (originCube d (n : ℤ)) ⊆ cubeSet (originCube d (m : ℤ)) := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    refine ih.trans ?_
    have := HarmonicApprox.originCube_pred_cubeSet_subset (d := d) ((m + 1 : ℕ) : ℤ)
    have e : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    rwa [e] at this

theorem ea5_zero_shift_incl {n m : ℕ} (h : n ≤ m) :
    (fun x : Vec d => (fun i : Fin d => (3 : ℝ) ^ ((n : ℤ) - 3) *
        (((0 : Fin d → ℤ) i : ℤ) : ℝ)) + x) '' cubeSet (originCube d (n : ℤ)) ⊆
      cubeSet (originCube d (m : ℤ)) := by
  rintro y ⟨x, hx, rfl⟩
  beta_reduce
  rw [ea5_shift_eq]
  exact ea5_cubeSet_mono h hx

/-- The window arithmetic: if `exp Hb ≤ j` and `1 ≤ C`, then `Hb ≤ ⌈C log j⌉`. -/
theorem ea5_block_le_ceil {C : ℝ} (hC : 1 ≤ C) {Hb j : ℕ} (hj : ⌈Real.exp (Hb : ℝ)⌉₊ ≤ j) :
    (Hb : ℤ) ≤ ⌈C * Real.log (j : ℝ)⌉ := by
  have h1 : Real.exp (Hb : ℝ) ≤ (j : ℝ) := (Nat.ceil_le.mp hj)
  have hjpos : (0 : ℝ) < (j : ℝ) := lt_of_lt_of_le (Real.exp_pos _) h1
  have h2 : (Hb : ℝ) ≤ Real.log (j : ℝ) := (Real.le_log_iff_exp_le hjpos).mpr h1
  have h3 : 0 ≤ Real.log (j : ℝ) := le_trans (Nat.cast_nonneg _) h2
  have h4 : (Hb : ℝ) ≤ C * Real.log (j : ℝ) := by nlinarith only [h2, h3, hC]
  exact_mod_cast h4.trans (Int.le_ceil _)

/-- Constants are monotone against nonnegative factors. -/
theorem ea5_mono3 {C Cin δ R S : ℝ} (hC : C ≤ Cin) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    C * δ * R * S ≤ Cin * δ * R * S := by
  gcongr

theorem ea5_mono2 {C Cin δ S : ℝ} (hC : C ≤ Cin) (hδ : 0 ≤ δ) (hS : 0 ≤ S) :
    C * δ * S ≤ Cin * δ * S := by
  gcongr

theorem ea5_mono_sqrt {C Cin a S : ℝ} (hC : C ≤ Cin) (hS : 0 ≤ S) :
    C * Real.sqrt a * S ≤ Cin * Real.sqrt a * S := by
  gcongr

theorem ea5_mono1 {C Cin S : ℝ} (hC : C ≤ Cin) (hS : 0 ≤ S) : C * S ≤ Cin * S := by
  gcongr

end SuperdiffusionCLT.Section6
