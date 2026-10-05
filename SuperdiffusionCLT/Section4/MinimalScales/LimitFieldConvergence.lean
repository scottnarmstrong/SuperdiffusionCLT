/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummability
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB

/-!
# Containment of `cu_m` in the open cube `cu_{m+1}`

This is the geometric input to the field-convergence half of the "It remains only to include the
limiting coefficient" paragraph of the proof of `p.new.mixing.attempt`: almost surely,
`a_L - (k_L)_{cu_m} → a - (k)_{cu_m}` pointwise on `cu_m`. The difference
`(k)_{cu_m} - (k_L)_{cu_m}` is the tail of the defining series of the centered stream field, whose
pointwise summability is supplied almost surely, for `U` a natural cube, by the Borel-Cantelli
module `SuperdiffusionCLT.Section2.Cutoff.eventually_summable_shellDerivLinftyNorm` at the
next-coarser scale `cu_{m+1}`, using that `cu_m ⊆ cu_{m+1}` as open sets.

## Main result

* `srootL_cubeSet_subset_openCubeSet_succ`: the half-open cube `cu_m` lies inside the open
  cube `cu_{m+1}`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Filter Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Frozen.Assumptions

/-- `cu_m` (half-open) sits inside the open cube `cu_{m+1}`: the side length
only grows by the factor `3` and the half-open cube's right endpoint is
already excluded on the open cube's side. -/
theorem srootL_cubeSet_subset_openCubeSet_succ {d : ℕ} (m : ℕ) :
    cubeSet (originCube d (m : ℤ)) ⊆
      openCubeSet (originCube d ((m + 1 : ℕ) : ℤ)) := by
  intro x hx
  rw [mem_cubeSet_originCube_iff] at hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  have hcast : (((m : ℕ) + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  have hpow : (3 : ℝ) ^ (m : ℤ) < (3 : ℝ) ^ (((m + 1 : ℕ) : ℤ)) := by
    rw [hcast, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    have hpos : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
    nlinarith only [hpos]
  refine ⟨?_, lt_trans hhi (by nlinarith only [hpow])⟩
  nlinarith only [hlo, hpow]

end SuperdiffusionCLT.Section4.MinimalScales
