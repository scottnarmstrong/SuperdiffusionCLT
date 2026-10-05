/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Morrey.W1pD
public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2pF

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Hölder gradient on a cube from an `L^p` weak Hessian

Helpers for `holderGradient_of_weakHessian`: a weak Hessian in `L̲^p`, `p > d`, makes each
coordinate `∂ᵢw` a `W^{1,p}` function of the open cube, and the cube is an axis cube, so the
`W^{1,p}` Morrey inequality applies.  The restricted-volume `L^p` norm is the normalized one
times `|Q|^{1/p}`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- `L^p` membership for the normalized cube measure gives it for Lebesgue measure on the open
cube. -/
theorem holderGradient_memLp_restrict {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    {p : ℝ≥0∞} {f : Vec d → E}
    (hf : MemLp f p (normalizedCubeMeasure Q)) :
    MemLp f p (volume.restrict (openCubeSet Q)) :=
  (Homogenization.memLp_cubeMeasure_of_memLp_normalizedCubeMeasure Q hf).mono_measure
    (Measure.restrict_mono_set volume (openCubeSet_subset_cubeSet Q))

/-- Unnormalizing the `L^p` norm: on the open cube, `‖f‖_{L^p(dx)} ≤ |Q|^{1/p} ‖f‖_{L̲^p}`. -/
theorem holderGradient_eLpNorm_restrict_le {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    {p : ℝ≥0∞} (f : Vec d → E) :
    eLpNorm f p (volume.restrict (openCubeSet Q)) ≤
      ENNReal.ofReal (cubeVolume Q) ^ (1 / p).toReal * eLpNorm f p (normalizedCubeMeasure Q) := by
  have hV : 0 < cubeVolume Q := cubeVolume_pos Q
  have hcm : cubeMeasure Q = ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [normalizedCubeMeasure, smul_smul, ← ENNReal.ofReal_mul hV.le,
      mul_inv_cancel₀ hV.ne', ENNReal.ofReal_one, one_smul]
  have hle : volume.restrict (openCubeSet Q) ≤
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [← hcm]
    exact Measure.restrict_mono_set volume (openCubeSet_subset_cubeSet Q)
  simpa only [smul_eq_mul] using eLpNorm_le_of_measure_le_smul (f := f) (p := p) hle

/-- Entries of a matrix are bounded by its Hilbert norm. -/
theorem holderGradient_abs_entry_le {d : ℕ} (A : Mat d) (i j : Fin d) :
    |A i j| ≤ ‖HilbertMat.ofMat A‖ := by
  have h1 := PiLp.norm_apply_le (HilbertMat.ofMat A) i
  have h2 := PiLp.norm_apply_le ((HilbertMat.ofMat A) i) j
  simpa [HilbertMat.ofMat] using h2.trans h1

end SuperdiffusionCLT.Section7
