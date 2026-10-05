/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Deterministic.MultiscaleQuantities
public import Homogenization.CoarseGraining.Translation

/-!
# Translation covariance of `normalizedBlockResponseMax` (bare `CoeffField` carrier)

Extending the near-local origin-cube bound to every
descendant cube `y + cu_l` needs the translation covariance of the carrier
`Homogenization.normalizedBlockResponseMax` (the bare-`CoeffField` declaration in
`Deterministic.MultiscaleQuantities`, **not** the `TriadicCoeffFamily`-based
`Homogenization.Book.Ch02.normalizedBlockResponseMax` that
`Book/Ch02/Theorems/HomogenizationError/Translation.lean` already covers: that file's translation
statement takes `a b : TriadicCoeffFamily d`, a different declaration).

This module proves that covariance from first principles, via
`Homogenization.BlockJ_translateSet_eq_translateCoeffField`
(`CoarseGraining/Translation.lean`): `normalizedBlockResponseMax`'s defining value set only
reads the field `a` through `BlockJ (cubeSet Q) P Q' a` at two test vectors `P, Q'` that depend on
`a0`, not on `Q`, so translating the cube translates the field exactly as
`BlockJ_translateSet_eq_translateCoeffField` prescribes.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

noncomputable section

/-- `cubeSet (translateCube shift Q)` is the real-space translate of `cubeSet Q` by the
matching shift `fun i => (shift i : ℝ) * cubeScaleFactor Q`. -/
private theorem srootN3_cubeSet_translateCube_eq {d : ℕ} (shift : Fin d → ℤ)
    (Q : Homogenization.TriadicCube d) :
    Homogenization.cubeSet (Homogenization.translateCube shift Q) =
      Homogenization.translateSet
        (fun i => (shift i : ℝ) * Homogenization.cubeScaleFactor Q)
        (Homogenization.cubeSet Q) := by
  ext x
  rw [Homogenization.mem_cubeSet_translateCube_iff, Homogenization.mem_translateSet_iff_sub_mem]

/-- **Translation covariance of `normalizedBlockResponseMax`.** Translating the cube by an
integer lattice `shift` reads the same as evaluating at the origin-scale cube `Q` with the
field itself translated by the matching real shift `fun i => (shift i : ℝ) * cubeScaleFactor Q`.
The reference envelope `a0` is untouched (it never depends on the cube). -/
theorem srootN3_normalizedBlockResponseMax_translateCube_eq {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Homogenization.CoeffField d) (a0 : Homogenization.Mat d)
    (shift : Fin d → ℤ) :
    Homogenization.normalizedBlockResponseMax (Homogenization.translateCube shift Q) a a0 =
      Homogenization.normalizedBlockResponseMax Q
        (Homogenization.translateCoeffField
          (fun i => (shift i : ℝ) * Homogenization.cubeScaleFactor Q) a) a0 := by
  unfold Homogenization.normalizedBlockResponseMax
  congr 1
  unfold Homogenization.normalizedBlockResponseValueSet
  ext m
  simp only [Set.mem_ofPred_eq]
  refine exists_congr fun e => and_congr_right fun _ => ?_
  rw [srootN3_cubeSet_translateCube_eq shift Q,
    Homogenization.BlockJ_translateSet_eq_translateCoeffField]

end

end SuperdiffusionCLT.Section4.MinimalScales
