/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.LimitTermFieldUniform
public import SuperdiffusionCLT.Section2.Localization.BlockPerturbation
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB
public import SuperdiffusionCLT.Section4.MinimalScales.LimitLocLimFieldEllipticity
public import SuperdiffusionCLT.Section4.MinimalScales.LimitRespEllipticity

/-!
# The Loewner sandwich `bfA(cu_n; a_L)` vs `bfA(cu_n; a_∞)`

Assembles `SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_localization_scalar_two_sided`
(the scalar two-sided form of `l.localization.A`) at
`a := srootE_limField`, `b := srootE_field L`, `h := srootE_field L −
srootE_limField`. The perturbation `h` is skew (difference of two skew fields,
`centeredStreamCutoff_skew`/`centeredStreamField_skew`) with a uniform operator
norm bound `M_L := d · bound(L)`, `bound` the a.s. `L^∞(cu_m)` field-convergence
sequence of `LimitTermFieldUniform.lean` (converted from the entrywise bound
via the general `matrixOperatorNorm_le_of_entry_bound`); `M_L → 0` a.s.

The conclusion is stated at the *raw* layer (`Homogenization.coarseBlockMatrix`
on the raw `CoeffField d`, not the bundled `Book.Ch02.CoeffOn`) so that no
proof-term of the a.s. summability hypothesis needs to appear in the
*statement*; the proof builds the `Book.Ch02.CoeffOn` bundles internally (after
`filter_upwards` has fixed `omega`) and converts via
`SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_toCoeffField`.

## Main results

* `srootL4_hField`: the perturbation field `h_L := srootE_field(L) − srootE_limField`.
* `srootL4_hField_eq`, `srootL4_hField_skew`: its pointwise form and its skewness.
The two-sided `BlockMatLoewnerLE` sandwich of `coarseBlockMatrix (openCubeSet n; a_L)`
around `coarseBlockMatrix (openCubeSet n; a_∞)` with relative factor
`D_L := nu⁻¹ M_L + nu⁻¹² M_L²` is obtained from these in `LimitLocDescendant.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open Homogenization MeasureTheory Filter
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Frozen.Assumptions
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- The perturbation field `h_L := srootE_field(L) − srootE_limField`, as a raw
`CoeffField d`. -/
def srootL4_hField {d : ℕ} [NeZero d] (nu : ℝ)
    (omega : ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ) : Homogenization.CoeffField d :=
  fun x => srootE_field nu omega L m n k x - srootE_limField nu omega m n k x

theorem srootL4_hField_eq {d : ℕ} [NeZero d] (nu : ℝ)
    (omega : ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ) (x : Vec d) :
    srootL4_hField nu omega L m n k x =
      centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
          ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) -
        centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
          ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) := by
  show (nu • (1 : Mat d) +
        centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
          ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) -
      (nu • (1 : Mat d) +
        centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
          ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) = _
  abel

theorem srootL4_hField_skew {d : ℕ} [NeZero d] (nu : ℝ)
    (omega : ShellSeq d) (L m n : ℕ) (k : Fin d → ℤ) (x : Vec d) :
    matTranspose (srootL4_hField nu omega L m n k x) = -srootL4_hField nu omega L m n k x := by
  rw [srootL4_hField_eq]
  have h1 := centeredStreamCutoff_skew omega L (cubeSet (originCube d (m : ℤ)))
    ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)
  have h2 := centeredStreamField_skew omega (cubeSet (originCube d (m : ℤ)))
    ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)
  rw [show matTranspose (centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
        ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x) -
      centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
        ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) =
      matTranspose (centeredStreamCutoff omega L (cubeSet (originCube d (m : ℤ)))
        ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) -
      matTranspose (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))
        ((fun l => (3 : ℝ) ^ ((n : ℤ) - 3) * (k l : ℝ)) + x)) from Matrix.transpose_sub _ _,
    h1, h2]
  abel

end

end SuperdiffusionCLT.Section4.MinimalScales
