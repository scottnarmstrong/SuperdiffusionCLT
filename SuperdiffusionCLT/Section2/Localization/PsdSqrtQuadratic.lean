/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Homogenization.Ambient.BlockMatrix
public import Homogenization.Ambient.CoefficientField
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Homogenization.Sobolev.H1.Definitions
public import SuperdiffusionCLT.Section2.Cutoff.Finite

/-!
# The quadratic form of the square root of a coarse block

The pointwise operator-norm bridge behind Step 3 of the proof of `l.RHS.term3`.

The left side of `e.bL.to.bhomell` is the double lattice
average of `|b_{L'}^{1/2}(z + cu_n) (∇w)_{z' + cu_k}|²`, where `b_{L'}` is the
coarse block and `b_{L'}^{1/2}` is its positive square root; the Hölder step
of that proof turns it into the double average of
`|b_{L'}(z + cu_n)| · |(∇w)_{z' + cu_k}|²`.  The pointwise bridge between the
two is

`|b^{1/2} v|² = v · (b v) ≤ |b| |v|²`,

for a symmetric positive-semidefinite block `b` and its square root.  This is
the free-binder bridge `hbHalfLe` of the display `e.bL.to.bhomell` in the proof of
`l.RHS.term3`, whose coarse blocks on the
translated cubes `z + cu_n` have no dedicated carrier: the hypothesis is stated
there for *arbitrary* real-valued functions `bHalfW` and `bLnorm`.

## The carrier

The square root is `CFC.sqrt b`, the positive square root of the continuous
functional calculus for real matrices (`Mathlib.Analysis.Matrix.Order`), which
is the carrier already used for exactly this purpose
(`constantFullBlockMatrixSqrt` in the CoarseGraining library).
`Matrix.PosSemidef` in that carrier is the nonnegativity of the quadratic form
together with self-adjointness, so a `PosSemidef` matrix is automatically symmetric.

The operator norm is `Book.Ch02.matrixOperatorNorm`; the inequality
`v · (b v) ≤ |b| |v|²` is
`vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef`.
What is new here is only the identity `|b^{1/2} v|² = v · (b v)`, proved from
self-adjointness of `CFC.sqrt b` and `CFC.sqrt_mul_sqrt_self`.

## Main results

* `posSemidef_sqrt_mul_self`, `posSemidef_sqrt_posSemidef`,
  `posSemidef_sqrt_isSymm`: the three algebraic facts about the carrier.
* `vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul`: `|b^{1/2} v|² = v · (b v)`.
* `vecNormSq_sqrt_matVecMul_le`: `|b^{1/2} v|² ≤ |b| |v|²`.
* `psdSqrtQuadratic_hbHalfLe`: the corollary in the shape of the hypothesis
  `hbHalfLe` of `e.bL.to.bhomell`, with `bHalfW omega z' z` the quadratic form of
  the square root of the coarse block `bBlock omega z` at the averaged gradient
  on the translated cube and `bLnorm omega z := |bBlock omega z|`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The square root carrier -/

/-- The square root of a symmetric positive-semidefinite block matrix is itself
symmetric positive-semidefinite, and its square is `b` (`CFC.sqrt_mul_sqrt_self`
with the matrix order of `Mathlib.Analysis.Matrix.Order`). -/
theorem posSemidef_sqrt_mul_self {b : Mat d} (hb : b.PosSemidef) :
    CFC.sqrt b * CFC.sqrt b = b :=
  CFC.sqrt_mul_sqrt_self b hb.nonneg

/-- The square root of a block matrix is positive-semidefinite: `CFC.sqrt_nonneg`
is unconditional, so this holds whether or not `b` is symmetric
positive-semidefinite. -/
theorem posSemidef_sqrt_posSemidef (b : Mat d) : (CFC.sqrt b).PosSemidef :=
  (Matrix.nonneg_iff_posSemidef (A := CFC.sqrt b)).mp (CFC.sqrt_nonneg b)

/-- The square root of a block matrix is symmetric: `Matrix.PosSemidef` carries
the self-adjointness, and nonnegativity carries it to the square root. -/
theorem posSemidef_sqrt_isSymm (b : Mat d) : (CFC.sqrt b).IsSymm := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using
    (posSemidef_sqrt_posSemidef b).isHermitian

/-! ## The pointwise operator-norm bridge -/

/-- **`|b^{1/2} v|² = v · (b v)`** for a symmetric positive-semidefinite block
`b` and its square root `b^{1/2} = CFC.sqrt b`.  The left side is the quadratic
form of `b^{1/2}` at `v` (`vecNormSq` is the squared Euclidean norm of the
project's vectors); symmetry of `b^{1/2}` moves the second factor across, and
`CFC.sqrt_mul_sqrt_self` identifies the resulting quadratic form with that of
`b`. -/
theorem vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul {b : Mat d} (hb : b.PosSemidef)
    (v : Vec d) :
    vecNormSq (matVecMul (CFC.sqrt b) v) = vecDot v (matVecMul b v) := by
  show vecDot (matVecMul (CFC.sqrt b) v) (matVecMul (CFC.sqrt b) v) = _
  rw [vecDot_matVecMul_comm_of_isSymm (posSemidef_sqrt_isSymm b)
      (matVecMul (CFC.sqrt b) v) v,
    matVecMul_mul (CFC.sqrt b) (CFC.sqrt b) v, posSemidef_sqrt_mul_self hb]

/-- **`|b^{1/2} v|² ≤ |b| |v|²`**, the pointwise operator-norm bridge behind the
Hölder step of `e.bL.to.bhomell`: the quadratic form of the
square root of a symmetric positive-semidefinite block at `v` is bounded by the
Euclidean operator norm `|b|` of `b` times the squared norm of `v`. -/
theorem vecNormSq_sqrt_matVecMul_le {b : Mat d} (hb : b.PosSemidef) (v : Vec d) :
    vecNormSq (matVecMul (CFC.sqrt b) v) ≤
      matrixOperatorNorm b * vecNormSq v :=
  calc vecNormSq (matVecMul (CFC.sqrt b) v)
      = vecDot v (matVecMul b v) := vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul hb v
    _ ≤ matrixOperatorNorm b * vecNormSq v :=
        vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq_of_posSemidef hb v

/-! ## The `hbHalfLe`-shaped corollary -/

/-- The pointwise operator-norm bridge in the shape of the hypothesis `hbHalfLe`
of the display `e.bL.to.bhomell`:

```
∀ (omega : ShellSeq d) (z' z : TriadicCube d),
  bHalfW omega z' z ≤
    vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
      bLnorm omega z
```

with the coarse block and its square root made explicit:

* `bHalfW omega z' z := vecNormSq (matVecMul (CFC.sqrt (bBlock omega z))
    (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)))`, the
  squared norm of the square root of the coarse block `bBlock omega z` applied
  to the averaged gradient on the translated cube `z'`; and
* `bLnorm omega z := matrixOperatorNorm (bBlock omega z)`, the Euclidean
  operator norm of the coarse block on `z + cu_n`.

`U` is the domain of the field `w`, in the application
`openCubeSet (originCube d (S.m : ℤ))`.  With these two assignments the
conclusion below is *verbatim* the instantiated hypothesis `hbHalfLe`, so
`e.bL.to.bhomell` applies with it in that slot.  The hypothesis `hbHalfLe` puts the
scalar `bLnorm omega z` second, while the bridge above puts the operator norm
first; the two factors are commuted here. -/
theorem psdSqrtQuadratic_hbHalfLe (U : Set (Vec d))
    (bBlock : ShellSeq d → TriadicCube d → Mat d)
    (hbBlock : ∀ (omega : ShellSeq d) (z : TriadicCube d), (bBlock omega z).PosSemidef)
    (w : ShellSeq d → H10Function U)
    (omega : ShellSeq d) (z' z : TriadicCube d) :
    vecNormSq (matVecMul (CFC.sqrt (bBlock omega z))
        (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) ≤
      vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
        matrixOperatorNorm (bBlock omega z) := by
  rw [mul_comm]
  exact vecNormSq_sqrt_matVecMul_le (hbBlock omega z)
    (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))

end

end SuperdiffusionCLT.Section2.Localization