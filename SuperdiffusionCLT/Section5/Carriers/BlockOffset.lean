/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Section2.StreamCutoff
public import Homogenization.CoarseGraining.OriginCubeOpenBridge
public import Homogenization.Sobolev.PotentialSolenoidalCubeBridge
public import Homogenization.CoarseGraining.ResponseIdentities.Existence
public import Homogenization.Geometry.CubeMeasure
public import Homogenization.Geometry.Translation
public import Homogenization.Geometry.TriadicPartition
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Block carriers of the localization lemma

The ordinary definitions of `lem.localization`: the flux `hshellFlux` of the shell field, the
gauge matrix `gaugeMat`, the action of `bfAhom^{-1/2}`, the slope `P_z` and the fluctuation `F_z`
on a subcube `z + cu_n`, and the class `F + (L²_{pot,0} × L²_{sol,0})(U)` with its energy
minimizers (`S_z`, `X_z`, `S̃_z`).

Subcubes `z + cu_n` with `z = 3^n k` are the triadic cubes `⟨n, k⟩`. The half-open convention of
`Homogenization.cubeSet` is used throughout, and `isBlockOffsetAdmissible_cubeSet_iff_openCubeSet`
transports the admissible class to the open cube.

Existence and uniqueness of the minimizers are in `Section5.Carriers.BlockOffsetMinimizer`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

variable {d : ℕ}

/-! ## Carriers -/

/-- `shom_{m-h}^{-1} (k_m - k_{m-h}) e`, the flux of `e.setup.w`. -/
noncomputable def hshellFlux [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e : Vec d) :
    Vec d → Vec d := fun x =>
  (sigmaBarInfinite nu (m - h) P)⁻¹ •
    matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m x -
      SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) x) e

/-- The gauge factorization matrix `G_{k0}` of `e.setup.G`. -/
def gaugeMat (k0 : Mat d) : BlockMat d :=
  { upperLeft := 1, upperRight := 0, lowerLeft := k0, lowerRight := 1 }

/-- `bfAhom_{m-h}^{-1/2}` applied to a block vector, `bfAhom = diag(shom Id, shom^{-1} Id)`. -/
noncomputable def ahomInvSqrtApply [NeZero d] (nu : ℝ) (L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (X : BlockVec d) : BlockVec d :=
  ((sigmaBarInfinite nu L P) ^ (-(1 : ℝ) / 2) • X.1,
    (sigmaBarInfinite nu L P) ^ ((1 : ℝ) / 2) • X.2)

/-- `P_z` of `e.setup.Pz` on the subcube `Q = z + cu_n`; `gD = ∇w_D`,
`gN = ∇w_N + shom^{-1} hshell e'`. -/
noncomputable def blockSlope [NeZero d] (nu : ℝ) (L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (Q : TriadicCube d) (e e' : Vec d) (gD gN : Vec d → Vec d) : BlockVec d :=
  ahomInvSqrtApply nu L P
    (e' + volumeAverageVec (cubeSet Q) gD, e + volumeAverageVec (cubeSet Q) gN)

/-- `F_z` of `e.setup.Fz`. -/
noncomputable def blockFluct [NeZero d] (nu : ℝ) (L : ℕ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (Q : TriadicCube d) (gD gN : Vec d → Vec d) : BlockState d where
  potential := fun x => (sigmaBarInfinite nu L P) ^ (-(1 : ℝ) / 2) •
    (gD x - volumeAverageVec (cubeSet Q) gD)
  flux := fun x => (sigmaBarInfinite nu L P) ^ ((1 : ℝ) / 2) •
    (gN x - volumeAverageVec (cubeSet Q) gN)

/-- The constant block state with value `P`. -/
def constBlockState (P : BlockVec d) : BlockState d where
  potential := fun _ => P.1
  flux := fun _ => P.2

/-- The class `F + (L²_{pot,0} × L²_{sol,0})(U)` with a non-constant offset `F`. -/
def IsBlockOffsetAdmissible (U : Set (Vec d)) (F X : BlockState d) : Prop :=
  MemVectorL2 U (fun x => X.potential x - F.potential x) ∧
    IsPotentialZeroTraceOn U (fun x => X.potential x - F.potential x) ∧
      MemVectorL2 U (fun x => X.flux x - F.flux x) ∧
        IsSolenoidalZeroNormalTraceOn U (fun x => X.flux x - F.flux x)

/-- Minimizer of `⨍_U ½ X·A X` over `IsBlockOffsetAdmissible U F` (`S_z`, `X_z`, `S̃_z`). -/
def IsBlockOffsetMinimizer (a : CoeffField d) (U : Set (Vec d)) (F X : BlockState d) : Prop :=
  IsBlockOffsetAdmissible U F X ∧
    ∀ Y : BlockState d, IsBlockOffsetAdmissible U F Y →
      volumeAverage U (blockEnergyDensity a X) ≤ volumeAverage U (blockEnergyDensity a Y)

/-! ## Basic API -/

/-- With a constant offset the class is the class of `Homogenization.IsBlockMuAdmissible`. -/
theorem isBlockOffsetAdmissible_constBlockState_iff (U : Set (Vec d)) (P : BlockVec d)
    (X : BlockState d) :
    IsBlockOffsetAdmissible U (constBlockState P) X ↔ IsBlockMuAdmissible U P X :=
  Iff.rfl

/-- `L²` membership on the half-open cube is `L²` membership on the open cube. -/
theorem memVectorL2_cubeSet_iff_openCubeSet (Q : TriadicCube d) (f : Vec d → Vec d) :
    MemVectorL2 (cubeSet Q) f ↔ MemVectorL2 (openCubeSet Q) f := by
  simp only [MemVectorL2, volumeMeasureOn,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]

/-- The admissible class on the half-open cube is the class on the open cube. -/
theorem isBlockOffsetAdmissible_cubeSet_iff_openCubeSet [NeZero d] (Q : TriadicCube d)
    (F X : BlockState d) :
    IsBlockOffsetAdmissible (cubeSet Q) F X ↔ IsBlockOffsetAdmissible (openCubeSet Q) F X := by
  rw [IsBlockOffsetAdmissible, IsBlockOffsetAdmissible, memVectorL2_cubeSet_iff_openCubeSet,
    memVectorL2_cubeSet_iff_openCubeSet]
  exact and_congr Iff.rfl (and_congr
    ⟨isPotentialZeroTraceOn_openCubeSet_triadicCube_of_cubeSet,
      isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet⟩
    (and_congr Iff.rfl
      ⟨isSolenoidalZeroNormalTraceOn_openCubeSet_triadicCube_of_cubeSet,
        isSolenoidalZeroNormalTraceOn_cubeSet_triadicCube_of_openCubeSet⟩))

/-- The minimizer property on the half-open cube is the one on the open cube. -/
theorem isBlockOffsetMinimizer_cubeSet_iff_openCubeSet [NeZero d] (Q : TriadicCube d)
    (a : CoeffField d) (F X : BlockState d) :
    IsBlockOffsetMinimizer a (cubeSet Q) F X ↔ IsBlockOffsetMinimizer a (openCubeSet Q) F X := by
  have hv : ∀ f : Vec d → ℝ,
      volumeAverage (cubeSet Q) f = volumeAverage (openCubeSet Q) f := fun f =>
    ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q f
  simp only [IsBlockOffsetMinimizer, isBlockOffsetAdmissible_cubeSet_iff_openCubeSet, hv]

end SuperdiffusionCLT.Section5
