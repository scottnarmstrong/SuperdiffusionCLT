/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Prereq.Domains
public import SuperdiffusionCLT.Section6.Prereq.FullField

/-!
# Statement carriers for the Dirichlet homogenization theorems

The Dirichlet problem with `H¹` boundary data, translated triadic cubes, the Whitney interior of
a dilated domain, the `H^{-1}` seminorm of a vector field, and the rescaled coefficient fields
`ν Id + k(·/ε)` and `ν Id + k(·/ε) - (k(·/ε))_U` for the recentered stream matrix.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- `u ∈ H¹(U)` solves `-∇·(a∇u) = f` in `U` with `u = g` on `∂U`: the weak equation tested
against `H¹₀(U)`, and `u - g ∈ H¹₀(U)`. -/
def IsDirichletSolution (a : CoeffField d) (U : Set (Vec d)) (f : Vec d → ℝ)
    (g u : H1Function U) : Prop :=
  IsWeakSolutionOn a U u f (fun _ => 0) ∧ MemH10 U (fun x => u.toFun x - g.toFun x)

/-- The translated open triadic cube `y + cu_m`. -/
def shiftCube (y : Vec d) (m : ℤ) : Set (Vec d) :=
  (fun x => y + x) '' openCubeSet (originCube d m)

/-- The union of the grid cubes `z + cu_j`, `z ∈ 3^j ℤ^d ∩ V`, with `z + cu_{j+3} ⊆ V`
(the set `U_int` of `l.Dirichlet.Whitney.Poincare`, at the scale of `V`). -/
def whitneyInterior (V : Set (Vec d)) (j : ℤ) : Set (Vec d) :=
  ⋃ k : Fin d → ℤ,
    ⋃ (_ : (fun i => (3 : ℝ) ^ j * (k i : ℝ)) ∈ V ∧
        shiftCube (fun i => (3 : ℝ) ^ j * (k i : ℝ)) (j + 3) ⊆ V),
      (fun x => (fun i => (3 : ℝ) ^ j * (k i : ℝ)) + x) '' cubeSet (originCube d j)

/-- The `H^{-1}(U)` seminorm of a vector field: the sum over components of the normalized dual
seminorm `wMinusOneBar U 2`. -/
noncomputable def hMinusOneVec (U : Set (Vec d)) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ i : Fin d, wMinusOneBar U 2 (fun x => F x i)

/-- `a^ε(x) = ν Id + (k - k(0))(x/ε)`. -/
noncomputable def epField (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (ε : ℝ) : CoeffField d :=
  fun x => SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega (ε⁻¹ • x)

/-- `ν Id + k^ε - (k^ε)_U`, with `k^ε(x) = (k - k(0))(x/ε)` and the entrywise average over
`U`. -/
noncomputable def epFieldCentered (nu : ℝ)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (ε : ℝ) (U : Set (Vec d)) :
    CoeffField d :=
  fun x => epField nu omega ε x -
    Matrix.of fun i j =>
      ⨍ y in U, SuperdiffusionCLT.Section6.fullStreamRecentered omega (ε⁻¹ • y) i j

end SuperdiffusionCLT.Section7
