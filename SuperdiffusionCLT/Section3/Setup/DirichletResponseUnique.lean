/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurability

/-!
# Existence of a responding family of Dirichlet responses

The paper defines `w` as *the* Dirichlet response of `e.def.w`.  The statements
of `l.LHS.term1` and `l.RHS.term3` instead bind `w` universally over *every*
realization of the defining predicate
(`_hw : ∀ omega, …IsDirichletResponse… (w omega)`), because the printed text
does not fix a particular response as a function: uniqueness and `H²` regularity
of the response are not part of the definition.

The Dirichlet problem itself is well posed: two responses of the same flux have
the same weak-gradient `L²(cu_m)` class (`isDirichletResponse_gradToVectorL2_eq`,
`gradToVectorL2_eq_of_isCubeDirichletResponse`), hence the same scalar `L²`
class, hence a.e. equal weak gradients.  The response is unique *as an element
of `L²(cu_m)`*, not as a function: the type `H10Function` carries no quotient,
so two responses may differ on a spatial null set, and it is exactly this
`L²`-level uniqueness that the two anchor displays require.

This module records the existence of a responding family, the witness that the anchors' `_hw`
binder is inhabited: `exists_dirichletResponse_family` realizes it by the canonical
`dirichletResponse`, which exists by `exists_isDirichletResponse`.

## What uniqueness does and does not give

Uniqueness is at the level of `L²(cu_m)` classes.  It does **not** by itself produce
measurability of `omega ↦ w omega`.  Since uniqueness holds only up to a spatial null set, a
selection may be altered on a null set of the cube at each sample; the map is determined only as
a map into the *class* space `L²(cu_m)`, and even the measurability of that class map is a
separate statement about the dependence of the solution on the sample.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The `IsDirichletResponse` family of the anchors -/

/-- **A responding family exists**, the witness that the anchors' `_hw` binder is
inhabited: `omega ↦ dirichletResponse omega LPrime ellPrime m p`. -/
theorem exists_dirichletResponse_family {LPrime ellPrime m : ℕ} {p : Vec d} :
    ∃ w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ))),
      ∀ omega, IsDirichletResponse omega LPrime ellPrime m p (w omega) :=
  ⟨fun omega => dirichletResponse omega LPrime ellPrime m p,
    fun omega => isDirichletResponse_dirichletResponse omega LPrime ellPrime m p⟩

end

end SuperdiffusionCLT.Section3.Setup
