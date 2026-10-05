/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02.Theorems.DeterministicIdentities
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerBridges

/-!
# The bridge identity is a minimizer-attainment statement

The equality conjunct of each conjunct-3 averaging bridge reduces to the single scalar
identity for a coefficient field `a` on `U` at the loading `(p, q)`:

`⟨(-p,q), C_U(a)(-p,q)⟩ = 2 (⨍_U pointwiseResponse (a x) p q + p·q)`.

This module resolves what that identity *is*.  Averaging the pointwise block
matrix and using the linearity of the volume average in the block matrix shows
that the right-hand side is `2` times the doubled energy of the **constant**
block field `X₀ = (fun _ => -p, fun _ => q)`; the left-hand side is `2` times
`Mu` at `(-p, q)`.  Hence

`doubledMu U a (-p,q) = doubledMuValue U a X₀`,

i.e. the identity is exactly the statement that *the constant block field
attains the infimum* defining `Mu`.  Its first variation is therefore available.

The module defines the constant block field `constBlockState p q`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Section2.CoarseGraining
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The identity is attainment of the block infimum

The right-hand side of the scalar identity is the doubled energy of the
*constant* block field `X₀ = (fun _ => -p, fun _ => q)`; the left-hand side is
twice the coarse block quadratic, i.e. (by the Chapter 2 quadratic formula for
`Mu`) twice `Mu U (-p,q) a`.  The identity is therefore exactly the statement
that the constant field attains the infimum defining `Mu`. -/

/-- The constant block field with potential `-p` and flux `q`. -/
def constBlockState {d : ℕ} (p q : Vec d) : BlockState d :=
  { potential := fun _ => -p, flux := fun _ => q }

@[simp] theorem constBlockState_eval {d : ℕ} (p q : Vec d) (x : Vec d) :
    (constBlockState p q).eval x = (-p, q) := rfl

end

end SuperdiffusionCLT.Section2.Localization
