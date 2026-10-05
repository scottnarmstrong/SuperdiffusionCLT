/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SublatticeIndependence

/-!
# The colour partition of a printed sublattice subcollection

`SuperdiffusionCLT.Section3.Terms.SublatticeIndependence` restates the sublattice
independence rule `hpair`/`hmem` at one printed subcollection, `subcollectionAtDepth R t c`: one
colour class of `ShellField.cubeShellColor` inside the depth-`t` descendants of a parent cube `R`.

The printed decomposition

`∑_{z ∈ 3^n ℤ^d ∩ cu_m} X_z = ∑_{y ∈ 3^n ℤ^d ∩ cu_{n+1}} ∑_{z ∈ 3^{n+1} ℤ^d ∩ cu_m} X_{y+z}`

splits the whole block family `descendantsAtDepth R t` into `3 ^ d` subcollections.  This file
shows that the colour classes form a partition of that family, with a bound on the number of
classes that does not depend on the scale.

## Main results

* `shellColorSet`, `biUnion_subcollectionAtDepth`, `disjoint_subcollectionAtDepth_of_ne`: the
  colour classes cover the descendant family and are pairwise disjoint;
* `card_shellColorSet_le`: at most `(Nat.sqrt d + 2) ^ d` classes, a bound free of the ambient
  scale — the number of subcollections, unlike the `m`-dependent modulus `3 ^ m * d + 1` of the
  descendant colouring.

At colour period `3` (that is, `d ≤ 3`, where `ShellField.shellColorPeriod d = Nat.sqrt d + 2`
equals `3`) the colouring is the printed period-`3` partition; for `d ≥ 4` the period exceeds
`3` and a printed subcollection need not be a single colour class.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## The colour partition of one descendant family -/

/-- The colours realised by the depth-`t` descendants of `R`: the image of the
`ShellField.cubeShellColor` colouring on that family. -/
def shellColorSet (R : TriadicCube d) (t : ℕ) : Finset (ShellField.ShellCubeColor d) :=
  (descendantsAtDepth R t).image ShellField.cubeShellColor

/-- The colour classes cover the whole descendant family: the printed
decomposition into subcollections is a partition of the block family. -/
theorem biUnion_subcollectionAtDepth (R : TriadicCube d) (t : ℕ) :
    (shellColorSet R t).biUnion (subcollectionAtDepth R t) = descendantsAtDepth R t :=
  Finset.image_biUnion_filter_eq _ _

/-- Distinct colours give disjoint classes: no block lies in two printed
subcollections. -/
theorem disjoint_subcollectionAtDepth_of_ne {R : TriadicCube d} {t : ℕ}
    {c₁ c₂ : ShellField.ShellCubeColor d} (hne : c₁ ≠ c₂) :
    Disjoint (subcollectionAtDepth R t c₁) (subcollectionAtDepth R t c₂) := by
  rw [Finset.disjoint_left]
  intro B hB₁ hB₂
  rw [mem_subcollectionAtDepth] at hB₁ hB₂
  exact hne (hB₁.2.symm.trans hB₂.2)

/-! ## The number of colour classes -/

/-- **The printed number of subcollections is `(Nat.sqrt d + 2) ^ d`, free of the
ambient scale.**  The colouring has a fixed, `h`- and `n`-independent type,
so the number of classes never depends on the shell scale, unlike the modulus
`3 ^ m * d + 1` of the descendant colouring. -/
theorem card_shellColorSet_le (R : TriadicCube d) (t : ℕ) :
    (shellColorSet R t).card ≤ (ShellField.shellColorPeriod d) ^ d := by
  classical
  calc (shellColorSet R t).card
      ≤ (Finset.univ : Finset (ShellField.ShellCubeColor d)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = (ShellField.shellColorPeriod d) ^ d := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

end

end SuperdiffusionCLT.Section3.Terms
