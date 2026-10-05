/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.J3DerivativeAPI

/-!
# The `L∞(U)` derivative norm of one shell on an arbitrary set

The paper writes the hypothesis of the
cutoff approximation lemma `l.cutoff.approximation` as

> `∑_{k=0}^∞ ‖∇ j_k‖_{L∞(U)} < ∞`

for a bounded domain `U`. This module supplies the carrier
`shellDerivLinftyNorm U j` for the single term `‖∇ j‖_{L∞(U)}`: the exact
supremum, over the points of `U`, of the induced `vecNorm → matrixOperatorNorm`
norm of the derivative stored in the shell `j`.

The definition is the exact generalization, from the natural open cube `cu_n`
to an arbitrary set `U`, of the cube carrier
`SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellCubeDerivNorm`
(`Assumptions/ShellField/J3Observable.lean`), and it uses the same device: the
supremum is taken over the range of a function on `Option {x // x ∈ U}` whose
`none` branch is the explicit value `0`, so the set is nonempty in every
dimension and for every `U`, including `U = ∅` and `d = 0`.

## The value on an unbounded set

`Real.sSup` of a set that is not bounded above is the junk value `0`
(`Real.sSup_of_not_bddAbove`), so on a set `U` on which `∇ j` is unbounded the
carrier returns `0`. The branch is unreachable on a bounded `U`: the stored
derivative `ShellField.deriv j` is a continuous map, the closure of a bounded
subset of `Vec d` is compact, and `bddAbove_range_shellDerivAtIndex` turns this
into the boundedness of the defining range. Every consumer of this carrier
quantifies over bounded domains, where `le_shellDerivLinftyNorm` and
`shellDerivLinftyNorm_le` together say that the value is the genuine
supremum.

## Main definitions

* `shellDerivAtIndex`: the defining family of values.
* `shellDerivLinftyNorm`: `‖∇ j‖_{L∞(U)}`, the supremum of that family.

## Main results

* `shellDerivLinftyNorm_nonneg`: nonnegativity, valid for every `U`.
* `le_shellDerivLinftyNorm`: on a bounded `U`, the value dominates every
  pointwise derivative norm on `U`.
* `shellDerivLinftyNorm_le`: it is the least such nonnegative bound.
* `shellDerivLinftyNorm_mono`: monotone in `U` under a bounded ambient set.
* `shellDerivLinftyNorm_openCubeSet`: it agrees with the cube carrier
  `shellCubeDerivNorm` on the natural open cube `cu_n`.
* `shellDerivLinftyNorm_empty`: the degenerate value on the empty set.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Carriers

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}

/-- Values of the induced derivative norm on `U`, with the explicit zero of the
`none` branch.  The `Option` index makes the defining range nonempty for every
`U` and every `d`. -/
def shellDerivAtIndex (U : Set (Vec d)) (j : ShellField d) :
    Option {x : Vec d // x ∈ U} → ℝ
  | none => 0
  | some x => matrixDerivativeNorm (ShellField.deriv j x.1)

/-- The `L∞(U)` norm `‖∇ j‖_{L∞(U)}` of the derivative stored in the shell `j`,
the single term of the summability hypothesis of
`l.cutoff.approximation`. -/
def shellDerivLinftyNorm (U : Set (Vec d)) (j : ShellField d) : ℝ :=
  sSup (Set.range (shellDerivAtIndex U j))

/-- The defining range always contains `0`. -/
private theorem zero_mem_range_shellDerivAtIndex (U : Set (Vec d))
    (j : ShellField d) :
    (0 : ℝ) ∈ Set.range (shellDerivAtIndex U j) :=
  ⟨none, rfl⟩

/-- **The defining range is bounded above on a bounded set.** The stored
derivative is continuous and the closure of a bounded subset of `Vec d` is
compact. -/
theorem bddAbove_range_shellDerivAtIndex {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (j : ShellField d) :
    BddAbove (Set.range (shellDerivAtIndex U j)) := by
  have hcont : Continuous
      (fun x : Vec d => matrixDerivativeNorm (ShellField.deriv j x)) :=
    matrixDerivativeNorm_continuous.comp (ShellField.deriv j).continuous
  obtain ⟨C, hC⟩ :=
    hU.isCompact_closure.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left 0 C
  | some x =>
      have hx : x.1 ∈ closure U := subset_closure x.2
      have hle : matrixDerivativeNorm (ShellField.deriv j x.1) ≤ C := by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (matrixDerivativeNorm_nonneg _)] using hC x.1 hx
      exact hle.trans (le_max_right 0 C)

/-- The carrier is nonnegative for every set, the junk branch included. -/
theorem shellDerivLinftyNorm_nonneg (U : Set (Vec d)) (j : ShellField d) :
    0 ≤ shellDerivLinftyNorm U j := by
  by_cases hb : BddAbove (Set.range (shellDerivAtIndex U j))
  · exact le_csSup hb (zero_mem_range_shellDerivAtIndex U j)
  · rw [shellDerivLinftyNorm, Real.sSup_of_not_bddAbove hb]

/-- **On a bounded set the carrier dominates every pointwise derivative
norm.** -/
theorem le_shellDerivLinftyNorm {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (j : ShellField d) {x : Vec d} (hx : x ∈ U) :
    matrixDerivativeNorm (ShellField.deriv j x) ≤ shellDerivLinftyNorm U j :=
  le_csSup (bddAbove_range_shellDerivAtIndex hU j) ⟨some ⟨x, hx⟩, rfl⟩

/-- **Any nonnegative bound valid on `U` bounds the carrier.** No hypothesis on
`U` is needed: the defining range is nonempty. -/
theorem shellDerivLinftyNorm_le {U : Set (Vec d)} {j : ShellField d} {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x ∈ U, matrixDerivativeNorm (ShellField.deriv j x) ≤ C) :
    shellDerivLinftyNorm U j ≤ C := by
  refine csSup_le (Set.range_nonempty (shellDerivAtIndex U j)) ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact hC
  | some x => exact h x.1 x.2

/-- **Monotonicity in the set**, on a bounded ambient set. -/
theorem shellDerivLinftyNorm_mono {U V : Set (Vec d)}
    (hV : Bornology.IsBounded V) (hUV : U ⊆ V) (j : ShellField d) :
    shellDerivLinftyNorm U j ≤ shellDerivLinftyNorm V j :=
  shellDerivLinftyNorm_le (shellDerivLinftyNorm_nonneg V j)
    fun _ hx => le_shellDerivLinftyNorm hV j (hUV hx)

/-- The natural open manuscript cube is bounded. -/
theorem isBounded_openCubeSet_originCube (n : ℤ) :
    Bornology.IsBounded (openCubeSet (originCube d n)) := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  exact Metric.isBounded_ball

/-- **The carrier agrees with the cube carrier on `cu_n`.** -/
theorem shellDerivLinftyNorm_openCubeSet (n : ℕ) (j : ShellField d) :
    shellDerivLinftyNorm (openCubeSet (originCube d (n : ℤ))) j =
      shellCubeDerivNorm n j := by
  refine le_antisymm ?_ ?_
  · refine shellDerivLinftyNorm_le (shellCubeDerivNorm_nonneg n j) ?_
    intro x hx
    exact matrixDerivativeNorm_deriv_le_shellCubeDerivNorm n j hx
  · refine (shellCubeDerivNorm_le_iff n j _).2
      ⟨shellDerivLinftyNorm_nonneg _ j, ?_⟩
    intro x
    exact le_shellDerivLinftyNorm (isBounded_openCubeSet_originCube (n : ℤ)) j
      x.2

/-- The carrier on the empty set is zero. -/
@[simp]
theorem shellDerivLinftyNorm_empty (j : ShellField d) :
    shellDerivLinftyNorm (∅ : Set (Vec d)) j = 0 := by
  refine le_antisymm (shellDerivLinftyNorm_le le_rfl ?_)
    (shellDerivLinftyNorm_nonneg _ j)
  intro x hx
  exact absurd hx (Set.notMem_empty x)

end

end SuperdiffusionCLT.Section2.Carriers
