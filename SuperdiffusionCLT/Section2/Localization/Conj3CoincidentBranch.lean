/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3Degenerate
public import SuperdiffusionCLT.Section2.Localization.TransposeMaximizer

/-!
# The coincident scale `m = L` split off from the third conjunct

`Frozen.Section2.cutoff_localization` quantifies its third conjunct
`e.localization.minimizers` over every `n ≤ m ≤ L`, so the coincident scale
`m = L` is admissible.  At `m = L` the centered field is the level-`L` cutoff
field (`centeredPairField_selfCoincident`), the shell increment
`finiteShellIncrement omega L L` vanishes, and a.e. gradient uniqueness makes
the two maximizers agree in gradient, so the conjunct's left side is `0` while
its window is also `0`: the conclusion is `0 ≤ 0` at every loading.

Every hypothesis written for the generic scale has broken there: the pointwise
gradient identity `hgrad` is refuted at `m = L` (`Conj3Hgrad`), the averaged
remainder `hrem` is false there for `p ≠ 0` (`AveragedRemainderProof`), and the
mean-slope input `hmean` needs its own coincident treatment.
This module isolates the degenerate scale once, so that every strict-scale
argument may be stated under `m < L` and never meets it.

## Results

* `cutoffLocalizationConjunct3_coincidentBranch`: the conjunct-3
  conclusion at `m = L`, verbatim, with the binders of the statement and `m = L` as the
  only hypotheses.  It restates `Conj3Degenerate`'s
  `cutoffLocalizationConjunct3_selfCoincident` in the shape of the statement
  (`[NeZero d]`, `2 ≤ d`); the coincident argument itself is that theorem's
  proof and consumes no `hgrad`/`hrem`/`hmean`.

Nothing in this module consumes a route hypothesis: the coincident branch is
`Conj3Degenerate`'s argument.  In particular no `hgrad`, `hrem` or `hmean` occurs in any
statement below.

The dimension binders `[NeZero d]` and `_hd : 2 ≤ d` record the range of the statement;
the arguments do not use them (they are uniform in `d`), and nothing dimension-one is asserted.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The coincident branch -/

/-- **The conjunct-3 conclusion at the coincident scale `m = L`.**  The
statement is the third conjunct of `Frozen.Section2.cutoff_localization`
(`e.localization.minimizers`) at its carriers, with the equation `m = L` adjoined and the
dimension range `[NeZero d]`, `2 ≤ d` recorded.  The `L^∞` window is
written through the carrier `anchorDerivSup`, definitionally the
supremum of the statement (`anchorDerivSup_eq`).

The proof is `Conj3Degenerate`'s coincident argument, unchanged: the two fields
coincide, a.e. gradient uniqueness zeroes the left side, the empty shell
interval zeroes the window, and `0 ≤ 0` holds for every constant.  In
particular no `hgrad`, `hrem` or `hmean` occurs anywhere in its hypotheses. -/
theorem cutoffLocalizationConjunct3_coincidentBranch
    (d : ℕ) [NeZero d] (_hd : 2 ≤ d)
    (C : ℝ) (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (m n L : ℕ) (hnm : n ≤ m) (hmL : m ≤ L) (hmL' : m = L)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (omega : ShellSeq d) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField
      (U : Set (Vec d)))
    (hu : ∀ w : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
        (U : Set (Vec d)),
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (centeredPairField nu omega m L (U : Set (Vec d))) p q w) ≤
        volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (centeredPairField nu omega m L (U : Set (Vec d))) p q u))
    (hv : ∀ w : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField
        (U : Set (Vec d)),
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField p q w) ≤
        volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField p q v)) :
    volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega *
        (ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) +
          ResponseJ (U : Set (Vec d)) p q
            (coefficientCutoff nu omega m).toCoeffField +
          2 * vecDot p q) :=
  cutoffLocalizationConjunct3_selfCoincident d C nu hnu hnu1 m n L hnm hmL hmL'
    U hU omega p q u v hu hv

/-! ## The case split: the deliverable -/

/-! ## The hypothesis sets are inhabited -/

end

end SuperdiffusionCLT.Section2.Localization
