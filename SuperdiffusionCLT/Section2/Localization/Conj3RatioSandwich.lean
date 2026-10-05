/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedRoute
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerBridges

/-!
# The pointwise coefficient-ratio sandwiches of the cutoff pair

`Conj3AveragedRouteData` (`Conj3AveragedRoute.lean`) carries two pointwise
coefficient-ratio sandwiches, `hratioA` and `hratioAt`:

`⟨W, 𝐀(A x) W⟩ ≤ ⟨W, 𝐀(At x) W⟩ + η ⟨W, 𝐀(At x) W⟩`, and conversely,

where `𝐀(A x)` is the block matrix of the coefficient `A x`.  They are
hypotheses of the averaged route and, at the cutoff carriers
`A = a_m` (`coefficientCutoff nu omega m`) and
`At = â` (`centeredPairField nu omega m L U`), they are **not** extra analytic
input: the two fields have symmetric part exactly `ν Id`
(`symmPart_coefficientCutoff`, `symmPart_centeredPairField_eq_smul_one`) and their
increment is skew (`finiteShellIncrement_skew`), so the block form separates and
the sandwich is exactly an operator-norm condition on the skew increment.  This
module proves the sandwiches at the cutoff carriers with the explicit constant
`cutoffPairEtaWindow d nu n m L omega`.

## Main results

* `hratioA_centeredCutoffPair_window`, `hratioAt_centeredCutoffPair_window`: the two
  sandwiches at the cutoff pair in the exact shape the route consumes, with the explicit
  constant `cutoffPairEtaWindow`, from the construction-level window bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The two sandwiches at the cutoff pair -/

/-- **`hratioA` at the cutoff pair, at the window amplitude.**  For the
level-`m` cutoff `A = a_m = coefficientCutoff nu omega m` and the centered pair
`At = â = centeredPairField nu omega m L U`, the block form of `A` is dominated
by that of `At` with relative amplitude `cutoffPairEtaWindow d nu n m L omega`,
uniformly over `U` and over all block vectors `W`.  This is the first conjunct of
the construction-level `blockQuadraticSandwich_centeredCutoffPair_window`, read
in the route's `averagedBlockQuadratic` notation; it is exactly the `hratioA`
field of `Conj3AveragedRouteData` at these two fields. -/
theorem hratioA_centeredCutoffPair_window
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d)
    (n m L : ℕ) (hmL : m ≤ L)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) :
    ∀ x ∈ (U : Set (Vec d)), ∀ W : BlockVec d,
      averagedBlockQuadratic ((coefficientCutoff nu omega m).toCoeffField x) W ≤
        averagedBlockQuadratic (centeredPairField nu omega m L (U : Set (Vec d)) x) W +
          cutoffPairEtaWindow d nu n m L omega *
            averagedBlockQuadratic (centeredPairField nu omega m L (U : Set (Vec d)) x) W :=
  fun x hx W =>
    (blockQuadraticSandwich_centeredCutoffPair_window U nu hnu omega n m L hmL hU x hx).1 W

/-- **`hratioAt` at the cutoff pair, at the window amplitude.**  The
converse domination, with the same constant `cutoffPairEtaWindow d nu n m L
omega`: the block form of the centered pair `â` is dominated by that of the
level-`m` cutoff `a_m`.  This is the second conjunct of
`blockQuadraticSandwich_centeredCutoffPair_window`, and it is exactly the
`hratioAt` field of `Conj3AveragedRouteData` at these two fields. -/
theorem hratioAt_centeredCutoffPair_window
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d)
    (n m L : ℕ) (hmL : m ≤ L)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) :
    ∀ x ∈ (U : Set (Vec d)), ∀ W : BlockVec d,
      averagedBlockQuadratic (centeredPairField nu omega m L (U : Set (Vec d)) x) W ≤
        averagedBlockQuadratic ((coefficientCutoff nu omega m).toCoeffField x) W +
          cutoffPairEtaWindow d nu n m L omega *
            averagedBlockQuadratic ((coefficientCutoff nu omega m).toCoeffField x) W :=
  fun x hx W =>
    (blockQuadraticSandwich_centeredCutoffPair_window U nu hnu omega n m L hmL hU x hx).2 W

end

end SuperdiffusionCLT.Section2.Localization
