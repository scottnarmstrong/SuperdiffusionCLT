/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Response
public import Homogenization.Book.Ch05.Theorems.Section57.ScaleGeometry
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers

/-!
# `l.maximums.Gamma.s`, specialized to the near-scale descendant maximum

This module is one self-contained ingredient of the assembly of `srootE_mathcalE_bounds_of_inputs`'s
`hNear` binder (`Section4/MinimalScales/SkeletonMathcalE.lean`), which packages, among other
things, the near-scale sum-bound display `e.new.mixing.attempt.near` of the paper. It does
**not** prove `hNear`; it proves the index-set count for the application of Lemma
`l.maximums.Gamma.s` in the proof of `e.new.mixing.attempt.near`, "Since
`|(x+3^l Z^d) cap (x+cu_n)| <= C 3^{d(n-l)}` ... Lemma `l.maximums.Gamma.s` implies", to the
family `X_l = max_y max_{|eta|=1} bfJ(y+cu_l,...)`.

In the Lean carrier of `srootE_term` (`SkeletonMathcalE.lean`), `X_l` at depth `l` below `n` is
`Homogenization.maxDescendantNormalizedBlockResponseAtScale (originCube d n) (n - l) a a0`, a
finite maximum, over the depth-`l` descendant cubes `R` of `originCube d n`, of
`Homogenization.normalizedBlockResponseMax R a a0`. The index set is exactly
`Homogenization.descendantsAtScale (originCube d n) (n - l)`, whose cardinality is `(3^d)^l`
(`srootN_descendantsAtScale_card`, from `descendantsAtScale_originCube_nat_card`) --
the paper's `C 3^{d(n-l)}` bound, with the dimensional constant `C` sharpened to `1`. Given a
uniform per-cube `O_{Gamma_sigma}(A)` bound over this index set, Lemma `l.maximums.Gamma.s`
concludes the finite maximum itself is `O_{Gamma_sigma}` at the amplitude `(3 l d log 3)^{1/sigma}
A`, the paper's `(3 log N)^{1/sigma} A` read with `N = (3^d)^l`, i.e.
`log N = l d log 3`.

## Role in `hNear`

This is one ingredient of the "local base + tail comparison + l.maximums.Gamma.s" chain of
`p.new.mixing.attempt` (`e.new.mixing.attempt.near`). The other ingredients are the per-cube
amplitude `A` itself (from `hParam`, via the bridge
`Homogenization.Book.Ch02.doubledResponseJ_eq_BlockJ_of_isEllipticFieldOn` connecting
`doubledResponseJ` to `BlockJ`/`normalizedBlockResponseMax`), the tail-uniformity-in-`L` matrix
comparison (via `coarseBlockMatrix_localization` = `l.localization.A` and
`envelopeRescale_ellipticity` = `l.bfAm.ellip`), the weighted sum over
`l` (`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`, the Lean form of
`l.Gamma.sigma.triangle`), and the recentering to the fully centered field
(via `newMixParam_splitting_gaugeShift` (`Section4/NewMixing/Splitting.lean`) and
`e.jk.spatialavg`/`p.concentration`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization.IndependentSums

/-- The cardinality of the depth-`l` descendants of `originCube d n`, for `l ≤ n`, is `(3^d)^l` --
the paper's `C 3^{d(n-l)}` bound of `l.maximums.Gamma.s`, read with the depth
convention `l_lean = n_paper - l_paper` used by `srootE_term`, and with the dimensional constant `C`
sharpened to `1` (this is an exact count, not merely a bound). -/
theorem srootN_descendantsAtScale_card {d : ℕ} {n l : ℕ} (hln : l ≤ n) :
    (Homogenization.descendantsAtScale (Homogenization.originCube d (n : ℤ))
        ((n : ℤ) - (l : ℤ))).card = (3 ^ d) ^ l := by
  have hcast : (n : ℤ) - (l : ℤ) = ((n - l : ℕ) : ℤ) := (Nat.cast_sub hln).symm
  rw [hcast,
    Homogenization.Book.Ch05.Section57.descendantsAtScale_originCube_nat_card (Nat.sub_le n l)]
  congr 1
  omega

end SuperdiffusionCLT.Section4.MinimalScales
