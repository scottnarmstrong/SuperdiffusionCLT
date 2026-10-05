/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.BlockPotentialCorrector

@[expose] public section

open Homogenization MeasureTheory

/-- Marginal J5: there are positive constants `cStar`
and `K` such that, for every finite block of shells `(n, m]` and every unit
direction `e`, the energy of the stationary response
`grad Delta⁻¹ (div (sum of the block shells applied to e))` at the spatial
origin differs from `cStar (log 3) (m - n)` by at most `K`. The stationarity and
`L²` inputs consumed by the response are derived from the prefix, J2 and J3, not
added as J5 hypotheses. -/
structure SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d))
    (cStar K : ℝ)
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) : Prop where
  cStar_pos : 0 < cStar
  K_pos : 0 < K
  nondegenerate : ∀ (n m : ℕ), n < m →
    ∀ (e : Homogenization.Vec d)
      (he : Homogenization.Book.Ch02.vecNorm e = 1),
      |‖SuperdiffusionCLT.Section2.Cutoff.blockPotentialResponse P n m
              (SuperdiffusionCLT.Section2.Cutoff.blockRegLaw_stationary
                hPrefix hJ2 n m)
              e
              (SuperdiffusionCLT.Section2.Cutoff.memLp_originForcing_blockRegLaw
                hJ3 n m e he)‖ ^ 2 -
          cStar * Real.log 3 * ((m - n : ℕ) : ℝ)| ≤ K
