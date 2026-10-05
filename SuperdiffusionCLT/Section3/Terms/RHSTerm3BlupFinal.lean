/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BlupRemainderFinal
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3QuadZc
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditionsB

/-!
# The scale bookkeeping of the `_hBlup` witness (`e.blupbounds.remainder`)

The statement is `e.blupbounds` of the paper.  The obligation `_hBlup` of the term-3 assembly
is the printed remainder witness of `e.blupbounds` at `ep = 1` on the translated cubes, in
the `∃ Zrem` shape with four conjuncts: measurability of `Zrem · z` in the shell sequence,
the printed `Γ_{1/3}` tail at the amplitude `Czero ν^{-3} L' 3^{-(ℓ-n)}`, the tested pointwise
display `|b_{L'} − b_ℓ| ≤ 1 |b_ℓ| + 2 q(e) + Zrem` with
`q(e) = translatedStreamQuadFormLower nu ℓ L' e`, and integrability of the `∇w`-weighted
double lattice average of `Zrem`.

This module records the scale bookkeeping that the packaging of the four conjuncts at the
concrete witness `blupRemainderZrem` (`Section3/Terms/BlupRemainderAssembly.lean`) uses.

## Main results

* `blup_scales_of_ordering`: the localization scales satisfy `n < ℓ < L'` and the
  intermediate coarse scale lies between `n` and `m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

variable {d : ℕ}

noncomputable section

/-! ## The scale bookkeeping of the localization witness -/

/-- The ordering data of `hSorder` in the form the witness consumes: the
localization scales satisfy `n < ℓ < L'` and the intermediate coarse scale `k`
lies between `n` and `m`. -/
theorem blup_scales_of_ordering (d : ℕ) {S : ScaleSelection} (hSorder : ScalesOrdering S) :
    S.n < S.ell ∧ S.ell < S.LPrime ∧
      S.n ≤ coarseBlockScale d S ∧ coarseBlockScale d S ≤ S.m := by
  have hellP : S.ell ≤ S.ellPrime := le_of_lt hSorder.ell_lt_ellPrime
  have hlL : S.ell < S.LPrime :=
    lt_trans hSorder.ell_lt_ellPrime
      (lt_trans hSorder.ellPrime_lt_m hSorder.m_lt_LPrime)
  obtain ⟨hlk, hkl, -, -⟩ := coarse_block_scale_choice d S hellP
  exact ⟨hSorder.n_lt_ell, hlL, le_trans (le_of_lt hSorder.n_lt_ell) hlk,
    le_trans hkl (le_of_lt hSorder.ellPrime_lt_m)⟩

end

end SuperdiffusionCLT.Section3.Terms
