/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgPremise
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PigRatioCloseB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3QuadZc
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditionsB

/-!
# `delta + etaL <= 1` at the printed carriers, and the residue that is left

The constant-first term-3 statement carries `delta`
and `etaL` as **free nonnegative reals** (`_hdelta`, `_hetaL` and nothing else),
so the numeric premise `delta + etaL <= 1` that the term-3 chain consumes
(`w_average_difference`) is not a consequence of
the binders of the statement at those free carriers: with `delta = etaL = 1` every
binder holds and the premise fails.

At the **printed carriers**, however, it is a consequence of printed conditions.
This file proves the scale facts used in that derivation.

## The printed conditions, and what each supplies

* The display `e.cstar.bound` of assumption `a.j.nondeg`
  (`\cstar \leq 2`): the upper bound on the non-degeneracy constant.  This is
  the datum named `CStarLeTwo` in `RHSTerm3CgPremise`, and it is not
  invented: `ShellLawJ5.cStar_le_two`
  derives exactly it from the paper's `a.j.nondeg` assumption.
* The statement of `p.sstar.lower.bound`
  (`C(d) \in [1,\infty)`, `c(d) \in (0,\nf12]`): the lower bound `1 <= CM` on the
  constant of the relative smallness.
* The `gathered` display in the proof of
  `p.sstar.lower.bound` (`C \delta^{\nf12} \leq \frac14\cstar`): the relative
  smallness, in the factored form `CM * Real.sqrt c0 <= 1 / 8` that the root
  of `p.sstar.lower.bound` carries.
* The same display (`\eta_L \leq L^{-1000}`): the localization
  defect.

`delta` and `etaL` are the paper's own carriers, `delta = c_0 \cstar^2` and
`\eta_L = C\eta \nu^{-5} L 3^{-(L'-m)}`, formalized as
`smallnessParameter c0 cStar` and
`localizationEta Ceta nu L (2 * a)` at the
printed gap `L' - m = 2a`.

## What the four conditions do not supply, and what the binders do

The chain `sqrt delta <= CM sqrt delta <= (1/8) * 2 = 1/4` (relative smallness,
`1 <= CM`, `c⋆ <= 2`)
gives `delta <= 1/16`, and `eta_L <= L^{-1000} <= 2^{-1000} <= 1/2`
(the defect bound) needs `L >= 2`; the two give `delta + eta_L <= 3/4 <= 1`.  Two
further inputs are needed and neither is one of the four conditions:

* **`hCT`**, the `e.L.vs.nu` threshold at its least admissible
  annealing constant: `4 * pigRatioCeta d CL <= nu^{-1} * S.L`.  The
  `localizationEta_le` consumes exactly it
  (the defect bound alone bounds `eta_L` by `Ceta nu^{-5} L`, which is unbounded in the
  free `Ceta`).  It is already carried by `_hPigRatio`'s residue, and it is not
  a consequence of the binders of the statement.
* **`2 <= S.L`**, which the four conditions do not give either — but which is
  **free** for the statement: `ScalesOrdering` orders the six scales
  `n < ell < ell' < m < L' < L`, so `L >= 5`.  Proved here as
  `two_le_SL_of_scalesOrdering`, this removes the hypothesis rather than
  carrying it.

The remaining scale inputs of the chain are free at these carriers as well:
`0 <= pigRatioCeta d CL` from `0 < CL` (`pigRatioCeta_nonneg`), the gate
`8056 <= pigRatioK * Real.log 3`, and
the offset largeness `pigRatioK * Real.log (nu^{-1} * S.L) <= S.a`, which is
**literally** the binder `_hOffsetLower` because `pigRatioK = 8056 / Real.log 3`.

## Main results

* `two_le_SL_of_scalesOrdering`, `five_le_SL_of_scalesOrdering` — `L >= 2` and
  `L >= 5` from `ScalesOrdering S`; the scale hypothesis of
  `localizationEta_le_half` is not carried.
* `pigRatioCeta_nonneg` — `0 <= pigRatioCeta d CL` from
  `0 <= CL`, so `_hCeta` is not carried either.
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
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## The scale hypothesis `2 <= S.L` is free for the statement -/

/-- **`L >= 5` from `ScalesOrdering S`.**  The ordering orders the
six scales `n < ell < ell' < m < L' < L`, and all six are natural numbers, so
`L >= 5`.  In particular the scale hypothesis `2 <= L` of
`localizationEta_le_half` (which the printed defect bound needs to turn
`L^{-1000}` into `1/2`) is not carried: it is a consequence of a binder the
statement already has. -/
theorem five_le_SL_of_scalesOrdering {S : ScaleSelection} (h : ScalesOrdering S) :
    5 ≤ S.L := by
  have h1 := h.n_lt_ell
  have h2 := h.ell_lt_ellPrime
  have h3 := h.ellPrime_lt_m
  have h4 := h.m_lt_LPrime
  have h5 := h.LPrime_lt_L
  omega

/-- **`L >= 2` from `ScalesOrdering S`**, the form the chain
consumes (`localizationEta_le_half`). -/
theorem two_le_SL_of_scalesOrdering {S : ScaleSelection} (h : ScalesOrdering S) :
    2 ≤ S.L :=
  le_trans (by norm_num) (five_le_SL_of_scalesOrdering h)

/-! ## `0 <= pigRatioCeta d CL` from `0 <= CL` -/

/-- **`0 <= pigRatioCeta d CL` from `0 <= CL`.** -/
theorem pigRatioCeta_nonneg (d : ℕ) {CL : ℝ} (hCL : 0 ≤ CL) : 0 ≤ pigRatioCeta d CL := by
  have h1 : 0 ≤ IndependentSums.gammaMomentConst 1 :=
    (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  have h2 : 0 ≤ (crudeLowerConst d)⁻¹ := (inv_pos.mpr (crudeLowerConst_pos d)).le
  exact mul_nonneg (mul_nonneg h1 hCL) h2

/-! ## The binder `_hOffsetLower` in the shape the chain consumes -/

/-! ## The premise at the printed carriers -/

/-! ## The premise fed to `_hPigRatio` -/

/-! ## The same premise from the relative smallness: `0 <= cStar` is derived, not carried -/

/-! ## `hCT` is not redundant: `CL` is left free, and the sum is unbounded in it -/

/-! ## Non-vacuity of the hypothesis set -/

end

end SuperdiffusionCLT.Section3.Terms
