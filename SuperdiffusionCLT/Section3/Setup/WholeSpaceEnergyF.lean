/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyE

/-!
# The geometric amplitude summation of `l.LHS.term1`

The step of the proof of `l.LHS.term1` in which the two per-shell displays are added over the
shells `ℓ' < r ≤ L'` and the resulting geometric series is summed, producing the
single amplitude `C|p|` of the display `e.wN.wD.with.average.error`.

The print writes the two per-shell amplitudes as

* `C|p| (m − r)^{1/10} 3^{−(m−r)/5}` for a shell `r < m`
  (the per-shell display of `WholeSpaceEnergyC.lean`), and
* `C|p| 3^{−(r−m)/5}` for a shell `r ≥ m`
  (the per-shell display of `WholeSpaceEnergyE.lean`),

and then says "summing over `r` gives `C|p|`".  That summation has two
ingredients.  The probabilistic one is the finite-family triangle inequality
for `Γ_σ` tails, `l.Gamma.sigma.triangle`, available as
`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`: the
sum of the per-shell observables has amplitude
`gammaTriangleConst 2 * Σ_r a_r`.  The arithmetic one is that `Σ_r a_r` is
bounded uniformly in the scale selection, which is what this file supplies.

Both series are dominated by a single geometric series.  Along the shells
`r ≥ m` the exponents `r − m` are distinct natural numbers, so the sum is at
most `Σ_{j ≥ 0} 3^{−j/5} = (1 − 3^{−1/5})⁻¹`.  Along the shells `r < m` the
exponents `m − r` are distinct positive natural numbers, and the polynomial
factor is absorbed by `k ≤ 3^k`, i.e. `k^{1/10} ≤ 3^{k/10}`, which turns the
summand into `3^{−k/10}`; the sum is then at most
`Σ_{k ≥ 0} 3^{−k/10} = (1 − 3^{−1/10})⁻¹`.  The series bound proved here is stated
over an arbitrary finite set of exponents, hence holds uniformly in the scale
selection — which is what `l_LHS_term1_constFirst` needs, since it produces
its constant before the scales.

## Main results

* `shellTailSeriesConst`, `shellPolyTailSeriesConst`: the two explicit series
  constants `(1 − 3^{−1/5})⁻¹` and `(1 − 3^{−1/10})⁻¹`.
* `sum_rpow_three_neg_div_five_le`: the uniform bound for the geometric series
  `Σ_j 3^{−j/5}` over an arbitrary finite set of exponents.
* `shellResponseGapConst_pos`, `shellResponseGapGeConst_pos`: positivity of the
  constants of the two per-shell displays.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two uniform series bounds -/

/-- The sum `Σ_{j ≥ 0} 3^{−j/5} = (1 − 3^{−1/5})⁻¹` of the geometric series
that bounds the shell amplitudes at the scales `r ≥ m`. -/
def shellTailSeriesConst : ℝ := (1 - (3 : ℝ) ^ (-(1 : ℝ) / 5))⁻¹

/-- The sum `Σ_{k ≥ 0} 3^{−k/10} = (1 − 3^{−1/10})⁻¹` of the geometric series
that bounds the shell amplitudes at the scales `r < m`, after the polynomial
factor `k^{1/10}` has been absorbed by `k ≤ 3^k`. -/
def shellPolyTailSeriesConst : ℝ := (1 - (3 : ℝ) ^ (-(1 : ℝ) / 10))⁻¹

private theorem rpow_neg_lt_one (c : ℝ) (hc : 0 < c) :
    (3 : ℝ) ^ (-c) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.2 hc)

theorem shellTailSeriesConst_pos : 0 < shellTailSeriesConst := by
  have h : (3 : ℝ) ^ (-(1 : ℝ) / 5) < 1 := by
    have := rpow_neg_lt_one ((1 : ℝ) / 5) (by norm_num)
    simpa only [show -((1 : ℝ) / 5) = -(1 : ℝ) / 5 by ring] using this
  rw [shellTailSeriesConst]
  exact inv_pos.2 (by linarith only [h])

theorem shellPolyTailSeriesConst_pos : 0 < shellPolyTailSeriesConst := by
  have h : (3 : ℝ) ^ (-(1 : ℝ) / 10) < 1 := by
    have := rpow_neg_lt_one ((1 : ℝ) / 10) (by norm_num)
    simpa only [show -((1 : ℝ) / 10) = -(1 : ℝ) / 10 by ring] using this
  rw [shellPolyTailSeriesConst]
  exact inv_pos.2 (by linarith only [h])

/-- **The geometric series `Σ_{j ≥ 0} 3^{−j/5}`**, bounded uniformly over an
arbitrary finite set of exponents — in particular over `Finset.range N`
uniformly in `N`, and over the exponents `r − m` produced by the shells
`m ≤ r ≤ L'` of any scale selection. -/
theorem sum_rpow_three_neg_div_five_le (s : Finset ℕ) :
    ∑ j ∈ s, (3 : ℝ) ^ (-((j : ℝ) / 5)) ≤ shellTailSeriesConst := by
  have hq0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 : ℝ) / 5) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : (3 : ℝ) ^ (-(1 : ℝ) / 5) < 1 := by
    have := rpow_neg_lt_one ((1 : ℝ) / 5) (by norm_num)
    simpa only [show -((1 : ℝ) / 5) = -(1 : ℝ) / 5 by ring] using this
  have hsum : Summable (fun j : ℕ => ((3 : ℝ) ^ (-(1 : ℝ) / 5)) ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have h := hsum.sum_le_tsum s (fun j _ => pow_nonneg hq0 j)
  rw [tsum_geometric_of_lt_one hq0 hq1] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 : ℝ) / 5)) j,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf

/-! ## Positivity of the per-shell constants -/

theorem shellResponseGapConst_pos {Cnd Chm Cl4 Cav : ℝ} (hCnd : 0 < Cnd)
    (hChm : 0 < Chm) (hCl4 : 0 < Cl4) (hCav : 0 < Cav) :
    0 < shellResponseGapConst Cnd Chm Cl4 Cav := by
  have h1 : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : (0 : ℝ) < orliczProductConst 10 (5 / 2) := orliczProductConst_pos _ _
  have h3 : (0 : ℝ) < Chm ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hChm _
  have h4 : (0 : ℝ) < Cl4 ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos hCl4 _
  rw [shellResponseGapConst]
  positivity

theorem shellResponseGapGeConst_pos {Cnd Chm Cl4 : ℝ} (hCnd : 0 < Cnd)
    (hChm : 0 < Chm) (hCl4 : 0 < Cl4) :
    0 < shellResponseGapGeConst Cnd Chm Cl4 := by
  have h2 : (0 : ℝ) < orliczProductConst 10 (5 / 2) := orliczProductConst_pos _ _
  have h3 : (0 : ℝ) < Chm ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hChm _
  have h4 : (0 : ℝ) < Cl4 ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos hCl4 _
  rw [shellResponseGapGeConst]
  positivity

end

end SuperdiffusionCLT.Section3.Setup
