/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.Triangle

/-!
# The generalized triangle inequality for `O_{Γ_σ}` at `σ ≥ 1`

This module records the `σ ≥ 1` half of the manuscript's Lemma
`l.Gamma.sigma.triangle`, whose display
`e.Gamma.sigma.triangle` reads: for a nonnegative summable
sequence `{a_k}` and random variables `X_k = O_{Γ_σ}(a_k)`,

`∑_k X_k ≤ O_{Γ_σ}((1 + C σ⁻¹ 1_{σ < 1}) ∑_k a_k)`.

Here `X ≤ O_Ψ(A)` is the tail relation `P[X > t A] ≤ Ψ(t)⁻¹` for `t ∈ [1, ∞)`
and `Γ_σ(t) = exp(t ^ σ)`.

## What is proved here, and what is not

The printed proof splits at `σ = 1`: "The inequality for `σ ≥ 1` is
proved in `[AKMBook, Lemma A.4]`", and only the range `0 < σ < 1` is argued in
the manuscript. For `σ ≥ 1` the printed prefactor `1 + C σ⁻¹ 1_{σ < 1}` equals
`1` exactly, so the printed `σ ≥ 1` statement is the sum rule *with prefactor
one*. That prefactor-one statement is the external input
`ext.AKMBook.triangle.sigma.at.least.one`; it is **not** proved here and it is
**not** available upstream.

What the upstream library provides is the same finite-family sum rule with an
explicit prefactor: `Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`
gives,
for `0 < σ`, a nonempty `Finset s`, positive amplitudes `a i` and measurable
`X i` with `X i = O_{Γ_σ}(a i)`,

`∑_{i ∈ s} X i = O_{Γ_σ}(gammaTriangleConst σ * ∑_{i ∈ s} a i)`,

with `gammaTriangleConst σ = 4 * gammaGrowthConst σ ^ (12 : ℝ)` and
`gammaGrowthConst σ = max 2 ((1 + σ⁻¹) ^ σ⁻¹)`
(in the same library). Its prefactor is
therefore `16384`, not `1`.

Consequently this module proves the following, and claims nothing more: on the
manuscript's range `σ ≥ 1` the upstream prefactor collapses to the single
universal number `16384`, independent of `σ`, so the finite-sum instance of the
printed display holds on that range with a universal constant in place of the
printed constant `1`. The gap between `16384` and the printed `1` is exactly
the external node `ext.AKMBook.triangle.sigma.at.least.one`; a consumer needing
the printed constant must take that node as an assumption.

The manuscript's infinite sum over `k ∈ ℕ` is obtained in the printed proof by
passing to the limit over partial sums; only the finite-sum step is
treated here, over an arbitrary `Finset` and, in the manuscript's own indexing,
over `Fin N`.

## Main results

* `gammaGrowthConst_eq_two_of_one_le`: `gammaGrowthConst σ = 2` for `1 ≤ σ`.
* `gammaTriangleConst_eq_of_one_le`: the upstream prefactor is the universal
  number `16384` on the manuscript's range `σ ≥ 1`.
* `isBigO_gammaSigma_finset_sum_of_one_le`: the finite-sum instance of the
  printed display `e.Gamma.sigma.triangle` for `σ ≥ 1`, over a `Finset`, with
  amplitude `16384 * ∑ a`.
* `isBigO_gammaSigma_finSum_of_one_le`: the same in the manuscript's indexing
  `X_1, …, X_N`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory
open Homogenization

variable {Omega : Type*} [MeasurableSpace Omega]

/-- On the manuscript's range `σ ≥ 1` the upstream growth constant
`gammaGrowthConst σ = max 2 ((1 + σ⁻¹) ^ σ⁻¹)` equals `2`: the second entry of
the maximum is at most `1 + σ⁻¹ ≤ 2` because the exponent `σ⁻¹` is at most `1`
and the base is at least `1`. -/
theorem gammaGrowthConst_eq_two_of_one_le {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    IndependentSums.gammaGrowthConst sigma = 2 := by
  have hpos : (0 : ℝ) < sigma := lt_of_lt_of_le zero_lt_one hsigma
  have hinvpos : (0 : ℝ) < sigma⁻¹ := inv_pos.2 hpos
  have hinv : sigma⁻¹ ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hsigma hinvpos.le
    rwa [mul_one, inv_mul_cancel₀ (ne_of_gt hpos)] at hmul
  have hbase : (1 : ℝ) ≤ 1 + sigma⁻¹ := by linarith only [hinvpos]
  have hstep : (1 + sigma⁻¹) ^ sigma⁻¹ ≤ 1 + sigma⁻¹ := by
    have := Real.rpow_le_rpow_of_exponent_le hbase hinv
    rwa [Real.rpow_one] at this
  have hle : (1 + sigma⁻¹) ^ sigma⁻¹ ≤ 2 := by linarith only [hstep, hinv]
  simp only [IndependentSums.gammaGrowthConst]
  exact max_eq_left hle

/-- On the manuscript's range `σ ≥ 1` the upstream triangle prefactor
`gammaTriangleConst σ = 4 * gammaGrowthConst σ ^ (12 : ℝ)` is the single
universal number `16384`, with no dependence on `σ`. This is the sense in
which the upstream sum rule is uniform on the range where the printed display
`e.Gamma.sigma.triangle` has prefactor `1`; the two constants are
not the same, and the printed value `1` is the external input
`ext.AKMBook.triangle.sigma.at.least.one`. -/
theorem gammaTriangleConst_eq_of_one_le {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    IndependentSums.gammaTriangleConst sigma = 16384 := by
  have hpow : (2 : ℝ) ^ (12 : ℝ) = 4096 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  simp only [IndependentSums.gammaTriangleConst,
    gammaGrowthConst_eq_two_of_one_le hsigma, hpow]
  norm_num

/-- The finite-sum instance of the printed display `e.Gamma.sigma.triangle` on the manuscript's
range `σ ≥ 1`, over an arbitrary nonempty `Finset` of indices: if
`X i = O_{Γ_σ}(a i)` for each `i ∈ s`, then

`∑_{i ∈ s} X i = O_{Γ_σ}(16384 * ∑_{i ∈ s} a i)`.

This is `Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`
with its prefactor evaluated by `gammaTriangleConst_eq_of_one_le`. The printed
prefactor on this range is `1`; the value `16384` here is what the upstream
proof yields, and the improvement to `1` is the external node
`ext.AKMBook.triangle.sigma.at.least.one`, which is not used and not proved. -/
theorem isBigO_gammaSigma_finset_sum_of_one_le {mu : Measure Omega}
    [IsFiniteMeasure mu] {iota : Type*} (s : Finset iota) {X : iota → Omega → ℝ}
    {a : iota → ℝ} {sigma : ℝ} (hsigma : 1 ≤ sigma) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑ i ∈ s, X i omega) (16384 * ∑ i ∈ s, a i) := by
  have hpos : (0 : ℝ) < sigma := lt_of_lt_of_le zero_lt_one hsigma
  have hsum := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := mu) (s := s) (X := X) (a := a) (σ := sigma) hpos hs ha hX hXm
  rwa [gammaTriangleConst_eq_of_one_le hsigma] at hsum

/-- The same statement in the manuscript's own indexing `X_1, …, X_N`:
for `σ ≥ 1`, `N ≥ 1` and `X_i = O_{Γ_σ}(a_i)` with `a_i > 0`,

`∑_{i = 1}^{N} X_i = O_{Γ_σ}(16384 * ∑_{i = 1}^{N} a_i)`,

the finite-sum step of the printed proof before the passage to the
limit over partial sums. The prefactor is the upstream one; see the module
docstring for its relation to the printed prefactor `1`. -/
theorem isBigO_gammaSigma_finSum_of_one_le {mu : Measure Omega}
    [IsFiniteMeasure mu] {N : ℕ} {X : Fin N → Omega → ℝ} {a : Fin N → ℝ}
    {sigma : ℝ} (hsigma : 1 ≤ sigma) (hN : 1 ≤ N) (ha : ∀ i, 0 < a i)
    (hX : ∀ i, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (X i) (a i))
    (hXm : ∀ i, Measurable (X i)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑ i, X i omega) (16384 * ∑ i, a i) :=
  isBigO_gammaSigma_finset_sum_of_one_le (mu := mu)
    (Finset.univ : Finset (Fin N)) hsigma
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun i _ => ha i) (fun i _ => hX i)
    (fun i _ => hXm i)

end SuperdiffusionCLT.Probability
