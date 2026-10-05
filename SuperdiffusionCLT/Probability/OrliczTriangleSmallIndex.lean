/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.Triangle

/-!
# The generalized triangle inequality for `O_{Γ_σ}` at `0 < σ ≤ 1`

This module records the `σ ∈ (0, 1)` half of the manuscript's Lemma
`l.Gamma.sigma.triangle`, whose display
`e.Gamma.sigma.triangle` reads: for a nonnegative summable
sequence `{a_k}` and random variables `X_k = O_{Γ_σ}(a_k)`,

`∑_k X_k ≤ O_{Γ_σ}((1 + C σ⁻¹ 1_{σ < 1}) ∑_k a_k)`,

where `C` is a universal constant. Here `X ≤ O_Ψ(A)` is the tail relation
`P[X > t A] ≤ Ψ(t)⁻¹` for `t ∈ [1, ∞)` and
`Γ_σ(t) = exp(t ^ σ)`.

## What is proved here, and what is not

The printed proof argues only the range `0 < σ < 1`, and
does so by invoking "the standard quasi-triangle inequality for this Orlicz
norm", giving

`‖∑_k X_k‖_{Γ_σ} ≤ C σ⁻¹ ∑_k ‖X_k‖_{Γ_σ}`,

with the remark that "the factor `σ⁻¹` is the usual loss in convexifying the
quasi-norm `t ↦ t ^ σ` near the origin". No reference is
given for the quasi-triangle inequality and its constant is not computed; the
printed prefactor `1 + C σ⁻¹ 1_{σ < 1}` therefore remains an external input,
the graph node `l.Gamma.sigma.triangle#quasi-triangle-inequality`. It is
**not** proved here and it is **not** available upstream.

What the upstream library provides is the same finite-family sum rule with an
explicit prefactor: `Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`
gives,
for `0 < σ`, a nonempty `Finset s`, positive amplitudes `a i` and measurable
`X i` with `X i = O_{Γ_σ}(a i)`,

`∑_{i ∈ s} X i = O_{Γ_σ}(gammaTriangleConst σ * ∑_{i ∈ s} a i)`,

with `gammaTriangleConst σ = 4 * gammaGrowthConst σ ^ (12 : ℝ)` and
`gammaGrowthConst σ = max 2 ((1 + σ⁻¹) ^ σ⁻¹)`
(in the same library).

This module evaluates that upstream prefactor on `0 < σ ≤ 1`. There the
maximum is attained by its second entry (`(1 + σ⁻¹) ^ σ⁻¹ ≥ 2`), so
`gammaTriangleConst σ = 4 * (1 + σ⁻¹) ^ (12 σ⁻¹)`, and the explicit prefactor
obtained here is

`4 * (2 / σ) ^ (12 / σ)`,

which dominates the upstream one on this range because `1 + σ⁻¹ ≤ 2 / σ` for
`σ ≤ 1`.

## Why the printed prefactor is not reached by the upstream route

The printed prefactor on this range is `1 + C σ⁻¹`, a polynomial of degree
one in `σ⁻¹`. The upstream constant is not of that order: since `12 σ⁻¹ → ∞` as `σ → 0`, it
grows faster than any fixed polynomial in `σ⁻¹`. So no choice of the universal `C` makes
the printed prefactor an upper bound for the upstream one, and the printed
constant `1 + C σ⁻¹` must be taken as the external input named above.

The manuscript's infinite sum over `k ∈ ℕ` is obtained in the printed proof
by passing to the limit over partial sums; only the
finite-sum step is treated here, over an arbitrary `Finset` and, in the
manuscript's own indexing, over `Fin N`.

Throughout, the hypothesis on the index is written `hinv : (1 : ℝ) ≤ σ⁻¹`,
which for `0 < σ` is equivalent to `σ ≤ 1`.

## Main results

* `gammaGrowthConst_eq_rpow_inv_of_le_one`: `gammaGrowthConst σ =
  (1 + σ⁻¹) ^ σ⁻¹` for `0 < σ ≤ 1`, the second entry of the maximum.
* `gammaTriangleConst_le_of_le_one`: the explicit prefactor
  `4 * (2 / σ) ^ (12 / σ)` dominates the upstream one on `0 < σ ≤ 1`.
* `isBigO_gammaSigma_finset_sum_of_le_one`: the finite-sum rule on `0 < σ ≤ 1`
  with the explicit prefactor, over a `Finset`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory
open Homogenization

variable {Omega : Type*} [MeasurableSpace Omega]

/-- On the manuscript's range `0 < σ ≤ 1` the upstream
growth constant `gammaGrowthConst σ = max 2 ((1 + σ⁻¹) ^ σ⁻¹)`
equals its second entry: the exponent `σ⁻¹` is
at least `1`, so `(1 + σ⁻¹) ^ σ⁻¹ ≥ 1 + σ⁻¹ ≥ 2`. -/
theorem gammaGrowthConst_eq_rpow_inv_of_le_one {sigma : ℝ} (hpos : 0 < sigma)
    (hinv : (1 : ℝ) ≤ sigma⁻¹) :
    IndependentSums.gammaGrowthConst sigma = (1 + sigma⁻¹) ^ (sigma⁻¹) := by
  have hinvpos : (0 : ℝ) < sigma⁻¹ := inv_pos.2 hpos
  have hbase : (1 : ℝ) ≤ 1 + sigma⁻¹ := by linarith only [hinvpos]
  have hstep : (2 : ℝ) ≤ (1 + sigma⁻¹) ^ (sigma⁻¹) := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase hinv
    rw [Real.rpow_one] at h
    exact le_trans (by linarith only [hinv]) h
  simp only [IndependentSums.gammaGrowthConst]
  exact max_eq_right hstep

/-- The explicit prefactor of the `0 < σ ≤ 1` half of the finite-sum rule
`e.Gamma.sigma.triangle`: for `0 < σ ≤ 1` the upstream triangle
prefactor `gammaTriangleConst σ = 4 * gammaGrowthConst σ ^ (12 : ℝ)`
is bounded by

`4 * (2 / σ) ^ (12 / σ)`,

because on this range `gammaGrowthConst σ = (1 + σ⁻¹) ^ σ⁻¹`
(`gammaGrowthConst_eq_rpow_inv_of_le_one`) and `1 + σ⁻¹ ≤ 2 / σ`. This is the
prefactor stated in `isBigO_gammaSigma_finset_sum_of_le_one`; it is not the
printed `1 + C σ⁻¹`, which is the external input
`l.Gamma.sigma.triangle#quasi-triangle-inequality`. -/
theorem gammaTriangleConst_le_of_le_one {sigma : ℝ} (hpos : 0 < sigma)
    (hinv : (1 : ℝ) ≤ sigma⁻¹) :
    IndependentSums.gammaTriangleConst sigma ≤ 4 * (2 / sigma) ^ ((12 : ℝ) / sigma) := by
  have hinvpos : (0 : ℝ) < sigma⁻¹ := inv_pos.2 hpos
  have hbase : (1 : ℝ) ≤ 1 + sigma⁻¹ := by linarith only [hinvpos]
  have hbase0 : (0 : ℝ) ≤ 1 + sigma⁻¹ := le_trans zero_le_one hbase
  have hle : sigma ≤ 1 := (one_le_inv_iff₀ (a := sigma)).1 hinv |>.2
  have hexp : (12 : ℝ) * sigma⁻¹ = (12 : ℝ) / sigma := by ring
  have hscale : (1 : ℝ) + sigma⁻¹ ≤ 2 / sigma := by
    rw [show (1 : ℝ) + sigma⁻¹ = (1 + sigma) / sigma by field_simp; ring]
    exact div_le_div_of_nonneg_right (by linarith only [hle]) (le_of_lt hpos)
  have hcore : (1 + sigma⁻¹) ^ ((12 : ℝ) / sigma) ≤ (2 / sigma) ^ ((12 : ℝ) / sigma) :=
    Real.rpow_le_rpow hbase0 (by linarith only [hscale])
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 12) (le_of_lt hpos))
  calc IndependentSums.gammaTriangleConst sigma
      = 4 * ((1 + sigma⁻¹) ^ (sigma⁻¹)) ^ (12 : ℝ) := by
        simp only [IndependentSums.gammaTriangleConst,
          gammaGrowthConst_eq_rpow_inv_of_le_one hpos hinv]
    _ = 4 * (1 + sigma⁻¹) ^ ((12 : ℝ) / sigma) := by
        rw [(Real.rpow_mul hbase0 sigma⁻¹ (12 : ℝ)).symm, mul_comm sigma⁻¹ (12 : ℝ), hexp]
    _ ≤ 4 * (2 / sigma) ^ ((12 : ℝ) / sigma) :=
        mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 4)

/-- The finite-sum instance of the printed display `e.Gamma.sigma.triangle` on the manuscript's
range `0 < σ ≤ 1`, over an arbitrary nonempty `Finset` of indices: if `X i = O_{Γ_σ}(a i)` for
each `i ∈ s`, then

`∑_{i ∈ s} X i = O_{Γ_σ}((4 * (2 / σ) ^ (12 / σ)) * ∑_{i ∈ s} a i)`.

This is `Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`
with its prefactor bounded by `gammaTriangleConst_le_of_le_one`. The printed
prefactor on this range is `1 + C σ⁻¹`; that value is the external input
`l.Gamma.sigma.triangle#quasi-triangle-inequality` and is not used here, since the
upstream constant is not bounded by any such polynomial prefactor. -/
theorem isBigO_gammaSigma_finset_sum_of_le_one {mu : Measure Omega}
    [IsFiniteMeasure mu] {iota : Type*} (s : Finset iota) {X : iota → Omega → ℝ}
    {a : iota → ℝ} {sigma : ℝ} (hpos : 0 < sigma) (hinv : (1 : ℝ) ≤ sigma⁻¹)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma)
      (fun omega => ∑ i ∈ s, X i omega)
      ((4 * (2 / sigma) ^ ((12 : ℝ) / sigma)) * ∑ i ∈ s, a i) := by
  have hsum := IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := mu) (s := s) (X := X) (a := a) (σ := sigma) hpos hs ha hX hXm
  have hpos' : 0 < ∑ i ∈ s, a i := Finset.sum_pos ha hs
  have hamp : IndependentSums.gammaTriangleConst sigma * ∑ i ∈ s, a i
      ≤ (4 * (2 / sigma) ^ ((12 : ℝ) / sigma)) * ∑ i ∈ s, a i :=
    mul_le_mul_of_nonneg_right (gammaTriangleConst_le_of_le_one hpos hinv) hpos'.le
  exact IndependentSums.IsBigO.mono_scale hsum hamp

end SuperdiffusionCLT.Probability