/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz

/-!
# Weakening the index of a stretched-exponential tail class

The paper defines the tail relation `X ≤ O_Ψ(A)` by the bound
`P[X > t A] ≤ Ψ(t)⁻¹` for every `t ∈ [1, ∞)`, and takes for
`Ψ` the stretched-exponential class `Γ_σ(t) = exp(t ^ σ)`, whose index is
restricted to `σ ∈ (0, ∞)`. Because the bound is only asserted for `t ≥ 1`, the family
`Γ_σ` is increasing in `σ` where it is used, so a tail estimate stated with a
large index also holds with any smaller index and *the same amplitude* `A`.

This is the step the paper performs silently, where the
error term `O_{Γ_{1/2}}(C ν⁻³ ℓ 3 ^ (n - m))` supplied by the localization
estimate is reused inside a `Γ_{1/3}` bookkeeping as
`O_{Γ_{1/3}}(C ν⁻³ L' 3 ^ -(ℓ - n))`.

## Main results

* `gammaSigma_le_gammaSigma_of_exponent_le`: `Γ_{σ'}(t) ≤ Γ_σ(t)` for `t ≥ 1`
  and `σ' ≤ σ`.
* `inv_gammaSigma_le_inv_gammaSigma_of_exponent_le`: the reciprocal form, which
  is the shape in which the tail bound consumes the comparison.
* `isBigOWith_gammaSigma_of_exponent_le` and `isBigO_gammaSigma_of_exponent_le`:
  a random variable in `O_{Γ_σ}(A)` is in `O_{Γ_{σ'}}(A)`, with no change of
  amplitude.
* `isBigO_gammaSigma_one_third_of_one_half`: the instance `σ = 1/2`,
  `σ' = 1/3` used there.

## Implementation notes

The ambient hypothesis of the paper on the two indices is `0 < σ' ≤ σ`. The
positivity of `σ'` is not needed here and is therefore not assumed: since the
tail bound quantifies only over `t ≥ 1`, the comparison
`t ^ σ' ≤ t ^ σ` follows from `σ' ≤ σ` alone. The results below are stated with
that weaker hypothesis, which the hypothesis of the paper implies. For the same
reason no enlargement of the amplitude is required: the transfer is with the
identical constant `A`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open Homogenization
open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The stretched-exponential tail functions are increasing in the index on
`[1, ∞)`: if `sigma' ≤ sigma` and `1 ≤ t`, then `Γ_{sigma'}(t) ≤ Γ_sigma(t)`.
This is the pointwise content of the index weakening used in the paper. -/
theorem gammaSigma_le_gammaSigma_of_exponent_le {sigma' sigma t : ℝ}
    (hsigma : sigma' ≤ sigma) (ht : 1 ≤ t) :
    IndependentSums.gammaSigma sigma' t ≤ IndependentSums.gammaSigma sigma t := by
  rw [IndependentSums.gammaSigma_apply, IndependentSums.gammaSigma_apply]
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le ht hsigma)

/-- The reciprocal form of `gammaSigma_le_gammaSigma_of_exponent_le`: on
`[1, ∞)` the bound `Γ_sigma(t)⁻¹` supplied by the larger index is at least as
strong as the bound `Γ_{sigma'}(t)⁻¹` demanded by the smaller one. -/
theorem inv_gammaSigma_le_inv_gammaSigma_of_exponent_le {sigma' sigma t : ℝ}
    (hsigma : sigma' ≤ sigma) (ht : 1 ≤ t) :
    (IndependentSums.gammaSigma sigma t)⁻¹ ≤
      (IndependentSums.gammaSigma sigma' t)⁻¹ := by
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hpos : 0 < IndependentSums.gammaSigma sigma' t :=
    lt_of_lt_of_le zero_lt_one (IndependentSums.one_le_gammaSigma ht0)
  exact inv_anti₀ hpos (gammaSigma_le_gammaSigma_of_exponent_le hsigma ht)

/-- Index weakening for the one-sided tail relation `X ≤ O_{Γ_sigma}(A)`:
lowering the index of the stretched-exponential class preserves the estimate with the same
amplitude `A`. -/
theorem isBigOWith_gammaSigma_of_exponent_le {mu : Measure Omega}
    {X : Omega → ℝ} {A sigma' sigma : ℝ} (hsigma : sigma' ≤ sigma)
    (hX : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) X A) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma') X A := by
  intro t ht
  exact (hX ht).trans (inv_gammaSigma_le_inv_gammaSigma_of_exponent_le hsigma ht)

/-- Index weakening for the two-sided tail relation `X = O_{Γ_sigma}(A)`, the
absolute-value form. The amplitude `A` is unchanged. -/
theorem isBigO_gammaSigma_of_exponent_le {mu : Measure Omega}
    {X : Omega → ℝ} {A sigma' sigma : ℝ} (hsigma : sigma' ≤ sigma)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma) X A) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma sigma') X A :=
  isBigOWith_gammaSigma_of_exponent_le (X := fun omega ↦ |X omega|) hsigma hX

/-- The instance `σ = 1/2`, `σ' = 1/3` of `isBigO_gammaSigma_of_exponent_le`: the
`Γ_{1/2}` error term of the localization estimate enters the `Γ_{1/3}` bookkeeping
with the same amplitude. -/
theorem isBigO_gammaSigma_one_third_of_one_half {mu : Measure Omega}
    {X : Omega → ℝ} {A : ℝ}
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma (1 / 2)) X A) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma (1 / 3)) X A :=
  isBigO_gammaSigma_of_exponent_le (by norm_num) hX

end SuperdiffusionCLT.Probability
