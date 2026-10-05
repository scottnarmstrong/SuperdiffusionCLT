/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.GammaSigma.Basic

/-!
# The power rule for `O_{Γ_σ}` tail bounds

This module states the display `e.powerofGammasigma` of the paper (inside the
multiplication lemma `l.o.gamma2.mult`) in the tail-bound sense of the paper:

for `σ, p, K ∈ (0, ∞)` and a nonnegative random variable `X`,

`X ≤ O_{Γ_σ}(K)  ⟺  X^p ≤ O_{Γ_{σ/p}}(K^p)`.

Here `X ≤ O_Ψ(A)` means `P[X > t A] ≤ Ψ(t)⁻¹` for every `t ∈ [1, ∞)`,
and `Γ_σ(t) = exp(t ^ σ)`.

## Main results

* `isBigOWith_gammaSigma_rpow_fwd` / `isBigOWith_gammaSigma_rpow_rev`: the two
  directions of the printed equivalence in the one-sided form `≤ O_{Γ_σ}`.
* `isBigOWith_gammaSigma_rpow_iff`: the printed equivalence itself.
* `isBigO_gammaSigma_rpow_fwd` / `isBigO_gammaSigma_rpow_iff`: the same rule in
  the symmetric form `= O_{Γ_σ}`, which is the meaning of the equality sign in
  the print; since the symmetric relation is defined through `|X|`
  and `|X| ^ p = X ^ p` for nonnegative `X`, these are stated with `X ^ p`
  directly, as the print reads them.

## Relation to the upstream statement

The upstream library already proves the rule:
`Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow` and
`Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow_iff`
(`Homogenization/Probability/IndependentSums/GammaSigma/Basic.lean`), plus the symmetric
`Homogenization.IndependentSums.isBigO_gammaSigma_rpow_iff`,
whose right-hand side is phrased with `|X| ^ p`. This module is therefore a
bridge: it restates the rule in the indexing of the paper, separating the two
directions of the printed equivalence and carrying the symmetric form with
`X ^ p` for nonnegative `X`. All proofs are one-line appeals to the upstream
lemmas plus pointwise rewrites `|X ω| = X ω`.

Hypothesis accounting, relative to the print (which quantifies
`σ, p, K ∈ (0, ∞)` and a *positive* random variable `X`):

* `0 < p` is required upstream and is part of the print. It is used to invert
  `p` in the reverse direction (`σ / p` back to `σ`).
* The print requires `K ∈ (0, ∞)`; upstream only requires `0 ≤ K`, which is
  weaker. This module carries the weaker upstream hypothesis `0 ≤ K` and so
  states slightly more than the print.
* The print says `X` is positive; upstream only requires pointwise
  `0 ≤ X`, which is weaker. This module carries the weaker upstream hypothesis.
* The print requires `σ ∈ (0, ∞)`; the upstream statement carries *no*
  hypothesis on `σ` at all — `gammaSigma (σ / p)` is defined for every real
  `σ` and the set-inclusion argument goes through unchanged, so
  `σ > 0` is genuinely not needed. This module likewise carries no hypothesis
  on `σ` and thus states more than the print.
* Measurability of `X` is neither required by the print nor by upstream: the
  tail relation `X ≤ O_Ψ(A)` is defined purely through the upper-tail event
  `{X > t A}` and `μ.real`, and no measurability hypothesis appears in either
  statement. None is added here.
* Upstream requires `[IsFiniteMeasure μ]`, which is an extra hypothesis not
  visible in the print (the manuscript works throughout with probability
  measures). It is needed upstream because the surrounding `Γ_σ` calculus
  phrases the tail relation through `μ.real`; this module carries it
  unchanged, as the print is silent.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory
open Homogenization

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The forward direction of the printed display `e.powerofGammasigma` in the one-sided tail
sense: for `0 < p`, `0 ≤ K`, a pointwise nonnegative random variable `X`, and any real
`σ`,

`X ≤ O_{Γ_σ}(K)` implies `X ^ p ≤ O_{Γ_{σ / p}}(K ^ p)`.

This is exactly `Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow`.
The print quantifies `σ, K ∈ (0, ∞)` and a positive `X`; see the module
docstring for the hypothesis accounting. -/
theorem isBigOWith_gammaSigma_rpow_fwd {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {K σ p : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hX : ∀ ω, 0 ≤ X ω)
    (hXK : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma σ) X K) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma (σ / p))
      (fun ω => X ω ^ p) (K ^ p) :=
  IndependentSums.isBigOWith_gammaSigma_rpow (μ := mu) (X := X) (A := K)
    (σ := σ) (p := p) hp hK hX hXK

/-- The reverse direction of the printed display `e.powerofGammasigma` in the one-sided tail
sense: for `0 < p`, `0 ≤ K`, a pointwise nonnegative random variable `X`, and any real
`σ`,

`X ^ p ≤ O_{Γ_{σ / p}}(K ^ p)` implies `X ≤ O_{Γ_σ}(K)`.

This is the backward half of
`Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow_iff`. -/
theorem isBigOWith_gammaSigma_rpow_rev {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {K σ p : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hX : ∀ ω, 0 ≤ X ω)
    (hXK : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma (σ / p))
      (fun ω => X ω ^ p) (K ^ p)) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma σ) X K := by
  have hiff := IndependentSums.isBigOWith_gammaSigma_rpow_iff
    (μ := mu) (X := X) (A := K) (σ := σ) (p := p) hp hK hX
  exact hiff.2 hXK

/-- The printed display `e.powerofGammasigma` itself, in the
one-sided tail sense: for `0 < p`, `0 ≤ K`, a pointwise
nonnegative random variable `X`, and any real `σ`,

`X ≤ O_{Γ_σ}(K)  ⟺  X ^ p ≤ O_{Γ_{σ / p}}(K ^ p)`.

This is exactly `Homogenization.IndependentSums.isBigOWith_gammaSigma_rpow_iff`
with the two directions named `isBigOWith_gammaSigma_rpow_fwd` and
`isBigOWith_gammaSigma_rpow_rev`. -/
theorem isBigOWith_gammaSigma_rpow_iff {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {K σ p : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hX : ∀ ω, 0 ≤ X ω) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma σ) X K ↔
      IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma (σ / p))
        (fun ω => X ω ^ p) (K ^ p) :=
  ⟨isBigOWith_gammaSigma_rpow_fwd hp hK hX, isBigOWith_gammaSigma_rpow_rev hp hK hX⟩

/-- The forward direction of the printed display `e.powerofGammasigma` in the symmetric sense
carried by the equality sign of the multiplication lemma: for `0 < p`, `0 ≤ K`, and a pointwise
nonnegative random variable `X`,

`X = O_{Γ_σ}(K)` implies `X ^ p = O_{Γ_{σ / p}}(K ^ p)`.

Upstream proves this symmetric rule with the right-hand side phrased through
`|X| ^ p` (`Homogenization.IndependentSums.isBigO_gammaSigma_rpow_iff`); for
nonnegative `X` the pointwise rewrite `|X ω| ^ p = |X ω ^ p|` identifies the
two readings, which is what this restatement does. -/
theorem isBigO_gammaSigma_rpow_fwd {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {K σ p : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hX : ∀ ω, 0 ≤ X ω)
    (hXK : IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ) X K) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma (σ / p))
      (fun ω => X ω ^ p) (K ^ p) := by
  have hiff := IndependentSums.isBigO_gammaSigma_rpow_iff
    (μ := mu) (X := X) (A := K) (σ := σ) (p := p) hp hK
  have h := hiff.1 hXK
  have hfun : (fun ω => |X ω| ^ p) = (fun ω => X ω ^ p) := by
    funext ω
    rw [abs_of_nonneg (hX ω)]
  rw [hfun] at h
  exact h

/-- The reverse direction of the printed display `e.powerofGammasigma` in the symmetric sense:
for `0 < p`, `0 ≤ K`, and a pointwise nonnegative random variable `X`,

`X ^ p = O_{Γ_{σ / p}}(K ^ p)` implies `X = O_{Γ_σ}(K)`. -/
theorem isBigO_gammaSigma_rpow_rev {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {K σ p : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hX : ∀ ω, 0 ≤ X ω)
    (hXK : IndependentSums.IsBigO mu (IndependentSums.gammaSigma (σ / p))
      (fun ω => X ω ^ p) (K ^ p)) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ) X K := by
  have hiff := IndependentSums.isBigO_gammaSigma_rpow_iff
    (μ := mu) (X := X) (A := K) (σ := σ) (p := p) hp hK
  have hfun : (fun ω => X ω ^ p) = (fun ω => |X ω| ^ p) := by
    funext ω
    rw [abs_of_nonneg (hX ω)]
  rw [hfun] at hXK
  exact hiff.2 hXK

/-- The printed display `e.powerofGammasigma` in the
symmetric sense: for `0 < p`, `0 ≤ K`, and a pointwise nonnegative
random variable `X`,

`X = O_{Γ_σ}(K)  ⟺  X ^ p = O_{Γ_{σ / p}}(K ^ p)`.

For signed `X` the print's `X = O_Ψ(A)` reads `|X| = O_Ψ(A)`, and the upstream
symmetric rule
`Homogenization.IndependentSums.isBigO_gammaSigma_rpow_iff` holds without any
nonnegativity hypothesis, with the right-hand side `|X| ^ p ≤ O_{Γ_{σ / p}}(K ^ p)`.
Nonnegativity is used here only to replace `|X| ^ p` by `X ^ p`, matching the
way the print writes the powers. -/
theorem isBigO_gammaSigma_rpow_iff {mu : Measure Omega} [IsFiniteMeasure mu]
    {X : Omega → ℝ} {K σ p : ℝ} (hp : 0 < p) (hK : 0 ≤ K)
    (hX : ∀ ω, 0 ≤ X ω) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma σ) X K ↔
      IndependentSums.IsBigO mu (IndependentSums.gammaSigma (σ / p))
        (fun ω => X ω ^ p) (K ^ p) :=
  ⟨isBigO_gammaSigma_rpow_fwd hp hK hX, isBigO_gammaSigma_rpow_rev hp hK hX⟩

end SuperdiffusionCLT.Probability