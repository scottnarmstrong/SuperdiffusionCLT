/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.IndependentSums.WeakOrlicz

/-!
# Interpolation: truncating a `Γ₁` estimate to a `Γ₂` estimate

This module supplies the interpolation step of the printed minscale argument: a nonnegative random
variable which is `O_{Γ₁}(A)` is, after the truncation `min {1, ·}`, in
`O_{Γ₂}(√A)`. The printed proof applies it with `A = C ν⁻² 3 ^ -(n' - h)` to
convert the balanced comparison quantity of `e.localization.s.star` into the
inner `ν⁻¹` factor of the Step-C display; direct routes that skip the
`min {1, ·}` truncation lose one power of `ν`.

The mechanism is the tail-event comparison of the printed proof: for `y ≥ 0`
one has `min {1, y} ≤ √y` pointwise, and the tail event of `√y` at threshold
`√A t` is exactly the tail event of `y` at threshold `A t²`, so the `Γ₁` tail
hypothesis `P[|y| > A u] ≤ exp(-u)` evaluated at `u = t²` gives the `Γ₂` tail
bound `P[min {1, y} > √A t] ≤ exp(-t²)` with the sharp constant `1`. No
enlargement of the amplitude is required.

## Main results

* `isBigO_gammaSigma_sqrt_of_isBigO_gammaSigma_one`: the square-root
  interpolation `X = O_{Γ₁}(A) ⟹ √|X| = O_{Γ₂}(√A)` with the sharp amplitude
  `√A`.
* `isBigO_gammaSigma_min_one_of_isBigO_gammaSigma_one`: the truncated form
  `X ≥ 0`, `X = O_{Γ₁}(A) ⟹ min {1, X} = O_{Γ₂}(√A)`, the form consumed by
  the Step-C display of the minscale argument.

## Implementation notes

The amplitude `A` is assumed nonnegative rather than positive, since the
square-root amplitude `√A` is then still defined; the tail statements need no
other regularity of `A`. The measure is an arbitrary probability measure, as
elsewhere in this directory: the tail relations are defined for every measure
and the proofs below use no finiteness beyond the probability hypothesis
carried for uniformity with the sibling modules. Measurability of `X` is not
required: the tail relations quantify over raw events, and the proofs only
compare events pointwise.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open Homogenization
open MeasureTheory

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The pointwise truncation inequality behind the interpolation step of the
printed minscale argument: for `y ≥ 0` the truncated value
`min {1, y}` is at most `√y`. On `y ≤ 1` this is `y ≤ √y`, on `1 ≤ y` it is
`1 ≤ √y`. -/
private theorem min_one_le_sqrt {y : ℝ} (hy : 0 ≤ y) :
    min 1 y ≤ Real.sqrt y := by
  rcases le_total y 1 with h | h
  · rw [min_eq_right h]
    exact (Real.le_sqrt hy hy).2 <|
      calc y ^ 2 = y * y := pow_two y
        _ ≤ y * 1 := mul_le_mul_of_nonneg_left h hy
        _ = y := mul_one y
  · rw [min_eq_left h]
    exact Real.one_le_sqrt.2 h

/-- The square-root interpolation behind the printed Step C:
if `X = O_{Γ₁}(A)` with `A ≥ 0` — the tail relation `P[|X| > t A] ≤ exp(-t)`
for every `t ≥ 1` — then the nonnegative variable `ω ↦ √|X ω|` satisfies the
`Γ₂` tail bound with the sharp amplitude `√A`:

`P[√|X| > t √A] ≤ exp(-t²)` for every `t ≥ 1`.

The proof is the tail-event comparison: `√|X| > √A t` is the same event as
`|X| > A t²`, so the `Γ₁` hypothesis evaluated at `u = t² ≥ 1` gives the
conclusion exactly, with no change of amplitude. -/
theorem isBigO_gammaSigma_sqrt_of_isBigO_gammaSigma_one {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 1) X A) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2)
      (fun omega => Real.sqrt |X omega|) (Real.sqrt A) := by
  rw [IndependentSums.isBigO_gammaSigma_iff]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have ht1 : (1 : ℝ) ≤ t ^ (2 : ℝ) := Real.one_le_rpow ht zero_le_two
  -- the tail event of `√|X|` at `√A t` is the tail event of `X` at `A t²`
  have hset : IndependentSums.absTailEvent (fun omega => Real.sqrt |X omega|)
      (Real.sqrt A * t) = IndependentSums.absTailEvent X (A * t ^ (2 : ℝ)) := by
    have hA0 : (0 : ℝ) ≤ A * t ^ (2 : ℝ) :=
      mul_nonneg hA (Real.rpow_nonneg ht0 2)
    have hsqrt : Real.sqrt (A * t ^ (2 : ℝ)) = Real.sqrt A * t := by
      rw [Real.sqrt_mul hA, Real.rpow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]
    ext omega
    simp only [IndependentSums.mem_absTailEvent]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), ← hsqrt,
      Real.sqrt_lt_sqrt_iff hA0]
  rw [hset]
  have htail := IndependentSums.isBigO_gammaSigma_iff.1 hX ht1
  rw [Real.rpow_one] at htail
  exact htail

/-- The truncated form of the interpolation step of the printed minscale
argument: if `X ≥ 0` and `X = O_{Γ₁}(A)` with `A ≥ 0`, then
the truncated variable `ω ↦ min {1, X ω}` is `O_{Γ₂}(√A)` with the sharp
amplitude `√A`. This is the display `min {1, |s^{1/2} σ⁻¹ s^{1/2} - Id|} =
O_{Γ₂}(C √A)` of the Step-C line, with the inner `ν⁻¹` factor it produces.

The proof combines the pointwise domination `min {1, y} ≤ √y`
(`min_one_le_sqrt`) with the tail-event comparison
`isBigO_gammaSigma_sqrt_of_isBigO_gammaSigma_one`. -/
theorem isBigO_gammaSigma_min_one_of_isBigO_gammaSigma_one {mu : Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu] {X : Omega → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hnn : ∀ omega, 0 ≤ X omega)
    (hX : IndependentSums.IsBigO mu (IndependentSums.gammaSigma 1) X A) :
    IndependentSums.IsBigO mu (IndependentSums.gammaSigma 2)
      (fun omega => min 1 (X omega)) (Real.sqrt A) := by
  have hpoint : ∀ omega : Omega,
      |min 1 (X omega)| ≤ |(Real.sqrt |X omega|)| := by
    intro omega
    have hminnn : (0 : ℝ) ≤ min 1 (X omega) :=
      le_min zero_le_one (hnn omega)
    rw [abs_of_nonneg hminnn, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc min 1 (X omega) ≤ Real.sqrt (X omega) := min_one_le_sqrt (hnn omega)
      _ = Real.sqrt |X omega| := by rw [abs_of_nonneg (hnn omega)]
  exact (isBigO_gammaSigma_sqrt_of_isBigO_gammaSigma_one hA hX).of_abs_le hpoint

end SuperdiffusionCLT.Probability