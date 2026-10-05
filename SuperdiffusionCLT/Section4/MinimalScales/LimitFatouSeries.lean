/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Fatou's lemma for a series indexed by `ℕ`

The Fatou passage of the proof of `p.new.mixing.attempt` applies Fatou's lemma
to "the nonnegative weighted series in the definition of `mathcalE_{s,2}`".
This module proves that abstract fact: for a doubly-indexed family of
extended-nonnegative-real terms `f L l`, the series-sum of the pointwise
`liminf` over `L` is at most the `liminf` over `L` of the series-sums.

The proof transports Fatou's lemma for the Lebesgue integral
(`MeasureTheory.lintegral_liminf_le`) along the counting measure on `ℕ`
(`MeasureTheory.lintegral_count`), where every function is measurable because
`ℕ` carries the discrete measurable-space structure. No summability
hypothesis is needed: `ℝ≥0∞`-valued sums never hit the "non-summable tsum is
zero" junk branch that a real-valued `tsum` would.

## Main result

* `srootL_tsum_liminf_le_liminf_tsum`: `∑' l, liminf (fun L => f L l) atTop ≤
  liminf (fun L => ∑' l, f L l) atTop`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory Filter
open scoped ENNReal

/-- **Fatou's lemma for a nonnegative series indexed by `ℕ`.** For any family
`f : ℕ → ℕ → ℝ≥0∞` (thought of as `f L l`, the `l`-th term at stage `L`), the
series of the pointwise `liminf` over `L` is bounded by the `liminf` over `L`
of the series. This is Fatou's lemma for the Lebesgue integral against the
counting measure on `ℕ`, where every `ℝ≥0∞`-valued function is automatically
measurable. -/
theorem srootL_tsum_liminf_le_liminf_tsum (f : ℕ → ℕ → ℝ≥0∞) :
    (∑' l : ℕ, Filter.liminf (fun L : ℕ => f L l) Filter.atTop) ≤
      Filter.liminf (fun L : ℕ => ∑' l : ℕ, f L l) Filter.atTop := by
  have hmeas : ∀ L : ℕ, Measurable (f L) := fun L => Measurable.of_discrete
  have hfatou :
      (∫⁻ l, Filter.liminf (fun L : ℕ => f L l) Filter.atTop
          ∂(MeasureTheory.Measure.count (α := ℕ))) ≤
        Filter.liminf
          (fun L : ℕ => ∫⁻ l, f L l ∂(MeasureTheory.Measure.count (α := ℕ)))
          Filter.atTop :=
    MeasureTheory.lintegral_liminf_le hmeas
  rw [MeasureTheory.lintegral_count
      (fun l : ℕ => Filter.liminf (fun L : ℕ => f L l) Filter.atTop)] at hfatou
  simp only [MeasureTheory.lintegral_count] at hfatou
  exact hfatou

end SuperdiffusionCLT.Section4.MinimalScales
