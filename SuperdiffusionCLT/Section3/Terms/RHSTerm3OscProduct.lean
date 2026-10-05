/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscConst

/-!
# The product form of the printed step `e.RHS.term3.B`, at the weakened rate

In the display `e.RHS.term3.B` of the paper, the oscillation term of `e.RHS.term3`
is bounded by the printed constant times `ν^{-3/2}(δ + η_L)^{1/2}(L')^{1/2}3^{-(ℓ'-n)}`.

## Why the obligation needs the rate weakened

The printed constant is `oscBoundConst Cpo C C3 S.h`
(`Section3/Terms/RHSTerm3OscCg.lean`), whose only window dependence is the
union-bound loss `(1 + h)^{1/2}`.  So the obligation `_hOscBound` of the term-3 statement
— the printed display at a constant `CB` quantified *before* the scale
selection — asks for

`CB ≥ oscBoundConst Cpo C C3 S.h` for every `S`,

which is false, since no scale-free `CB` bounds `(1 + h)^{1/2}` over the windows
of scale selections.  The obstruction is removed, at no cost, by weakening the
rate of the obligation from the printed `3^{-(ℓ'-n)}` to the rate that the
conclusion of the term-3 statement itself uses at its matching summand,
`3^{-(ℓ'-n)/2}` (`S.ellPrime - S.n = 2 * S.a`, so this is `3^{-a}`).

## Main results

* `oscBoundConst_mul_frozen_rate_le`: the **product form of the printed constant
  at the weakened rate**.  Under the hypothesis `S.h + 1 ≤ 3 ^ S.a`, the product
  `oscBoundConst Cpo C C3 S.h · 3^{-(ℓ'-n)}` is dominated, at the rate
  `3^{-(ℓ'-n)/2}`, by the explicit **scale-free** constant
  `max 1 (oscBoundConstBase Cpo C C3)`.  This is the explicitly-constant form of
  `oscBoundConst_mul_rate_le` (`Section3/Terms/RHSTerm3OscConst.lean`) at the
  exponent the conclusion reads.
* `oscBoundConst_productForm_le`: the **discharge of the rate-weakened
  obligation**, in the shape `_hOscBound` carries: any quantity bounded by the
  printed constant times the three prefactors times the printed rate
  `3^{-(ℓ'-n)}` is bounded by the scale-free constant
  `max 1 (oscBoundConstBase Cpo C C3)` times the same prefactors times the rate
  `3^{-(ℓ'-n)/2}`.  Taking `a₁ = ν^{-3/2}`, `a₂ = (δ + η_L)^{1/2}`,
  `a₃ = (L')^{1/2}` this is exactly the rate-weakened `_hOscBound` at the
  scale-free constant.  No input beyond the hypothesis `S.h + 1 ≤ 3 ^ S.a` is
  used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-- The rate `3^{-(ℓ'-n)/2}` is the offset rate `3^{-a}`, since
`ℓ' - n = 2a`. -/
theorem frozenRate_eq_offset_rate (S : ScaleSelection) :
    (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) = (3 : ℝ) ^ (-(S.a : ℝ)) := by
  have h2a : ((S.ellPrime - S.n : ℕ) : ℝ) = 2 * (S.a : ℝ) := by
    rw [S.ellPrime_sub_n]
    push_cast
    ring
  rw [h2a]
  ring_nf

/-- **The product form of the printed constant at the weakened rate.**  Under the
hypothesis `S.h + 1 ≤ 3 ^ S.a`, the product of the printed constant
`oscBoundConst Cpo C C3 S.h` (whose only window dependence is the union-bound
loss `(1 + h)^{1/2}`) with the printed rate `3^{-(ℓ'-n)}` is dominated, at the
conclusion's own rate `3^{-(ℓ'-n)/2} = 3^{-a}`, by the explicit
**scale-free** constant `max 1 (oscBoundConstBase Cpo C C3)`.

This is `oscBoundConst_mul_rate_le` (`Section3/Terms/RHSTerm3OscConst.lean`) read at the
exponent the conclusion uses, so the dominating constant does not see the
scale selection at all. -/
theorem oscBoundConst_mul_frozen_rate_le {Cpo C C3 : ℝ} (hCpo : 0 ≤ Cpo) (hC : 0 ≤ C)
    (hC3 : 0 ≤ C3) (S : ScaleSelection) (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a) :
    oscBoundConst Cpo C C3 S.h * (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) ≤
      max 1 (oscBoundConstBase Cpo C C3) *
        (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) := by
  rw [frozenRate_eq_offset_rate S]
  exact oscBoundConst_mul_rate_le hCpo hC hC3 S hWindowVsOffset

/-- **The rate-weakened obligation, in the shape `_hOscBound` carries.**  If a
quantity `X` is bounded by the printed constant times the three prefactors
`a₁`, `a₂`, `a₃` times the printed rate `3^{-(ℓ'-n)}`, then it is bounded by the
explicit scale-free constant `max 1 (oscBoundConstBase Cpo C C3)` times the same
prefactors times the rate `3^{-(ℓ'-n)/2}`.

At `a₁ = ν^{-3/2}`, `a₂ = (δ + η_L)^{1/2}`, `a₃ = (L')^{1/2}` the hypothesis is
the conclusion of the assembly `osc_bound_bridge`
(`Section3/Terms/RHSTerm3OscCg.lean`) and the conclusion is the printed display
`e.RHS.term3.B` at the weakened rate — i.e. the rate-weakened `_hOscBound` of
the term-3 statement at a constant that does not depend on the scale selection.  The
only input beyond the prefactors' nonnegativity is the hypothesis
`S.h + 1 ≤ 3 ^ S.a`. -/
theorem oscBoundConst_productForm_le {Cpo C C3 a1 a2 a3 X : ℝ} (hCpo : 0 ≤ Cpo)
    (hC : 0 ≤ C) (hC3 : 0 ≤ C3) {S : ScaleSelection}
    (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3)
    (hstrong : X ≤ oscBoundConst Cpo C C3 S.h * a1 * a2 * a3 *
      (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ))) :
    X ≤ max 1 (oscBoundConstBase Cpo C C3) * a1 * a2 * a3 *
      (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) := by
  have hP : (0 : ℝ) ≤ a1 * a2 * a3 := mul_nonneg (mul_nonneg h1 h2) h3
  have hstep1 : oscBoundConst Cpo C C3 S.h * a1 * a2 * a3 *
        (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) =
      (oscBoundConst Cpo C C3 S.h * (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ))) *
        (a1 * a2 * a3) := by ring
  have hstep2 : max 1 (oscBoundConstBase Cpo C C3) * a1 * a2 * a3 *
        (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) =
      (max 1 (oscBoundConstBase Cpo C C3) *
          (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2))) *
        (a1 * a2 * a3) := by ring
  calc X
      ≤ oscBoundConst Cpo C C3 S.h * a1 * a2 * a3 *
          (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ)) := hstrong
    _ = (oscBoundConst Cpo C C3 S.h * (3 : ℝ) ^ (-((S.ellPrime - S.n : ℕ) : ℝ))) *
          (a1 * a2 * a3) := hstep1
    _ ≤ (max 1 (oscBoundConstBase Cpo C C3) *
          (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2))) *
          (a1 * a2 * a3) :=
        mul_le_mul_of_nonneg_right
          (oscBoundConst_mul_frozen_rate_le hCpo hC hC3 S hWindowVsOffset) hP
    _ = max 1 (oscBoundConstBase Cpo C C3) * a1 * a2 * a3 *
          (3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) := hstep2.symm

end

end SuperdiffusionCLT.Section3.Terms
