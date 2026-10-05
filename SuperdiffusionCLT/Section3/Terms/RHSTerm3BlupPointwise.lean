/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.BellUpscaleBoundRemainder
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3BlupTransport

/-!
# The operator-norm slot of the printed quadratic term

The `_hBlup` slot of the term-3 assembly carries the pointwise clause

`matrixOperatorNorm (b_{L'} - b_ℓ) ≤ 1 * |b_ℓ| + (1 + 1⁻¹) * q(e) + Zrem`

for every `omega` and every triadic cube `z`, where `q(e)` is the *tested*
quadratic form `translatedStreamQuadFormLower nu ℓ L' e` at the single chain
direction `e` of the display `e.bL.to.bhomell.pre0zz` of the paper.

## 1. The two hardcoded coefficients against the print

The printed display `e.blupbounds` reads

```
| (b_ℓ − b_m)(U) | ≤ ep | b_m(U) |
    + (1 + ep⁻¹) | σ_{m,*}^{-1/2}(U) (κ_m − κ_ℓ)_U |²
    + O_{Γ_{1/2}}( C ν^{-3} ℓ 3^{n-m} )
```

The paper fixes the choice for this application: "with the fixed choice `ep=1`".  At
`ep = 1` the two printed coefficients are exactly `1` and `(1 + 1⁻¹) = 2`, so the clause's
`1 *` and `(1 + (1:ℝ)⁻¹) *` **match the print**; there is no coefficient
mismatch.  The application in the paper absorbs both into a generic
constant `C`, which is compatible since `C ≥ 1`.

## 2. The clause is strictly stronger than the print

The clause does *not* match the print in its quadratic slot.  The print's slot
is the **operator-norm square** `|σ_{m,*}^{-1/2}(U)(κ_m − κ_ℓ)_U|²` — the
supremum over the unit sphere is taken in the proof ("taking the supremum over
`|e| = 1`") — while the clause's slot is the same form **tested at the single
direction `e`**.  The tested form never exceeds the slot.
Hence the printed display yields the clause only at the **enlarged**
remainder `Zrem + 2 (slot − q(e))`, which is nonnegative.  Nothing in the printed proof
supplies a `Γ_{1/3}` tail for that enlargement: the slot is an *explicit additive term* of
the print, not part of the `O_{Γ_{1/2}}` remainder, and the printed chain only
tails the tested stream norm at amplitude `O(ν^{-1}(ℓ − m))`, without the localization decay
`3^{-(ℓ-n)}` that the clause's amplitude carries.  So clause 3 is
**strictly stronger** than the print, and no `Czero` can absorb the gap.

## Main results

* `translatedStreamSlot`: the operator-norm slot of the printed quadratic term at the
  genuine carriers.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal
open scoped BigOperators Matrix.Norms.Elementwise
open scoped MatrixOrder

variable {d : ℕ}

noncomputable section

/-! ## The operator-norm slot at the genuine carriers -/

/-- **The operator-norm slot of the printed quadratic term** at the translated
cube: the square of `|σ_{ℓ,*}^{-1/2}(z + cu_n) (κ_{L'} − κ_ℓ)_{z + cu_n}|`,
i.e. the right-hand side of the printed supremum over `|e| = 1` at the
carriers (`sigmaStarInvCoarse` at the `ell`-cutoff and the averaged finite
shell increment).  It dominates the tested form. -/
noncomputable def translatedStreamSlot (nu : ℝ) (ell L : ℕ) (omega : ShellSeq d)
    (z : TriadicCube d) : ℝ :=
  (matrixOperatorNorm (CFC.sqrt (sigmaStarInvCoarse (cubeSet z)
        (coefficientCutoff nu omega ell).toCoeffField) *
      volumeAverageMat (cubeSet z)
        (fun y => finiteShellIncrement omega ell L y))) ^ (2 : ℕ)

end

end SuperdiffusionCLT.Section3.Terms
