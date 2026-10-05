/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxEnergy
public import SuperdiffusionCLT.Section3.Terms.CenteredGradientMeasurable
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCgB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscProduct
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PrintedFinal

/-!
# The energy carrier of the oscillation estimate `e.RHS.term3.B`

## The printed display and the rate

The display `e.RHS.term3.B` of the paper bounds the small-cube oscillation term by
`C\nu^{-\nicefrac32}(\delta+\eta_L)^{\nf12}(L')^{\nf12}3^{-(\ell'-n)}`.

The obligation `_hOscBound` of the term-3 statement reads the same display at the rate
`3^{-(\ell'-n)/2}` of the conclusion's own matching summand.  Since `\ell'-n = 2a \ge 0`,
this rate is the larger of the two, so the obligation is **weaker** than the printed
display at the same constant; it is not stronger.  The constant `CB` is a binder of
the term-3 statement, hence chosen before the `\forall`-telescope, as the printed pure `C`
is.

## Main results

* `oscEnergy`: the printed carrier `energyL2` pinned to `energyL2Carrier`, evaluated
  at the conclusion's own glued fields.
* `oscEnergy_nonneg`: it is nonnegative, which discharges the corresponding
  nonnegativity hypothesis of the oscillation estimate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
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

/-! ## The two printed carriers at the glued fields -/

/-- **`energyL2` pinned**: the printed
`\|\sigma^{1/2}(\nabla u_m - \nabla u_{n,z})\|^2_{\underline L^2(z+cu_n)}` of
`e.RHS.term3.B`, at the conclusion's own glued fields. -/
def oscEnergy {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu) (S : ScaleSelection)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) : ℝ :=
  energyL2Carrier nu
    (fun y => gluedGradientField hnu S.LPrime S.m S.m (fluxSlot nu S.LPrime P S.n e) omega y)
    (fun y => gluedGradientField hnu S.LPrime S.n S.m (fluxSlot nu S.LPrime P S.n e) omega y) R

/-- `oscEnergy` is nonnegative at `0 ≤ nu`: it is `nu` times a squared average. -/
theorem oscEnergy_nonneg {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (S : ScaleSelection)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    (omega : ShellSeq d) (R : TriadicCube d) : 0 ≤ oscEnergy nu hnu S P e omega R := by
  unfold oscEnergy
  exact energyL2Carrier_nonneg hnu.le _ _ R

/-! ## The close -/

end

end SuperdiffusionCLT.Section3.Terms
