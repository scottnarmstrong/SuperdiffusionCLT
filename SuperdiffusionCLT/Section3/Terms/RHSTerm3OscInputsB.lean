/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCg
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RBounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Displays
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurability
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC

/-!
# The side conditions of `e.RHS.term3.B` at the `oscH1` carrier

`rhs_term3_B` (`Section3/Terms/RHSTerm3StepsA2.lean`) takes, besides the
regularity-gate data discharged in `RHSTerm3OscCg`, side-condition binders on
the free data of the term: the nonnegativity clauses, the product integrability
`hOFint`, and the `L^3` / `L^{3/2}` memberships `hMemOsc`, `hMemFlux` of
`oscH1`, `fluxNegNorm`.

This module discharges the `oscH1` side conditions at the carrier
`oscH1Carrier` (`RHSTerm3OscInputs.lean`):

* `memLp_ofReal_of_integrable_rpow`: a nonnegative sample observable whose `q`-th real
  power is integrable is in `L^q`.
* `oscSideCondition_hOFint`: the product integrability `hOFint` of `rhs_term3_B`, from the
  two `MemLp` memberships by Hölder's inequality.

The sample measurability of the carrier, the discharge of the `hOFint` /
`hMemOsc` / `hMemFlux` binders at the carriers, and the `fluxNegNorm` /
`energyL2` carriers are the remaining items and are not attempted here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
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

variable {d : ℕ}

/-! ## The nonnegativity clause at the carrier -/

/-! ## The centered gradient as an `L²` field on a sub-cube -/

/-! ## The `MemLp` side conditions -/

/-- A nonnegative sample observable whose `q`-th real power is integrable is in
`L^q` for the exponent `ENNReal.ofReal q`: the `ℒ^q` seminorm is the
`q`-th root of the integral of the `q`-th power. -/
theorem memLp_ofReal_of_integrable_rpow {P : ProbabilityMeasure (ShellSeq d)}
    {f : ShellSeq d → ℝ} {q : ℝ} (hq : 0 < q) (hnn : 0 ≤ f)
    (hmeas : AEStronglyMeasurable f P.toMeasure)
    (hint : Integrable (fun omega : ShellSeq d => f omega ^ q) P.toMeasure) :
    MemLp f (ENNReal.ofReal q) P.toMeasure := by
  show eLpNorm f (ENNReal.ofReal q) P.toMeasure < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_ne_zero_iff.2 hq)
    ENNReal.ofReal_ne_top hmeas, ENNReal.toReal_ofReal (le_of_lt hq)]
  refine ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hq.le) ?_
  have hfin : ∫⁻ omega : ShellSeq d, ‖(fun t : ShellSeq d => f t ^ q) omega‖ₑ ∂P.toMeasure < ∞ :=
    hint.hasFiniteIntegral
  have hpoint : ∀ omega : ShellSeq d,
      ‖f omega‖ₑ ^ q = ‖(fun t : ShellSeq d => f t ^ q) omega‖ₑ := by
    intro omega
    rw [Real.enorm_eq_ofReal (hnn omega),
      Real.enorm_eq_ofReal (Real.rpow_nonneg (hnn omega) q),
      ENNReal.ofReal_rpow_of_nonneg (hnn omega) hq.le]
  rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact hfin.ne

/-! ## The product integrability -/

/-- **The `hOFint` side condition of `rhs_term3_B`**: the product
`oscH1 · fluxNegNorm` is integrable in the sample on every scale-`n` sub-cube,
from the two `MemLp` memberships by Hölder's inequality at the exponents
`3` and `3/2`, whose inverses add to one. -/
theorem oscSideCondition_hOFint {P : ProbabilityMeasure (ShellSeq d)} {n m : ℕ}
    (oscH1 fluxNegNorm : ShellSeq d → TriadicCube d → ℝ)
    (hMemOsc : ∀ R ∈ largeCubeSubcubes d n m,
      MemLp (fun omega : ShellSeq d => oscH1 omega R) (ENNReal.ofReal (3 : ℝ))
        P.toMeasure)
    (hMemFlux : ∀ R ∈ largeCubeSubcubes d n m,
      MemLp (fun omega : ShellSeq d => fluxNegNorm omega R)
        (ENNReal.ofReal ((3 : ℝ) / 2)) P.toMeasure) :
    ∀ R ∈ largeCubeSubcubes d n m,
      Integrable (fun omega : ShellSeq d => oscH1 omega R * fluxNegNorm omega R)
        P.toMeasure := by
  have hholder : ENNReal.HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal ((3 : ℝ) / 2)) 1 :=
    ⟨by
      have h3 : (0 : ℝ) < 3 := by norm_num
      have h32 : (0 : ℝ) < 3 / 2 := by norm_num
      have hsum : (3 : ℝ)⁻¹ + ((3 : ℝ) / 2)⁻¹ = 1 := by norm_num
      have hadd : ENNReal.ofReal ((3 : ℝ)⁻¹ + ((3 : ℝ) / 2)⁻¹)
          = ENNReal.ofReal ((3 : ℝ)⁻¹)
            + ENNReal.ofReal (((3 : ℝ) / 2)⁻¹) :=
        ENNReal.ofReal_add (by positivity) (by positivity)
      rw [← ENNReal.ofReal_inv_of_pos h3, ← ENNReal.ofReal_inv_of_pos h32, ← hadd, hsum,
        ENNReal.ofReal_one, inv_one]⟩
  intro R hR
  exact MeasureTheory.memLp_one_iff_integrable.1
    (MeasureTheory.MemLp.fun_mul (hf := hMemFlux R hR) (hφ := hMemOsc R hR))

end

end SuperdiffusionCLT.Section3.Terms