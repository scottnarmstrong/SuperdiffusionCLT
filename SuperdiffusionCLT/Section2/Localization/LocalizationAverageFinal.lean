/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1MomentsB
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageAssembly
public import SuperdiffusionCLT.Section2.Localization.LocalizationEnvelopeCarrier
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Inputs

/-!
# The final composition of the averaged gauged comparison

This module composes the two summand estimates of the proof of
`l.localization.average` (the statement
`SuperdiffusionCLT.Frozen.Section2.localization_average`).  The reduction
`localization_average_of_orlicz` (`LocalizationAverageWork.lean`) turns the single
Orlicz premise into the conclusion of the statement, and the assembly
`localizationAverageOrliczPremise_of_T1_T2` (`LocalizationAverageAssembly.lean`)
turns the two printed summand estimates at one common constant into that premise.

## Main results

1. `localizationAverageEnvelopeT1_mono_const`: the first printed amplitude is
   monotone in its envelope constant, the bookkeeping that lets the two
   summands meet at one common constant.

2. `localization_average_of_summandData`: the conclusion (in the Orlicz premise
   form) at the assembly constant `orliczAssemblyConst * max C₁ C₂`,
   from the two summand estimates at possibly different constants.  The
   constant reconciliation, the index weakening `Γ_{1/2} ↝ Γ_{1/3}`, the
   printed triangle rule and the degenerate branch `P = 0` are all
   included.

3. `localization_average_witness_of_summandData`: the same in the witness form
   of the statement, with its law binders.

The two summand estimates themselves are proved in the neighbouring modules.
The second summand is controlled through the carriers of
`LocalizationEnvelopeCarrier.lean`: the normalised perturbation
`V_z = bfE_ℓ^{-1/2}(bfA_ℓ(z+cu_n) - bfAhom_ℓ(cu_n))bfE_ℓ^{-1/2}` (`localizationV`),
the weight `W_z = |bfE_ℓ^{1/2}G_{-h_z}P|²` (`localizationW`), and the printed
averaged domination `|avsum_z Z_z| ≤ Wbar · avsum_z |V_z|`.

## The constant of the statement

The `∃ C` of the statement depends on `d` alone, whereas the constant produced
by the theorems of this module depends on the per-cube constants of the two
summand estimates.  Passing to a `d`-only constant takes the maximum of those
finitely many constants, which is what the printed proof's "after enlarging
`C(d)` if necessary" performs.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-! ## The first printed amplitude is monotone in its constant -/

/-- The first printed summand amplitude `C ν⁻³ |P|² 1_{L>ℓ} L 3^{-(ℓ-n)}` is
monotone in its envelope constant, the bookkeeping that lifts the first summand
from its own enlarged constant `localizationAverageT1Const * C` to the common
assembly constant. -/
theorem localizationAverageEnvelopeT1_mono_const {C C' nu : ℝ} (hCC' : C ≤ C')
    (hnu : 0 ≤ nu) (l L n : ℕ) (Pvec : BlockVec d) :
    localizationAverageEnvelopeT1 C nu l L n Pvec ≤
      localizationAverageEnvelopeT1 C' nu l L n Pvec := by
  unfold localizationAverageEnvelopeT1
  refine mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg hnu _))
      (SuperdiffusionCLT.Section2.Carriers.blockVecDot_self_nonneg Pvec)) ?_
  by_cases h : l < L
  · rw [ite_eq_left h]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  · rw [ite_eq_right h]

/-! ## The two summands at one common constant -/

/-- **The conclusion at one common constant.**  The assembly
`localizationAverageOrliczPremise_of_T1_T2` needs both printed summands at the
*same* envelope constant, whereas the two summand estimates produce them at
different ones (for the first, `localizationAverageT1Const` times the constant of
the per-cube bounds `localizationAverageT1CubeBoundConst Cd KY CR`).  Reconciling
them at `max C₁ C₂` via the two amplitude monotonicities is the printed
enlargement of `C(d)`: from the two summand estimates at `C₁`, `C₂` the Orlicz
premise holds at the assembly constant `orliczAssemblyConst * max C₁ C₂`. -/
theorem localization_average_of_summandData {C1 C2 nu : ℝ} (hC1 : 0 < C1)
    (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (m n l L : ℕ) (Pvec : BlockVec d)
    (T1 T2 : ShellSeq d → ℝ) (hT1m : Measurable T1) (hT2m : Measurable T2)
    (hT1nn : ∀ omega, 0 ≤ T1 omega) (hT2nn : ∀ omega, 0 ≤ T2 omega)
    (hdecomp : ∀ omega : ShellSeq d,
      |averagedGaugeComparison nu l L P m n Pvec omega| ≤ T1 omega + T2 omega)
    (hT1 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1 C1 nu l L n Pvec))
    (hT2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2)) T2
      (localizationAverageEnvelopeT2 C2 nu l L m n Pvec)) :
    LocalizationAverageOrliczPremise (orliczAssemblyConst * max C1 C2) nu P m n l L Pvec :=
  localizationAverageOrliczPremise_of_T1_T2
    (lt_of_lt_of_le hC1 (le_max_left C1 C2)) hnu P m n l L Pvec T1 T2 hT1m hT2m
    hT1nn hT2nn hdecomp
    (hT1.mono_scale (localizationAverageEnvelopeT1_mono_const (le_max_left C1 C2)
      hnu.le l L n Pvec))
    (hT2.mono_scale (localizationAverageEnvelopeT2_mono_le (le_max_right C1 C2)
      hnu.le l L m n Pvec))

/-- **The witness conclusion of `localization_average` at one common
constant.**  The premise form of `localization_average_of_summandData` turned
into the witness form of the statement by `localization_average_of_orlicz`: there is
a measurable witness `X` with `X = O_{Γ_{1/3}}(·)` at the printed amplitude and
the pointwise comparison `|LHS| ≤ X`.  The four law binders `J1V2`--`J4` and the
prefix are the binders of the statement (inert for the conclusion); the scale
inequalities `n ≤ ℓ ≤ m`, `ℓ ≤ L` and `ν ∈ (0,1]` are likewise carried
verbatim. -/
theorem localization_average_witness_of_summandData {C1 C2 nu : ℝ} (hC1 : 0 < C1)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P) (_hJ2 : ShellLawJ2 d P)
    (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
    (m n l L : ℕ) (hnl : n ≤ l) (hlm : l ≤ m) (hlL : l ≤ L) (Pvec : BlockVec d)
    (T1 T2 : ShellSeq d → ℝ) (hT1m : Measurable T1) (hT2m : Measurable T2)
    (hT1nn : ∀ omega, 0 ≤ T1 omega) (hT2nn : ∀ omega, 0 ≤ T2 omega)
    (hdecomp : ∀ omega : ShellSeq d,
      |averagedGaugeComparison nu l L P m n Pvec omega| ≤ T1 omega + T2 omega)
    (hT1 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) T1
      (localizationAverageEnvelopeT1 C1 nu l L n Pvec))
    (hT2 : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 2)) T2
      (localizationAverageEnvelopeT2 C2 nu l L m n Pvec)) :
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma ((1 : ℝ) / 3)) X
        (localizationAverageEnvelope (orliczAssemblyConst * max C1 C2) nu l L m n Pvec) ∧
      ∀ omega : ShellSeq d,
        |averagedGaugeComparison nu l L P m n Pvec omega| ≤ X omega :=
  localization_average_of_orlicz (C := orliczAssemblyConst * max C1 C2) hnu hnu1 P
    _hPrefix _hJ1V2 _hJ2 _hJ3 _hJ4 m n l L hnl hlm hlL Pvec
    (localization_average_of_summandData hC1 hnu P m n l L Pvec T1 T2 hT1m hT2m
      hT1nn hT2nn hdecomp hT1 hT2)

end SuperdiffusionCLT.Section2.Localization
