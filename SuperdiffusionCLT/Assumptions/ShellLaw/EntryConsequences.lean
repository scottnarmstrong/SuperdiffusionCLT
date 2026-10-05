/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.J3OriginConsequences
public import SuperdiffusionCLT.Assumptions.ShellLaw.StationarityConsequences
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4

/-!
# Scalar shell-entry consequences

This module combines the direct marginal J3 tail, per-shell stationarity, and
the negation half of J4. It gives the centered scalar-entry bounds consumed by
independent-sum concentration. No scaling law is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellLawConsequences

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- A scalar entry of one shell at one fixed point is measurable on the
canonical sequence carrier. -/
theorem measurable_entry_coordinate (n : ℕ) (x : Vec d) (i k : Fin d) :
    Measurable (fun F : ℕ → ShellField d ↦ (F n) x i k) :=
  (ShellField.measurable_eval_entry x i k).comp
    (ShellField.measurable_shellCoordinate n)

/-- Every scalar entry at the origin has the unit-scale symmetric `Γ₂` tail
supplied by J3. -/
theorem isBigO_gammaSigma_entry_zero_coordinate
    (hJ3 : ShellLawJ3 d P) (n : ℕ) (i k : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun F : ℕ → ShellField d ↦ (F n) 0 i k) 1 := by
  unfold IndependentSums.IsBigO
  exact (hJ3.isBigOWith_gammaSigma_j3Observable_coordinate n).of_le
    (fun F ↦ ShellField.abs_entry_zero_le_j3Observable n (F n) i k)

/-- Stationarity transports the unit-scale symmetric `Γ₂` entry bound
from the origin to every spatial point. -/
theorem isBigO_gammaSigma_entry_coordinate
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    (n : ℕ) (x : Vec d) (i k : Fin d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (fun F : ℕ → ShellField d ↦ (F n) x i k) 1 := by
  have hOrigin : IndependentSums.IsBigOWith P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun F : ℕ → ShellField d ↦ |(F n) 0 i k|) 1 := by
    simpa only [IndependentSums.IsBigO] using
      isBigO_gammaSigma_entry_zero_coordinate hJ3 n i k
  have hAbsMeas : Measurable (fun j : ShellField d ↦ |j 0 i k|) := by
    simpa only [Real.norm_eq_abs] using
      (ShellField.measurable_eval_entry 0 i k).norm
  have hTranslated :=
    hPrefix.isBigOWith_gammaSigma_shellObservable_translate n x
      (F := fun j : ShellField d ↦ |j 0 i k|) hAbsMeas hOrigin
  simpa only [IndependentSums.IsBigO, ShellField.translate_apply, zero_add]
    using hTranslated

/-- Whole-sequence negation symmetry makes the Bochner integral of every
measurable scalar shell entry vanish. Integrability is recorded separately
below, since Lean defines the integral of a nonintegrable function to be zero.
-/
theorem integral_entry_coordinate_eq_zero
    (hJ4 : ShellLawJ4 d P) (n : ℕ) (x : Vec d) (i k : Fin d) :
    ∫ F : ℕ → ShellField d, (F n) x i k ∂P.toMeasure = 0 := by
  let X : (ℕ → ShellField d) → ℝ := fun F ↦ (F n) x i k
  have hXMeas : Measurable X := by
    simpa only [X] using measurable_entry_coordinate n x i k
  have hNegLaw : Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure hJ4.negation
    change Measure.map (ShellField.negateSequence (d := d)) P.toMeasure =
      P.toMeasure at h
    exact h
  have hXMapMeas : AEStronglyMeasurable X
      (Measure.map (ShellField.negateSequence (d := d)) P.toMeasure) :=
    hXMeas.aestronglyMeasurable
  have hEq : (∫ F, X F ∂P.toMeasure) = -∫ F, X F ∂P.toMeasure := by
    calc
      ∫ F, X F ∂P.toMeasure =
          ∫ F, X F
            ∂Measure.map (ShellField.negateSequence (d := d)) P.toMeasure := by
        rw [hNegLaw]
      _ = ∫ F, X (ShellField.negateSequence F) ∂P.toMeasure :=
        integral_map ShellField.measurable_negateSequence.aemeasurable hXMapMeas
      _ = ∫ F, -X F ∂P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with F
        simp only [X, ShellField.negateSequence_apply, ShellField.negate_apply,
          Matrix.neg_apply]
      _ = -∫ F, X F ∂P.toMeasure := integral_neg X
  change (∫ F, X F ∂P.toMeasure) = 0
  exact CharZero.eq_neg_self_iff.mp hEq

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellLawConsequences
