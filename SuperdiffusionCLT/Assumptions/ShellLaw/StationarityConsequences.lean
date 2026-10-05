/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Homogenization.Book.Ch04.Theorems.Concentration
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix

/-!
# One-shell consequences of marginal stationarity

This module reads the stationarity field of the marginal shell-law
prefix at one natural shell index. It introduces no joint stationarity and no
scaling law.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open scoped ENNReal

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- The law of a measurable observable of shell `n` is its law under the
canonical one-coordinate marginal. -/
theorem map_shellObservable_eq_marginal (n : ℕ)
    (F : ShellField d → ℝ) (hF : Measurable F) :
    Measure.map (fun omega : ℕ → ShellField d ↦ F (omega n)) P.toMeasure =
      Measure.map F (ShellField.shellMarginalLaw P n).toMeasure := by
  change Measure.map (F ∘ fun omega : ℕ → ShellField d ↦ omega n) P.toMeasure =
    Measure.map F
      (Measure.map (fun omega : ℕ → ShellField d ↦ omega n) P.toMeasure)
  exact (Measure.map_map hF (ShellField.measurable_shellCoordinate n)).symm

/-- Every measurable one-shell observable has the same law after translating
that shell. Only the one-coordinate stationarity in the prefix is used.
-/
theorem map_shellObservable_translate_eq (hPrefix : ShellLawPrefix d P)
    (n : ℕ) (z : Homogenization.Vec d) (F : ShellField d → ℝ)
    (hF : Measurable F) :
    Measure.map
        (fun omega : ℕ → ShellField d ↦
          F (ShellField.translate z (omega n))) P.toMeasure =
      Measure.map (fun omega : ℕ → ShellField d ↦ F (omega n))
        P.toMeasure := by
  have hFt : Measurable (fun j : ShellField d ↦ F (ShellField.translate z j)) :=
    hF.comp (ShellField.measurable_translate z)
  rw [map_shellObservable_eq_marginal n _ hFt,
    map_shellObservable_eq_marginal n F hF]
  calc
    Measure.map (fun j : ShellField d ↦ F (ShellField.translate z j))
          (ShellField.shellMarginalLaw P n).toMeasure =
        Measure.map F
          (Measure.map (ShellField.translate z)
            (ShellField.shellMarginalLaw P n).toMeasure) := by
      exact (Measure.map_map hF (ShellField.measurable_translate z)).symm
    _ = Measure.map F (ShellField.shellMarginalLaw P n).toMeasure := by
      rw [hPrefix.stationary n z]

/-- Every one-shell weak `Γ_σ` tail estimate is unchanged when the shell is
translated. -/
theorem isBigOWith_gammaSigma_shellObservable_translate
    (hPrefix : ShellLawPrefix d P) (n : ℕ) (z : Homogenization.Vec d)
    {F : ShellField d → ℝ} (hF : Measurable F) {σ A : ℝ}
    (h : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma σ)
      (fun omega : ℕ → ShellField d ↦ F (omega n)) A) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma σ)
      (fun omega : ℕ → ShellField d ↦ F (ShellField.translate z (omega n))) A := by
  rw [IndependentSums.isBigOWith_gammaSigma_iff] at h ⊢
  intro t ht
  have hX : Measurable
      (fun omega : ℕ → ShellField d ↦ F (ShellField.translate z (omega n))) :=
    (hF.comp (ShellField.measurable_translate z)).comp
      (ShellField.measurable_shellCoordinate n)
  have hY : Measurable (fun omega : ℕ → ShellField d ↦ F (omega n)) :=
    hF.comp (ShellField.measurable_shellCoordinate n)
  have hE : MeasurableSet {x : ℝ | A * t < x} :=
    measurableSet_lt measurable_const measurable_id
  calc
    P.toMeasure.real
          {omega | A * t < F (ShellField.translate z (omega n))} =
        (Measure.map
          (fun omega : ℕ → ShellField d ↦ F (ShellField.translate z (omega n)))
          P.toMeasure).real {x : ℝ | A * t < x} := by
      have hmapApply := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := P.toMeasure)
          hX.aemeasurable hE)
      exact hmapApply.symm
    _ = (Measure.map (fun omega : ℕ → ShellField d ↦ F (omega n))
          P.toMeasure).real {x : ℝ | A * t < x} := by
      rw [hPrefix.map_shellObservable_translate_eq n z F hF]
    _ = P.toMeasure.real {omega | A * t < F (omega n)} := by
      have hmapApply := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := P.toMeasure)
          hY.aemeasurable hE)
      exact hmapApply
    _ ≤ Real.exp (-(t ^ σ)) := h ht

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
