/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import SuperdiffusionCLT.Assumptions.ShellField.Actions

/-!
# Canonical laws and transformations of marginal shell sequences

The manuscript's probability space uses the canonical natural-number-indexed
sequence carrier `ℕ → ShellField d`. This file provides coordinate marginal
laws and the componentwise transformations needed to state stationarity, J2,
and J4. It introduces no probabilistic assumptions or invariance claims.

## Main definitions

* `shellMarginalLaw`: the law of one specified shell coordinate.
* `translateSequence`: simultaneous real translation of every shell.
* `negateSequence`: simultaneous negation of every shell.
* `rotateSequence`: simultaneous signed-permutation conjugation of every shell.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## Coordinate laws -/

/-- Evaluation of a shell sequence at a fixed natural-number coordinate is measurable. -/
theorem measurable_shellCoordinate (n : ℕ) :
    Measurable (fun F : ℕ → ShellField d ↦ F n) :=
  measurable_pi_apply n

/-- The exact marginal law of shell coordinate `n`. -/
noncomputable def shellMarginalLaw
    (P : MeasureTheory.ProbabilityMeasure (ℕ → ShellField d)) (n : ℕ) :
    MeasureTheory.ProbabilityMeasure (ShellField d) :=
  P.map (fun F ↦ F n)

/-! ## Componentwise whole-sequence transformations -/

/-- Simultaneously translate every shell by the same real vector. -/
def translateSequence (z : Vec d) (F : ℕ → ShellField d) :
    ℕ → ShellField d := fun n ↦ translate z (F n)

@[simp]
theorem translateSequence_apply (z : Vec d) (F : ℕ → ShellField d) (n : ℕ) :
    translateSequence z F n = translate z (F n) :=
  rfl

/-- Componentwise real translation is measurable on the whole sequence. -/
theorem measurable_translateSequence (z : Vec d) :
    Measurable (translateSequence (d := d) z) := by
  exact Measurable.of_eval fun n ↦
    (measurable_translate z).comp (measurable_pi_apply n)

/-- Simultaneously negate every shell in the sequence. -/
def negateSequence (F : ℕ → ShellField d) : ℕ → ShellField d :=
  fun n ↦ negate (F n)

@[simp]
theorem negateSequence_apply (F : ℕ → ShellField d) (n : ℕ) :
    negateSequence F n = negate (F n) :=
  rfl

/-- Componentwise negation is measurable on the whole sequence. -/
theorem measurable_negateSequence :
    Measurable (negateSequence (d := d)) := by
  exact Measurable.of_eval fun n ↦
    measurable_negate.comp (measurable_pi_apply n)

/-- Simultaneously apply one signed-permutation conjugation to every shell. -/
def rotateSequence (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (F : ℕ → ShellField d) : ℕ → ShellField d :=
  fun n ↦ rotate R hR (F n)

@[simp]
theorem rotateSequence_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (F : ℕ → ShellField d) (n : ℕ) :
    rotateSequence R hR F n = rotate R hR (F n) :=
  rfl

/-- Componentwise signed-permutation conjugation is measurable on the whole sequence. -/
theorem measurable_rotateSequence (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotateSequence (d := d) R hR) := by
  exact Measurable.of_eval fun n ↦
    (measurable_rotate R hR).comp (measurable_pi_apply n)

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
