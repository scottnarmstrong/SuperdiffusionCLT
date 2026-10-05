/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix
public import SuperdiffusionCLT.Section2.Cutoff.Finite

/-!
# Stationarity of a finite block of shells

One shell of the marginal stream matrix is stationary by the prefix assumption, and
the shells are mutually independent by J2. This file upgrades those two
one-coordinate facts to the joint law of the whole sequence and then to the law
of the finite increment `finiteShellIncrement omega n m` on the CoarseGraining library's regular
coefficient fields.

## Main results

* `SuperdiffusionCLT.Probability.map_coordinatewise_eq_of_iIndepFun_coordinates`:
  a general product-space statement — independent coordinates whose marginals
  are preserved by given coordinate maps have a jointly preserved law.
* `SuperdiffusionCLT.Frozen.Assumptions.ShellField.map_translateSequence_eq`:
  the joint law of the shell sequence is invariant under the simultaneous real
  translation of every shell.
* `SuperdiffusionCLT.Section2.Cutoff.blockRegLaw_stationary`: the law of a
  finite shell block is invariant under the CoarseGraining library's `translateReg`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Probability

open MeasureTheory ProbabilityTheory

/-- If the coordinates of a product space are mutually independent under `μ` and
each `f i` preserves the `i`th coordinate marginal, then `μ` itself is preserved
by the simultaneous coordinatewise transformation. -/
theorem map_coordinatewise_eq_of_iIndepFun_coordinates
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsProbabilityMeasure μ]
    (hindep : iIndepFun (fun i (x : ∀ i, X i) ↦ x i) μ)
    (f : ∀ i, X i → X i) (hf : ∀ i, Measurable (f i))
    (hmap : ∀ i, Measure.map (f i) (Measure.map (fun x : ∀ i, X i ↦ x i) μ) =
      Measure.map (fun x : ∀ i, X i ↦ x i) μ) :
    Measure.map (fun (x : ∀ i, X i) i ↦ f i (x i)) μ = μ := by
  have hprob :
      ∀ i, IsProbabilityMeasure (Measure.map (fun x : ∀ i, X i ↦ x i) μ) :=
    fun _ ↦ inferInstance
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map (P := μ)
      (X := fun i (x : ∀ i, X i) ↦ x i) (fun i ↦ measurable_pi_apply i)).1 hindep
  have hid : (fun (x : ∀ i, X i) (i : ι) ↦ x i) = id := rfl
  rw [hid, Measure.map_id] at hprod
  calc
    Measure.map (fun (x : ∀ i, X i) i ↦ f i (x i)) μ =
        Measure.map (fun (x : ∀ i, X i) i ↦ f i (x i))
          (Measure.infinitePi
            (fun i ↦ Measure.map (fun x : ∀ i, X i ↦ x i) μ)) := by
      rw [← hprod]
    _ = Measure.infinitePi
          (fun i ↦ Measure.map (f i) (Measure.map (fun x : ∀ i, X i ↦ x i) μ)) :=
      Measure.infinitePi_map_pi _ hf
    _ = Measure.infinitePi (fun i ↦ Measure.map (fun x : ∀ i, X i ↦ x i) μ) :=
      congrArg Measure.infinitePi (funext hmap)
    _ = μ := hprod.symm

end SuperdiffusionCLT.Probability

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization MeasureTheory ProbabilityTheory

variable {d : ℕ} {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- Per-shell stationarity and mutual independence give joint stationarity of
the whole shell sequence under the simultaneous real translation. -/
theorem map_translateSequence_eq (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (z : Vec d) :
    Measure.map (translateSequence z) P.toMeasure = P.toMeasure :=
  SuperdiffusionCLT.Probability.map_coordinatewise_eq_of_iIndepFun_coordinates
    P.toMeasure hJ2.independent (fun _ ↦ translate z)
    (fun _ ↦ measurable_translate z) (fun n ↦ hPrefix.stationary n z)

end SuperdiffusionCLT.Frozen.Assumptions.ShellField

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- Translating a finite shell block as a regular coefficient field is the same
as translating every shell of the underlying sequence. -/
theorem translateReg_finiteShellIncrement (z : Vec d) (omega : ShellSeq d)
    (n m : ℕ) :
    translateReg z (finiteShellIncrement omega n m) =
      finiteShellIncrement (ShellField.translateSequence z omega) n m := by
  refine RegCoeffField.ext fun x ↦ ?_
  rw [translateReg_apply, finiteShellIncrement_apply, finiteShellIncrement_apply]
  exact Finset.sum_congr rfl fun k _ ↦ rfl

/-- The law of the finite shell block `(n, m]` on the CoarseGraining library's
regular coefficient fields. -/
def blockRegLaw (P : ProbabilityMeasure (ℕ → ShellField d)) (n m : ℕ) :
    ProbabilityMeasure (RegCoeffField d) :=
  P.map (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m)

theorem blockRegLaw_toMeasure (P : ProbabilityMeasure (ℕ → ShellField d))
    (n m : ℕ) :
    (blockRegLaw P n m).toMeasure =
      Measure.map (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m)
        P.toMeasure :=
  rfl

/-- The law of a finite shell block is invariant under every real translation of
the regular coefficient field. -/
theorem blockRegLaw_stationary (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (n m : ℕ) (z : Vec d) :
    Measure.map (translateReg z) (blockRegLaw P n m).toMeasure =
      (blockRegLaw P n m).toMeasure := by
  rw [blockRegLaw_toMeasure]
  calc
    Measure.map (translateReg z)
          (Measure.map (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m)
            P.toMeasure) =
        Measure.map (fun omega : ShellSeq d ↦
          translateReg z (finiteShellIncrement omega n m)) P.toMeasure :=
      Measure.map_map (measurable_translateReg z)
        (measurable_finiteShellIncrement n m)
    _ = Measure.map ((fun omega : ShellSeq d ↦ finiteShellIncrement omega n m) ∘
          ShellField.translateSequence z) P.toMeasure := by
      refine congrArg
        (fun g : ShellSeq d → RegCoeffField d ↦ Measure.map g P.toMeasure) ?_
      funext omega
      exact translateReg_finiteShellIncrement z omega n m
    _ = Measure.map (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m)
          (Measure.map (ShellField.translateSequence z) P.toMeasure) :=
      (Measure.map_map (measurable_finiteShellIncrement n m)
        (ShellField.measurable_translateSequence z)).symm
    _ = Measure.map (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m)
          P.toMeasure := by
      rw [ShellField.map_translateSequence_eq hPrefix hJ2 z]

end

end SuperdiffusionCLT.Section2.Cutoff
