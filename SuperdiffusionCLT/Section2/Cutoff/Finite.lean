/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.RegCoeffField.Sigma
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw

/-!
# Finite marginal infrared increments

This module provides the finite natural-shell sums used in the first marginal
estimates. It contains no infinite cutoff and no scaling law.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The canonical natural-indexed shell-sequence sample carrier. -/
abbrev ShellSeq (d : ℕ) :=
  ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d

/-- One shell coordinate realized as a regular coefficient field of the
CoarseGraining library. -/
def shellReg (omega : ShellSeq d) (n : ℕ) : RegCoeffField d :=
  SuperdiffusionCLT.Frozen.Assumptions.ShellField.forgetShell (omega n)

/-- A regular-field shell coordinate is measurable on the sequence carrier.
-/
theorem measurable_shellReg (n : ℕ) :
    Measurable (fun omega : ShellSeq d ↦ shellReg omega n) :=
  SuperdiffusionCLT.Frozen.Assumptions.ShellField.measurable_forgetShell.comp
    (measurable_pi_apply n)

/-- The finite stream increment over the literal natural interval `(n,m]`.
-/
def finiteShellIncrement (omega : ShellSeq d) (n m : ℕ) : RegCoeffField d :=
  ∑ k ∈ Finset.Ioc n m, shellReg omega k

/-- Matrix-valued evaluation of a finite stream increment. -/
@[simp]
theorem finiteShellIncrement_apply (omega : ShellSeq d) (n m : ℕ) (x : Vec d) :
    finiteShellIncrement omega n m x =
      ∑ k ∈ Finset.Ioc n m, shellReg omega k x := by
  simp only [finiteShellIncrement, RegCoeffField.finset_sum_apply]

/-- Entrywise evaluation of a finite stream increment. -/
@[simp]
theorem finiteShellIncrement_apply_entry (omega : ShellSeq d) (n m : ℕ)
    (x : Vec d) (i k : Fin d) :
    finiteShellIncrement omega n m x i k =
      ∑ l ∈ Finset.Ioc n m, omega l x i k := by
  rw [finiteShellIncrement_apply]
  simp only [Matrix.sum_apply]
  rfl

/-- Finite stream increments are measurable as regular coefficient fields. -/
theorem measurable_finiteShellIncrement (n m : ℕ) :
    Measurable (fun omega : ShellSeq d ↦ finiteShellIncrement omega n m) := by
  unfold finiteShellIncrement
  exact Finset.measurable_sum _ fun k _ ↦ measurable_shellReg k

/-- Every finite stream increment remains skew-symmetric. -/
theorem finiteShellIncrement_skew (omega : ShellSeq d) (n m : ℕ) (x : Vec d) :
    (finiteShellIncrement omega n m x).transpose =
      -finiteShellIncrement omega n m x := by
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply,
    finiteShellIncrement_apply_entry]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  exact SuperdiffusionCLT.Frozen.Assumptions.ShellField.skew_entry
    (omega l) x k i

end

end SuperdiffusionCLT.Section2.Cutoff
