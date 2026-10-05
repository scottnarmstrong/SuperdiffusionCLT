/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.StreamCutoff
public import SuperdiffusionCLT.Assumptions.ShellField.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The infrared cutoff of the marginal stream matrix

This module is the deterministic API of the infrared cutoff
`k_L = j_0 + ... + j_L` of the stream matrix. It reads the cutoff pointwise
and entrywise, records its measurability in the shell sequence and its
anti-symmetry, links it to the finite shell increment over a natural interval,
and exhibits its Frechet derivative, which is available because every shell of
the carrier stores its own derivative.

Nothing here assumes a shell law, independence, stationarity, or a
concentration estimate.

## Main definitions

* `streamCutoffDeriv`: the derivative of `k_L`, the sum of the stored shell
  derivatives.

## Main results

* `streamCutoff_apply`, `streamCutoff_apply_entry`: evaluation.
* `measurable_streamCutoff`: measurability in the shell sequence.
* `streamCutoff_skew`, `streamCutoff_skew_entry`: anti-symmetry.
* `streamCutoff_add_finiteShellIncrement`,
  `finiteShellIncrement_apply_eq_streamCutoff_sub`: the increment identities.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Evaluation, measurability, and anti-symmetry -/

/-- Matrix-valued evaluation of the infrared cutoff. -/
@[simp]
theorem streamCutoff_apply (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    streamCutoff omega L x = ∑ n ∈ Finset.range (L + 1), omega n x := by
  simp only [streamCutoff, RegCoeffField.finset_sum_apply, shellReg,
    ShellField.forgetShell_apply]

/-- Entrywise evaluation of the infrared cutoff. -/
@[simp]
theorem streamCutoff_apply_entry (omega : ShellSeq d) (L : ℕ) (x : Vec d)
    (i k : Fin d) :
    streamCutoff omega L x i k = ∑ n ∈ Finset.range (L + 1), omega n x i k := by
  rw [streamCutoff_apply]
  simp only [Matrix.sum_apply]

/-- The infrared cutoff is measurable on the shell-sequence carrier. -/
theorem measurable_streamCutoff (L : ℕ) :
    Measurable (fun omega : ShellSeq d ↦ streamCutoff omega L) := by
  unfold streamCutoff
  exact Finset.measurable_sum _ fun n _ ↦ measurable_shellReg n

/-- Entrywise anti-symmetry of the infrared cutoff, inherited from the shells
of the carrier. -/
theorem streamCutoff_skew_entry (omega : ShellSeq d) (L : ℕ) (x : Vec d)
    (i k : Fin d) :
    streamCutoff omega L x i k = -streamCutoff omega L x k i := by
  simp only [streamCutoff_apply_entry, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ ↦ ShellField.skew_entry (omega n) x i k

/-- The infrared cutoff is an anti-symmetric matrix field. -/
theorem streamCutoff_skew (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    matTranspose (streamCutoff omega L x) = -streamCutoff omega L x := by
  ext i k
  exact streamCutoff_skew_entry omega L x k i

/-! ## The increment identities -/

/-- The half-open natural interval decomposition behind the increment
identity. -/
private theorem range_succ_union_Ioc {n m : ℕ} (hnm : n ≤ m) :
    Finset.range (n + 1) ∪ Finset.Ioc n m = Finset.range (m + 1) := by
  ext k
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
  omega

/-- The additive form of the increment identity: the finite shell increment
over `(n, m]` transports `k_n` to `k_m`. -/
theorem streamCutoff_add_finiteShellIncrement (omega : ShellSeq d) {n m : ℕ}
    (hnm : n ≤ m) :
    streamCutoff omega n + finiteShellIncrement omega n m =
      streamCutoff omega m := by
  have hdisj : Disjoint (Finset.range (n + 1)) (Finset.Ioc n m) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ioc] at hk'
    omega
  rw [streamCutoff, streamCutoff, finiteShellIncrement,
    ← range_succ_union_Ioc hnm, Finset.sum_union hdisj]

/-- The subtraction form of the increment identity, stated pointwise because
`RegCoeffField d` is an additive monoid without negation:
`k_m(x) - k_n(x) = ∑_{l = n+1}^{m} j_l(x)`. -/
theorem finiteShellIncrement_apply_eq_streamCutoff_sub (omega : ShellSeq d)
    {n m : ℕ} (hnm : n ≤ m) (x : Vec d) :
    finiteShellIncrement omega n m x =
      streamCutoff omega m x - streamCutoff omega n x := by
  have h := congrArg (fun a : RegCoeffField d ↦ a x)
    (streamCutoff_add_finiteShellIncrement omega hnm)
  simp only [RegCoeffField.add_apply] at h
  rw [← h]
  abel

/-! ## The derivative of the cutoff -/

/-- The Frechet derivative of `k_L` at `x`, read off the derivative stored in
each shell of the carrier. -/
def streamCutoffDeriv (omega : ShellSeq d) (L : ℕ) (x : Vec d) :
    Vec d →L[ℝ] Mat d :=
  ∑ n ∈ Finset.range (L + 1), ShellField.deriv (omega n) x

end

end SuperdiffusionCLT.Section2.Cutoff
