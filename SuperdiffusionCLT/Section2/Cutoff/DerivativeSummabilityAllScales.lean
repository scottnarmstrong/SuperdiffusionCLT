/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import SuperdiffusionCLT.Section2.Carriers.ShellDerivLinftyNorm
public import SuperdiffusionCLT.Section2.Cutoff.DerivativeSummability

/-!
# Almost-sure summability of the shell derivative norms at every scale

The cutoff approximation lemma `l.cutoff.approximation` has as hypothesis the
pointwise `L∞` summability

> `∑_{k=0}^∞ ‖∇ j_k‖_{L∞(U)} < ∞`

and a remark in its proof records that, for every fixed bounded `U`,
this hypothesis holds almost surely. The module
`SuperdiffusionCLT.Section2.Cutoff.DerivativeSummability` derives that
remark for one fixed `U` contained in a natural open cube.

The "Moreover" block of the stream-increment scale estimates (the statement of
`SuperdiffusionCLT.Frozen.Section2.streamIncrement_scale_estimates`)
quantifies that block almost surely *under a guard*: the conjunction over
every natural cube `cu_i` of the summability of the series of shell
derivative norms on that cube,

> `∀ i, ∑_{k=0}^∞ ‖∇ j_k‖_{L∞(cu_i)} < ∞`,

which is exactly the hypothesis of the cutoff approximation lemma
with `U = cu_i` for every `i` at once. This module proves that the guard holds
almost surely.

Since the guard is a countable conjunction of full-measure events, and
`MeasureTheory.ae_all_iff` passes a countable family of full-measure
statements to their single full-measure conjunction, the guard holds almost
surely: the single-cube result of
`SuperdiffusionCLT.Section2.Cutoff.DerivativeSummability` applied with
`U = cu_i` gives, for each fixed `i`, the full-measure statement
`∀ᵐ omega ∂P.toMeasure, Summable (fun k => ‖∇ j_k‖_{L∞(cu_i)})`, and
`MeasureTheory.ae_all_iff` reassembles the countable family into one event.
No probabilistic input beyond the single-cube result is needed; in
particular the covering caveat of its docstring is irrelevant
here, because the set is itself a natural cube.

## Main results

* `eventually_summable_shellDerivLinftyNorm_originCube`: the single-scale
  event, the instance of
  `SuperdiffusionCLT.Section2.Cutoff.eventually_summable_shellDerivLinftyNorm`
  at `U = cu_i`.
* `ae_forall_summable_shellDerivLinftyNorm_originCube`: the guard of the
  "Moreover" block, the countable conjunction of the single-scale events,
  almost surely.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Carriers

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

/-! ## The guard of the "Moreover" block -/

/-- **The single scale.** Under the J3 assumption,
the remark in the proof of `l.cutoff.approximation` gives the convergence of the
series of shell derivative norms on one fixed natural cube `cu_i` almost surely:

`∀ᵐ omega ∂P.toMeasure, Summable (fun k => ‖∇ j_k‖_{L∞(cu_i)})`.

This is
`eventually_summable_shellDerivLinftyNorm` with `U` the natural open cube of
scale `i` itself, so the cube-containment hypothesis is the identity subset:
no covering of `U` by cubes is needed. -/
theorem eventually_summable_shellDerivLinftyNorm_originCube
    (hJ3 : ShellLawJ3 d P) (i : ℕ) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      Summable fun k : ℕ =>
        shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k) := by
  have hU : openCubeSet (originCube d (i : ℤ)) ⊆
      openCubeSet (originCube d (i : ℤ)) := subset_refl _
  exact eventually_summable_shellDerivLinftyNorm hJ3 hU

/-- **The summability guard is a full-measure event.** Under the
J3 assumption, almost surely the series of shell derivative norms
converges on *every* natural cube at once:

`∀ᵐ omega ∂P.toMeasure, ∀ i, Summable (fun k => ‖∇ j_k‖_{L∞(cu_i)})`.

This is the guard with which the "Moreover" block of the stream-increment
scale estimates is quantified, the hypothesis
of the cutoff approximation lemma for every `U = cu_i`
simultaneously, so the block's clauses can be proved on that single event.
It is the countable conjunction of the single-scale events of
`eventually_summable_shellDerivLinftyNorm_originCube`, reassembled by
`MeasureTheory.ae_all_iff` — the countable-conjunction passage from a family
of full-measure statements, indexed by the countable set of scales, to the
single event on which all of them hold. -/
theorem ae_forall_summable_shellDerivLinftyNorm_originCube
    (hJ3 : ShellLawJ3 d P) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∀ i : ℕ, Summable fun k : ℕ =>
        shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k) :=
  MeasureTheory.ae_all_iff.mpr fun i =>
    eventually_summable_shellDerivLinftyNorm_originCube hJ3 i

end

end SuperdiffusionCLT.Section2.Cutoff