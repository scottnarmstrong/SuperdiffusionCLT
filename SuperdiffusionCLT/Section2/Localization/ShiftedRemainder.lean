/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.AveragedRemainderProof
public import SuperdiffusionCLT.Section2.Localization.BlockScalarCorrespondence
public import SuperdiffusionCLT.Section2.Localization.Conj3CoincidentBranch
public import SuperdiffusionCLT.Section2.Localization.CutoffLocalizationAssembly
public import SuperdiffusionCLT.Section2.Localization.SlopeBoundRoute
public import Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The shifted remainder: the difference of the two shifted fields

## What the paper writes

Quoted verbatim, the passage in the proof of `l.localization.A` that fixes the object is:

> Fix~`p,q ∈ ℝ^d` and set~`P := (-p,q)`.  Let~`X` and~`X̃` be the minimizers in
> `e.J.P0.Dirichlet` for~`𝐀` and~`𝐀̃`, respectively, and write~`Z := X + P` and
> `Z̃ := X̃ + P`.

and, immediately after, the two fields are identified with the
doubled fields of the two pairs of scalar maximizers:

> `Z = ½ (∇u + ∇u*,  a∇u − aᵗ∇u*)`  and
> `Z̃ = ½ (∇ũ + ∇ũ*,  ã∇ũ − ãᵗ∇ũ*)`.

The left-hand side of the printed estimate is therefore

* `Z − Z̃ = (X + P) − (X̃ + P) = X − X̃`.

Both fields carry the **same** shift `P`, so the shift cancels in the difference:
the printed object is the difference of two fields that are each admissible at
the loading `(-p,q)`, and its potential slot is the difference of two
zero-trace potentials, hence has **zero** mean.  Nothing in the paper ever forms
`P − (Z − Z̃)`.

## The route's carrier, and the divergence

The route's earlier carrier was

* `(p, q) − (Z − Zt)`,

that is, the constant split loading minus the difference of the two shifted
fields.  The loading does **not** cancel there: its potential slot averages to
`p`, so the averaged remainder hypothesis is refuted at a vanishing window.

This module defines the object the paper actually uses.

## Main results

* `conj3ShiftedPairRemainder` — the shifted remainder, the difference
  `Z − Zt` of the two shifted fields of the route's forward maximizers.

The potential slot of a difference of two fields admissible at the same loading
`(-p,q)` averages to `0`, in contrast to the route's earlier carrier, whose
potential slot averages to `p`.  Dimension one is out of scope.  Names from other
namespaces are fully qualified.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The shifted remainder -/

/-- **The shifted remainder.**  The difference of the two *shifted* fields of the
route's forward maximizers: `Z − Zt` with `Z` and `Zt` the doubled fields
admissible at the loading `(-p,q)`.  This is the paper's object
`Z − Z̃ = (X + P) − (X̃ + P) = X − X̃`: the shift `P` is carried by both fields and
therefore cancels.  Its potential slot is the difference of the two potentials,
whose mean is `0`, in contrast to the route's earlier carrier
`(p, q) − (Z − Zt)`, whose potential slot has mean `p`. -/
noncomputable def conj3ShiftedPairRemainder {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) : Vec d → BlockVec d :=
  fun x => (routeDoubledFieldM U nu hnu omega m p q v).eval x -
    (routeDoubledFieldL U nu hnu omega m L hmL p q u).eval x

end

end SuperdiffusionCLT.Section2.Localization
