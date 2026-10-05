/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Probability.RegCoeffField.RestrictionBridge
public import SuperdiffusionCLT.Assumptions.ShellField.LIHLocalSigma

/-!
# The pointwise-restriction sigma-field for marginal shell fields

`shellRestrictionSigma U hU` is the pullback along `ShellField.forgetShell` of
the CoarseGraining library's `Homogenization.RestrictionSigmaR U hU`, the comap of the canonical
carrier sigma-algebra along the pointwise restriction `a |-> 1_U a`. It is the
lane in which `CoarseGraining`'s high-contrast entry theorem states range of
dependence, and the shell-level counterpart of the local integral lane
`ShellField.lihLocalSigma` of `LIHLocalSigma.lean`.

The two lanes differ exactly by the point evaluations `a |-> a x` for `x` in
`U`; the only comparison `CoarseGraining` supplies,
`Homogenization.localSigmaR_le_restrictionSigmaR`, puts the integral lane below
the restriction lane, and that inequality is recorded here as
`lihLocalSigma_le_shellRestrictionSigma`.

This is a deterministic carrier module: it assumes no shell law, independence,
stationarity, or concentration estimate.

## Main definitions

* `shellRestrictionSigma`: the shell-level pointwise-restriction sigma-field.

## Main results

* `shellRestrictionSigma_le`: it is dominated by the canonical Borel sigma-field.
* `lihLocalSigma_le_shellRestrictionSigma`: the integral lane is below it.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The shell-level pointwise-restriction sigma-field: the comap along the map
that restricts a shell, read as a regular coefficient field, to `U`. It is the
shell-level counterpart of `CoarseGraining`'s `RestrictionSigmaR`. -/
@[instance_reducible]
def shellRestrictionSigma (U : Set (Vec d)) (hU : MeasurableSet U) :
    MeasurableSpace (ShellField d) :=
  MeasurableSpace.comap
    (fun j : ShellField d ↦ restrictReg U hU (forgetShell j)) inferInstance

theorem shellRestrictionSigma_le (U : Set (Vec d)) (hU : MeasurableSet U) :
    shellRestrictionSigma U hU ≤ (shellFieldMeasurableSpace d) :=
  ((measurable_restrictReg U hU).comp measurable_forgetShell).comap_le

/-- The inequality `CoarseGraining` supplies, pulled back to shell fields: the
integral lane is below the pointwise-restriction lane. -/
theorem lihLocalSigma_le_shellRestrictionSigma (U : Set (Vec d)) (hU : MeasurableSet U) :
    lihLocalSigma U ≤ shellRestrictionSigma U hU := by
  have h : MeasurableSpace.comap (forgetShell (d := d)) (LocalSigmaR U) ≤
      MeasurableSpace.comap (forgetShell (d := d)) (RestrictionSigmaR U hU) :=
    MeasurableSpace.comap_mono (localSigmaR_le_restrictionSigmaR U hU)
  rwa [RestrictionSigmaR, MeasurableSpace.comap_comp] at h

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
