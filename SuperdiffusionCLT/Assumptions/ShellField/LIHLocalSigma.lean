/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.Basic

/-!
# The local integral sigma-field for marginal shell fields

`lihLocalSigma U` is the pullback of the CoarseGraining library's integral-generated
`Homogenization.LocalSigmaR U` along `ShellField.forgetShell`. It carries the
measurability of supported entry-test observables and is dominated by the
canonical Borel sigma-field on shell fields.

The definition deliberately contains no point-evaluation or restriction
sigma-fields.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Filter Homogenization MeasureTheory Topology

noncomputable section

variable {d : ℕ}

/-- The shell-field pullback of the CoarseGraining library's local integral sigma-field. -/
@[instance_reducible]
def lihLocalSigma (U : Set (Vec d)) : MeasurableSpace (ShellField d) :=
  MeasurableSpace.comap (forgetShell (d := d)) (LocalSigmaR U)

/-- A supported entry-test observable, pulled back to shell fields, is
measurable from `lihLocalSigma U`. -/
theorem measurable_entryTestR_forgetShell_lihLocalSigma (U : Set (Vec d))
    (i k : Fin d) {psi : Vec d → ℝ} (hpsi : IsProbeR psi)
    (hpsiSupport : Function.support psi ⊆ U) :
    @Measurable (ShellField d) ℝ (lihLocalSigma U) (borel ℝ)
      (fun j ↦ entryTestR i k psi (forgetShell j)) := by
  have hentry : @Measurable (RegCoeffField d) ℝ (LocalSigmaR U) (borel ℝ)
      (entryTestR i k psi) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, k, psi, hpsi, hpsiSupport, t, ht, rfl⟩
  have hforget : @Measurable (ShellField d) (RegCoeffField d)
      (lihLocalSigma U) (LocalSigmaR U) forgetShell := by
    exact Measurable.of_comap_le le_rfl
  exact hentry.comp hforget

/-- The pulled-back local integral sigma-field is contained in the canonical
Borel sigma-field on shell fields. -/
theorem lihLocalSigma_le_borel (U : Set (Vec d)) :
    lihLocalSigma U ≤
      (inferInstance : MeasurableSpace (ShellField d)) := by
  calc
    lihLocalSigma U
        ≤ MeasurableSpace.comap forgetShell
            (inferInstance : MeasurableSpace (RegCoeffField d)) :=
      MeasurableSpace.comap_mono (LocalSigmaR_le U)
    _ ≤ (inferInstance : MeasurableSpace (ShellField d)) :=
      measurable_forgetShell.comap_le

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
