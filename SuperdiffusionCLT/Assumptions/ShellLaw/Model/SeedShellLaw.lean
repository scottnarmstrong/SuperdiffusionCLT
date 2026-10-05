/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedCovarianceE
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellDilationB

/-!
# The seed shell law

`nv_seedShellLaw d ε` is the law of the skew-matrix field whose entries `(i, j)`, `i < j`, are
independent copies of the scalar Gaussian seed `nv_seedLaw d ε`, with `k_{ji} = -k_{ij}` and zero
diagonal. It is the push-forward of the product measure `Measure.pi` under `assembleSkew`.

* `nv_seedShellLaw`, `nv_seedShellLaw_toMeasure`
* `nv_seedShellLaw_map_eq`: the push-forward of the seed shell law under a measurable map is the
  push-forward of the product of the scalar seeds under the composite with `assembleSkew`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- The product of independent scalar seeds over the index set of strictly upper entries. -/
def nv_seedProduct (d : ℕ) (ε : ℝ) : Measure (SkewIdx d → ScalarC2Field d) :=
  Measure.pi fun _ : SkewIdx d ↦ (nv_seedLaw d ε)

instance nv_seedProduct_isProbability (d : ℕ) (ε : ℝ) :
    IsProbabilityMeasure (nv_seedProduct d ε) := by
  unfold nv_seedProduct
  infer_instance

/-- The measure underlying the seed shell law. -/
def nv_seedShellMeasure (d : ℕ) (ε : ℝ) : Measure (ShellField d) :=
  (nv_seedProduct d ε).map assembleSkew

instance nv_seedShellMeasure_isProbability (d : ℕ) (ε : ℝ) :
    IsProbabilityMeasure (nv_seedShellMeasure d ε) := by
  unfold nv_seedShellMeasure
  infer_instance

/-- The **seed shell law**: the entries `(i, j)`, `i < j`, are independent copies of the scalar
seed, `k_{ji} = -k_{ij}`, and the diagonal vanishes. -/
def nv_seedShellLaw (d : ℕ) (ε : ℝ) : ProbabilityMeasure (ShellField d) :=
  ⟨nv_seedShellMeasure d ε, nv_seedShellMeasure_isProbability d ε⟩

theorem nv_seedShellLaw_toMeasure (d : ℕ) (ε : ℝ) :
    (nv_seedShellLaw d ε).toMeasure =
      Measure.map assembleSkew (Measure.pi fun _ : SkewIdx d ↦ (nv_seedLaw d ε)) :=
  rfl

instance nv_seedShellLaw_isProbability (d : ℕ) (ε : ℝ) :
    IsProbabilityMeasure (nv_seedShellLaw d ε).toMeasure :=
  nv_seedShellMeasure_isProbability d ε

/-- The seed shell law feeds directly into the dilation family. -/
example (d : ℕ) (ε : ℝ) (n : ℕ) : ProbabilityMeasure (ShellField d) :=
  scaledShellLaw (nv_seedShellLaw d ε) n

/-- Integrals against the seed shell law are integrals of the assembled field. -/
theorem nv_seedShellLaw_map_eq (d : ℕ) (ε : ℝ) {β : Type*} [MeasurableSpace β]
    (G : ShellField d → β) (hG : Measurable G) :
    (nv_seedShellLaw d ε).toMeasure.map G =
      (nv_seedProduct d ε).map (fun φ ↦ G (assembleSkew φ)) := by
  rw [nv_seedShellLaw_toMeasure, Measure.map_map hG measurable_assembleSkew]
  rfl

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
