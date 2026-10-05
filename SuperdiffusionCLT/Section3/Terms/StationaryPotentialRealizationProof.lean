/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.StationaryProjection
public import Homogenization.Sobolev.L2Ambient
public import Homogenization.Sobolev.H1.Definitions
public import Homogenization.Geometry.TriadicCube

/-!
# The `L²(Ω)` layer of the stationary potential realization

The statement `SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization`
asks for the cube `H¹` realization `uReal` of a stationary potential field, at the generality of a
probability carrier `Ω` carrying a measure-preserving translation action of `Vec d`.  This file
treats the
`L²(Ω)` layer of that statement, i.e. what its hypotheses say about the stationary fields
*before* the passage to a single sample.

The passage to a single sample needs more than the abstract hypotheses give: they contain only
`MeasurableConstVAdd (Vec d) Ω`, i.e. measurability of `ω ↦ x +ᵥ ω` for each fixed `x`, which is
all that the `L²(Ω)` layer uses, whereas the sample-wise argument (group mollification, smearing
of a cube test potential, differentiation under the cube integral) needs joint measurability of
`(x, ω) ↦ x +ᵥ ω`.  At the concrete carrier `ShellSeq d` the joint measurability is available
(`measurable_vadd_shellSeq` and `map_vadd_prod_eq` in `Section3/Terms/StationaryRealization.lean`).

## Main results

* `add_toLp_mem_stationarySolenoidalSubspace` — with the projection hypothesis `hproj`, the field
  `gradHatW + F (·) 0` of the response-field construction lies in the stationary solenoidal
  subspace, as the orthogonal remainder of the projection;
* `add_field_toLp_mem_stationarySolenoidalSubspace` — the same statement for the `L²(Ω)` class of
  the pointwise sum, which is the object the printed decomposition
  `F (·) 0 = gradHatW + (solenoidal)` is about.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Probability.Stationary
open scoped BigOperators ENNReal

noncomputable section

namespace SuperdiffusionCLT.Section3.Terms

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
  [VAddInvariantMeasure (Vec d) Ω μ]
variable {F : Ω → Vec d → Vec d} {gradHatW : Ω → Vec d}

section Cocycle

end Cocycle

section Projection

/-- **The solenoidal remainder lies in the stationary solenoidal subspace.**
This is the second half of the content of `hproj`: the printed claim that the stationary
potential field `gradHatW + F (·) 0` of the response-field construction is solenoidal.
With `hproj` that field is exactly `F (·) 0 - stationaryPotentialProjection (F (·) 0)`,
the orthogonal remainder of the projection
(`sub_stationaryPotentialProjection_mem_orthogonal`). -/
theorem add_toLp_mem_stationarySolenoidalSubspace
    {hF : MemLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)) 2 μ}
    {hG : MemLp (fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) 2 μ}
    (hproj : hG.toLp (fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := μ)
        (hF.toLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)))) :
    hG.toLp (fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) +
        hF.toLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)) ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) := by
  have h := sub_stationaryPotentialProjection_mem_orthogonal (μ := μ)
    (hF.toLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)))
  rw [hproj]
  rwa [sub_eq_add_neg, add_comm] at h

/-- **The `L²(Ω)` class of the printed stationary potential field is solenoidal.**
This is `add_toLp_mem_stationarySolenoidalSubspace` at the level of the field rather
than of its two summands: the class of the pointwise sum
`fun ω => ofVec (gradHatW ω) + ofVec (F ω 0)` is the sum of the two classes
(`MemLp.toLp_add`), and that is the object the printed decomposition
`F (·) 0 = gradHatW + (solenoidal)` is about. -/
theorem add_field_toLp_mem_stationarySolenoidalSubspace
    {hF : MemLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)) 2 μ}
    {hG : MemLp (fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) 2 μ}
    (hproj : hG.toLp (fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := μ)
        (hF.toLp (fun ω : Ω => HilbertVec.ofVec (F ω 0)))) :
    (hG.add hF).toLp (fun ω : Ω =>
        HilbertVec.ofVec (gradHatW ω) + HilbertVec.ofVec (F ω 0)) ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) := by
  change (hG.add hF).toLp ((fun ω : Ω => HilbertVec.ofVec (gradHatW ω)) +
    (fun ω : Ω => HilbertVec.ofVec (F ω 0))) ∈
      stationarySolenoidalSubspace (μ := μ) (d := d)
  rw [MemLp.toLp_add hG hF]
  exact add_toLp_mem_stationarySolenoidalSubspace (μ := μ) hproj

end Projection

section Witness

end Witness

end SuperdiffusionCLT.Section3.Terms
