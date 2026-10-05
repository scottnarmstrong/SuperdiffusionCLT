/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.StationaryRealization
public import SuperdiffusionCLT.Section3.Terms.StationaryPotentialRealizationProof

/-!
# The stationary-potential realization at the concrete carrier `ShellSeq d`

The statement `SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization` is
formulated for an abstract probability carrier `Ω` with a
measure-preserving translation action of `Vec d`.
This file provides the measurability and transfer facts at the concrete carrier `Ω = ShellSeq d`
that the sample-wise passage needs and that the abstract hypotheses do not supply:

* `instMeasurableVAdd₂ShellSeq` — the joint measurability of the action,
  `MeasurableVAdd₂ (Vec d) (ShellSeq d)`, which the abstract layer does not have and which the
  sample-wise technique needs;
* `measurable_vadd_spaceFirst_shellSeq`, `measurable_vadd_const_sample_shellSeq` — the fixed- and
  joint-variable measurability of the spatial realization `x ↦ X (x +ᵥ ω)` of a shell-sequence
  field;
* `vaddMeasurableEquivShellSeq` — the translation by a fixed vector as a measurable equivalence;
* `integral_comp_vadd_shellSeq` — the real-shift transfer of expectations at the concrete
  carrier, the identity that converts every cube average into an abstract `L²(Ω)` quantity;
* `lintegral_cubeAverage_vadd_shellSeq` — the averaged abstract-to-space transfer
  `E_ω h(ω) = E_ω E_x h(x +ᵥ ω)`, i.e. the integrated form of `map_vadd_prod_eq`.

The averaged transfer identifies the space variable only in the mean: passing from the
`L²(Ω)`-orthogonality of the stationary field `H = gradHatW + F (·) 0` to stationary potential
gradients to the per-sample weak equation `∫ x in U, vecDot (H (x +ᵥ ω)) (∇φ x) = 0` for a.e. `ω`
is additional input, since a cube test function `φ_0 ∈ H¹₀(U)` is not a stationary field on `Ω`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators ENNReal

noncomputable section

namespace SuperdiffusionCLT.Section3.Terms

variable {d : ℕ}

/-! ## Joint measurability of the action on the concrete carrier -/

/-- **The joint measurability of the translation action on shell sequences**, as a
Mathlib instance: `MeasurableVAdd₂ (Vec d) (ShellSeq d)`, i.e. measurability of the
*uncurried* map `(x, ω) ↦ x +ᵥ ω`.

This is the class that the abstract statement's `MeasurableConstVAdd (Vec d) Ω`
does not supply and that no instance derives from it; at `ShellSeq d` it is
available, from `measurable_vadd_shellSeq`
(in `Section3/Terms/StationaryRealization.lean`). -/
instance instMeasurableVAdd₂ShellSeq : MeasurableVAdd₂ (Vec d) (ShellSeq d) :=
  ⟨(measurable_vadd_shellSeq (d := d)).comp measurable_swap⟩

/-- The same joint measurability in the argument order `(space, sample)`, which is
the order of the product `μ.prod (volume.restrict U)` used by Fubini. -/
theorem measurable_vadd_spaceFirst_shellSeq :
    Measurable (fun p : Vec d × ShellSeq d => p.1 +ᵥ p.2) :=
  measurable_vadd (M := Vec d) (α := ShellSeq d)

/-- The translation at a *fixed* sample is measurable in the space variable. -/
theorem measurable_vadd_const_sample_shellSeq (ω : ShellSeq d) :
    Measurable (fun x : Vec d => x +ᵥ ω) :=
  (measurable_vadd_spaceFirst_shellSeq (d := d)).comp
    (measurable_id.prodMk measurable_const)

/-- The translation of a shell sequence by a fixed vector, as a measurable
equivalence (`ω ↦ x +ᵥ ω` with inverse `ω ↦ -x +ᵥ ω`). -/
def vaddMeasurableEquivShellSeq (x : Vec d) : ShellSeq d ≃ᵐ ShellSeq d where
  toFun := fun ω => x +ᵥ ω
  invFun := fun ω => (-x) +ᵥ ω
  left_inv := by
    intro ω
    show (-x) +ᵥ (x +ᵥ ω) = ω
    rw [vadd_vadd, neg_add_cancel, zero_vadd]
  right_inv := by
    intro ω
    show x +ᵥ ((-x) +ᵥ ω) = ω
    rw [vadd_vadd, add_neg_cancel, zero_vadd]
  measurable_toFun := measurable_const_vadd x
  measurable_invFun := measurable_const_vadd (-x)

/-! ## The stationary transfer of expectations on the concrete carrier -/

section Transfer

variable {P : ProbabilityMeasure (ShellSeq d)}
variable [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]

/-- **Stationary expectations at the concrete carrier.**  For the translation
invariant law `P.toMeasure` and any `g`, the expectation of a translated sample is
the expectation of the sample.  This is the real-shift Koopman transfer
underlying every conversion of a cube average into an abstract `L²(Ω)` quantity,
proved here at `ShellSeq d` from `VAddInvariantMeasure` alone. -/
theorem integral_comp_vadd_shellSeq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ShellSeq d → E) (x : Vec d) :
    ∫ ω, g (x +ᵥ ω) ∂P.toMeasure = ∫ ω, g ω ∂P.toMeasure :=
  (measurePreserving_const_vadd (μ := P.toMeasure) (Ω := ShellSeq d) x).integral_comp'
    (f := vaddMeasurableEquivShellSeq x) g

/-- **The averaged abstract-to-space transfer at the concrete carrier.**  For a
measurable `h` on shell sequences, its `P.toMeasure`-expectation equals its
expectation over the product of the law with the normalized cube measure, i.e. its
average over all spatial translations `ω ↦ x +ᵥ ω` of the sample:

`E_ω h(ω) = E_ω E_x h(x +ᵥ ω)`.

This is the integrated form of the pushforward identity `map_vadd_prod_eq`
(in `Section3/Terms/StationaryRealization.lean`).  It is stated for an arbitrary
measurable `h`; the *inner* integral `∫⁻ x, h (x +ᵥ ω)` is an average over the space
variable for *each fixed* `ω`, and nothing here identifies that average with its
integrand at a.e. `ω`. -/
theorem lintegral_cubeAverage_vadd_shellSeq {Q : TriadicCube d}
    {h : ShellSeq d → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ ω, h ω ∂P.toMeasure =
      ∫⁻ ω, ∫⁻ x, h (x +ᵥ ω) ∂(normalizedCubeMeasure Q) ∂P.toMeasure := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hjoint : AEMeasurable (fun p : ShellSeq d × Vec d => h (p.2 +ᵥ p.1))
      (P.toMeasure.prod (normalizedCubeMeasure Q)) :=
    (hh.comp (measurable_vadd_shellSeq (d := d))).aemeasurable
  have hmp : MeasurePreserving (fun p : ShellSeq d × Vec d => p.2 +ᵥ p.1)
      (P.toMeasure.prod (normalizedCubeMeasure Q)) P.toMeasure :=
    ⟨measurable_vadd_shellSeq (d := d), map_vadd_prod_eq (P := P) (Q := Q)⟩
  have h1 : ∫⁻ p : ShellSeq d × Vec d, h (p.2 +ᵥ p.1)
        ∂(P.toMeasure.prod (normalizedCubeMeasure Q)) = ∫⁻ ω, h ω ∂P.toMeasure :=
    hmp.lintegral_comp hh
  have h2 : ∫⁻ p : ShellSeq d × Vec d, h (p.2 +ᵥ p.1)
        ∂(P.toMeasure.prod (normalizedCubeMeasure Q)) =
        ∫⁻ ω, ∫⁻ x, h (x +ᵥ ω) ∂(normalizedCubeMeasure Q) ∂P.toMeasure :=
    lintegral_prod (fun p : ShellSeq d × Vec d => h (p.2 +ᵥ p.1)) hjoint
  exact h1.symm.trans h2

end Transfer

/-! ## The `L²(Ω)` layer at the concrete carrier -/

section Pairing

variable {P : ProbabilityMeasure (ShellSeq d)}
variable [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]

end Pairing

/-! ## The statement, instantiated -/

section Concrete

variable {P : ProbabilityMeasure (ShellSeq d)}
variable [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]

end Concrete

/-! ## Non-vacuity of the conclusion at the concrete carrier -/

section ZeroDatum

variable {P : ProbabilityMeasure (ShellSeq d)}

end ZeroDatum

/-! ## Inhabitation of the hypothesis class at `ShellSeq d` -/

section Hypotheses

variable {P : ProbabilityMeasure (ShellSeq d)}
variable [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]

end Hypotheses

end SuperdiffusionCLT.Section3.Terms
