/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section3.Terms.GluedFieldAnnealedFiniteness

/-!
# `l.RHS.term2`: measurability for the difference of the two proxy fields

The statement `SuperdiffusionCLT.Frozen.Section3.rhs_term2` needs the `AEMeasurable`
property of the two annealed cube norms of the proxy fields.  This module proves it, at the
data of that statement:

* `term2_ob5_measurableDifference`: the observable
  `omega ↦ ‖∇u_n − ∇ũ_n‖_{L̲²(cu_m)}` is `P`-a.e. measurable.  This is the half
  left open by the module `GluedFieldAnnealedFiniteness`, whose squared observable
  contains the cross cube average of the two maximizers.
* `term2_ob5_measurable`: both observables together, in the form needed for the
  display of `l.RHS.term2`.

## The route

The `L̲²(cu_m)` class of the glued gradient field is a measurable function of
the sample (`measurable_gluedGradientClass` of
`MaximizerCoefficientStabilityB`, which reads the
coefficient-stability estimate `norm_gradToHilbertVectorL2_sub_le_of_
isResponseMaximizer` as a Lipschitz modulus of the cube maximizer in the
sample, hence continuity, hence measurability on the Borel sample carrier).
The class of a pointwise difference of two `L²` fields is the difference of
the two classes (`toHilbertVectorL2OfVecField_sub`), the `enorm` is continuous
on the class space (`continuous_enorm`), and the cube norm is a fixed constant
multiple of the `enorm` of the class
(`vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField` of
`ResponseMeasurability.lean`).  So the observable of `‖∇u_n − ∇ũ_n‖_{L̲²(cu_m)}`
is a constant multiple of a continuous image of a difference of two measurable
class maps: no selection of a maximizer enters, and the cross cube average of
the two maximizers that blocked the identity route never appears.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The class of the difference of two glued fields -/

/-- The `L²(cu_m)` class of the pointwise difference of two glued gradient
fields of `e.u.k.def` is the difference of the two classes: the pointwise
difference is `L²` on the cube (`MemVectorL2.sub`) and the class map subtracts
(`toHilbertVectorL2OfVecField_sub`). -/
theorem class_gluedGradientField_sub {nu : ℝ} (hnu : 0 < nu) (L₁ L₂ k m : ℕ)
    (F : Vec d) (omega : ShellSeq d) (Q : TriadicCube d) :
    toHilbertVectorL2OfVecField
        ((memVectorL2_openCubeSet_gluedGradientField hnu L₁ k m F omega Q).sub
          (memVectorL2_openCubeSet_gluedGradientField hnu L₂ k m F omega Q)) =
      toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_gluedGradientField hnu L₁ k m F omega Q) -
        toHilbertVectorL2OfVecField
          (memVectorL2_openCubeSet_gluedGradientField hnu L₂ k m F omega Q) :=
  toHilbertVectorL2OfVecField_sub _ _

/-! ## The difference half -/

/-- **Measurability for `l.RHS.term2`, difference half**: the observable
`omega ↦ ‖∇u_n − ∇ũ_n‖_{L̲²(cu_m)}` is `P`-a.e. measurable.  By
`vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField` it is a fixed constant
times the `enorm` of the `L²(cu_m)` class of the difference field; by
`class_gluedGradientField_sub` that class is the difference of the two glued
classes, each of which is a measurable function of the sample
(`measurable_gluedGradientClass`), and `enorm` is continuous. -/
theorem term2_ob5_measurableDifference [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e : Vec d) :
    AEMeasurable (fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x)) P.toMeasure := by
  classical
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set F : Vec d := fluxSlot nu S.LPrime P S.n e
  set Q : TriadicCube d := originCube d (S.m : ℤ)
  have hA := measurable_gluedGradientClass (d := d) hnu S.LPrime S.n S.m F
  have hB := measurable_gluedGradientClass (d := d) hnu S.ell S.n S.m F
  have hpair : AEMeasurable (fun omega : ShellSeq d =>
      (toHilbertVectorL2OfVecField
          (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q),
        toHilbertVectorL2OfVecField
          (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q)))
      P.toMeasure :=
    hA.aemeasurable.prodMk hB.aemeasurable
  set C : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ ((1 : ℝ≥0∞) / 2).toReal
  have hEq : (fun omega : ShellSeq d =>
      vecCubeLpENorm Q 2
        (fun x => gluedGradientField hnu S.LPrime S.n S.m F omega x -
          gluedGradientField hnu S.ell S.n S.m F omega x)) =
      fun omega : ShellSeq d => C * ‖toHilbertVectorL2OfVecField
          (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q) -
        toHilbertVectorL2OfVecField
          (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q)‖ₑ := by
    funext omega
    have hbridge := vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField
      ((memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q).sub
        (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q))
    rw [class_gluedGradientField_sub hnu S.LPrime S.ell S.n S.m F omega Q] at hbridge
    exact hbridge
  rw [hEq]
  exact AEMeasurable.const_mul
    ((continuous_enorm.measurable.comp_aemeasurable
      (continuous_sub.measurable.comp_aemeasurable hpair))) C

/-! ## Both observables -/

/-- **Measurability for `l.RHS.term2`**: the two observables
`omega ↦ ‖∇u_n − ∇ũ_n‖_{L̲²(cu_m)}` and `omega ↦ ‖∇ũ_n − p̃‖_{L̲²(cu_m)}` are
`P`-a.e. measurable.  The first conjunct is `term2_ob5_measurableDifference`, the
second is `term2_ob5_measurableProxy` of
`GluedFieldAnnealedFiniteness`. -/
theorem term2_ob5_measurable [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (hS : ScalesOrdering S) (e : Vec d) :
    (AEMeasurable (fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.LPrime S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x)) P.toMeasure) ∧
    (AEMeasurable (fun omega : ShellSeq d =>
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x -
              annealedGluedAverage hnu P S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e))) P.toMeasure) :=
  ⟨term2_ob5_measurableDifference hnu P S e, term2_ob5_measurableProxy hnu P S hS e⟩

end

end SuperdiffusionCLT.Section3.Terms