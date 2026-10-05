/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1ConcDepthB
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC
public import SuperdiffusionCLT.Section2.Norms.NegativeNormPairing
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurability
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.DirichletResponse

/-!
# Sample-measurability of the cube mean of the response gradient

The centered gradient `∇w − (∇w)_R` of the response on a cube `R` is built from the **raw**
gradient `∇w` and the cube mean `(∇w)_R` subtracted inside the norm.  This module proves the
measurability in the sample of that cube mean.

## Main results

* `measurable_volumeAverageVec_grad_subcube`: the cube-average map
  `ω ↦ (∇w(ω))_R = ⍍_R ∇w(ω)` is measurable in the sample, on every cube
  contained in `cu_m`.  It is the vector-valued
  (all coordinates at once) form of the componentwise statement, because the centered
  carrier consumes the whole vector.
  The route is choice independence: `∇w` carries the weak-gradient class of the
  canonical response (`measurable_volumeAverageVec_matVecMul_grad_of_canonical`)
  and the cube mean of the canonical gradient is measurable because the solution
  operator is continuous and the flux class is
  (`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`).

The lemma carries the hypothesis `∀ ω, IsDirichletResponse ω L' ℓ' m p (w ω)`
of the response family and `[NeZero d]`; no other hypothesis is required, and the
canonical witness `w := dirichletResponse · L' ℓ' m p` with
`isDirichletResponse_dirichletResponse` inhabits them.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The cube mean of the response gradient is sample-measurable -/

/-- The identity matrix acts trivially on a vector. -/
private theorem matVecMul_one_vec_centered (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  have h := matVecMul_scalarMatrix (d := d) (1 : ℝ) v
  rw [scalarMatrix] at h
  simpa using h

/-- **The cube-average map `ω ↦ ⍍_R ∇w(ω)` is measurable**, on every cube
contained in `cu_m`.  Choice independence transports the cube mean of `∇w` to
the cube mean of the canonical Dirichlet response, which is measurable because
the solution operator is continuous and the flux class is measurable. -/
theorem measurable_volumeAverageVec_grad_subcube [NeZero d] {m : ℕ} {LPrime ellPrime : ℕ}
    {p : Vec d} {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    {R : TriadicCube d}
    (hsub : openCubeSet R ⊆ openCubeSet (originCube d (m : ℤ))) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad)) := by
  have hcan : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet R)
        (fun y => matVecMul ((1 : Mat d))
          ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad y))) := by
    refine measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
      (alpha := ShellSeq d) (fun omega => omega) (fun _ _ => (1 : Mat d)) ?_ ?_
      LPrime ellPrime m p hsub (measurableSet_openCubeSet R) ?_
    · intro a i j
      exact continuous_const
    · intro y i j
      exact measurable_const
    · intro x
      exact measurable_dirichletRhsField_apply LPrime ellPrime p x
  have hv1 : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet R)
        (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y))) :=
    measurable_volumeAverageVec_matVecMul_grad_of_canonical hsub
      (fun _ _ => (1 : Mat d)) hw hcan
  have hEq : (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad)) =
      fun omega : ShellSeq d => volumeAverageVec (openCubeSet R)
        (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y)) := by
    funext omega
    exact congrArg (volumeAverageVec (openCubeSet R))
      (funext fun y => (matVecMul_one_vec_centered _).symm)
  rw [hEq]
  exact hv1

/-! ## The gradient class of the response family is sample-measurable

This is the public form of the `private` lemma
`measurable_gradClass_isDirichletResponse_B` of `RHSTerm3IntegrabilityC.lean`,
because the centered carrier consumes it and a `private` lemma is not visible
outside its module. -/

/-! ## The centered square average is sample-measurable -/

/-! ## The centered carrier is sample-measurable -/

end

end SuperdiffusionCLT.Section3.Terms
