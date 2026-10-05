/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs
public import Homogenization.Sobolev.PotentialSolenoidalL2
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-!
# The `L²` membership of the maximizer gradient and its pairing integrability

The final assembly of Section 3 (`Section3/Setup/MasterIdentityAssembly.lean`)
carries three cube-side integrability binders whose only missing ingredient is
the `L²` membership of the maximizer gradient `∇u_m = ∇u_{m,0}` on the open
cube `cu_m`:

* the flux pairing `∇w · (a_ℓ ∇u_m)` (`hIntFlux`),
* the stream pairing `∇w · ((k_{L'} − k_ℓ)(∇u_m − p))` (`hIntK`),
* the coordinate pairing `(k_{L'} − k_ℓ)∇w` read coordinatewise (`hIntCoord`).

This module supplies the datum `MemVectorL2 (openCubeSet z) (∇u_{k,z})` and the
three corollaries, at the carrier `cubeMaximizerGradient` of
`GluedField.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The `L²` membership of the maximizer gradient -/

/-- `MemVectorL2` is by definition `MemLp f 2 (volumeMeasureOn U)`, and
`volumeMeasureOn` is by definition the restricted volume, so the datum is
exactly `memLp_two_cubeMaximizerGradient`. -/
theorem memVectorL2_cubeMaximizerGradient {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) :
    MemVectorL2 (openCubeSet z) (cubeMaximizerGradient hnu omega L F z) :=
  memLp_two_cubeMaximizerGradient hnu omega L F z

/-! ## `L²` transport across a continuous matrix field -/

/-- On an open triadic cube, `L²` membership is stable under pairing with a
continuous matrix field: the entries of the matrix are bounded on the closed
ball containing the cube, so each coordinate of the product is controlled
pointwise by the corresponding coordinate of the field. -/
theorem memVectorL2_matVecMul_of_continuous (Q : TriadicCube d)
    {A : Vec d → Mat d} (hA : ∀ i j : Fin d, Continuous (fun x : Vec d => A x i j))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    MemVectorL2 (openCubeSet Q) (fun x : Vec d => matVecMul (A x) (g x)) := by
  rw [MemVectorL2] at hg ⊢
  refine (MeasureTheory.memLp_pi_iff).2 ?_
  intro i
  have hrw : (fun x : Vec d => matVecMul (A x) (g x) i)
      = fun x : Vec d => ∑ j : Fin d, A x i j * g x j := rfl
  rw [hrw]
  refine MeasureTheory.memLp_finsetSum (s := Finset.univ)
    (f := fun j : Fin d => fun x : Vec d => A x i j * g x j) ?_
  intro j hj
  have hgj : MeasureTheory.MemLp (fun x : Vec d => g x j) 2 (volumeMeasureOn (openCubeSet Q)) :=
    (MeasureTheory.memLp_pi_iff.mp hg) j
  have hsub : openCubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    ProperSpace.isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn hK ((hA i j).continuousOn)
  have hbound : ∀ᵐ x ∂ volumeMeasureOn (openCubeSet Q),
      ‖A x i j * g x j‖ ≤ C * ‖g x j‖ := by
    filter_upwards
      [MeasureTheory.ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
    calc ‖A x i j * g x j‖ = ‖A x i j‖ * ‖g x j‖ := norm_mul _ _
      _ ≤ C * ‖g x j‖ :=
        mul_le_mul_of_nonneg_right (hC x (hsub hx)) (norm_nonneg (g x j))
  exact MeasureTheory.MemLp.of_le_mul hgj
    (((hA i j).aestronglyMeasurable).mul hgj.aestronglyMeasurable) hbound

/-- The stream increment `k_b − k_a` is a continuous matrix field. -/
theorem continuous_streamCutoff_sub_entries (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b) :
    ∀ i j : Fin d, Continuous (fun x : Vec d =>
      (streamCutoff omega b x - streamCutoff omega a x) i j) :=
  fun i j => (continuous_apply j).comp ((continuous_apply i).comp
    (SuperdiffusionCLT.Section3.ResponseFields.continuous_streamCutoff_sub
      omega hab))

/-! ## The three pairing integrability corollaries at the maximizer carrier -/

/-- The flux pairing of the master identity's `hIntFlux` slot,
`∇w · (a_ell ∇u_{k,z})`, is integrable on the open cube `z`.  At the assembly
carrier the cube is `originCube d (S.m : ℤ)`, `L` is the maximizer level and
`ell` the cutoff level of the flux field. -/
theorem integrableOn_vecDot_coefficientCutoff_cubeMaximizerGradient {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) (L ell : ℕ) (F : Vec d) (z : TriadicCube d)
    (w : H10Function (openCubeSet z)) :
    MeasureTheory.IntegrableOn
      (fun x : Vec d => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
          (cubeMaximizerGradient hnu omega L F z x)))
      (openCubeSet z) volume :=
  integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2
    (memVectorL2_matVecMul_coefficientCutoff hnu omega ell z
      (memVectorL2_cubeMaximizerGradient hnu omega L F z))

/-- The stream pairing of the master identity's `hIntK` slot,
`∇w · ((k_b − k_a)(∇u_{k,z} − p))`, is integrable on the open cube `z`. -/
theorem integrableOn_vecDot_streamCutoff_cubeMaximizerGradient {nu : ℝ}
    (hnu : 0 < nu) (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (L : ℕ) (F : Vec d) (p : Vec d) (z : TriadicCube d)
    (w : H10Function (openCubeSet z)) :
    MeasureTheory.IntegrableOn
      (fun x : Vec d => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega b x - streamCutoff omega a x)
          (cubeMaximizerGradient hnu omega L F z x - p)))
      (openCubeSet z) volume := by
  refine integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2 ?_
  refine memVectorL2_matVecMul_of_continuous z
    (continuous_streamCutoff_sub_entries omega hab) ?_
  exact (memVectorL2_cubeMaximizerGradient hnu omega L F z).sub
    (memVectorL2_const p)

/-- The coordinate pairing of the master identity's `hIntCoord` slot,
`(k_b − k_a)∇w` read coordinatewise, is integrable on the open cube `z`. -/
theorem integrableOn_coord_streamCutoff_grad (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) (z : TriadicCube d) (w : H10Function (openCubeSet z))
    (i : Fin d) :
    MeasureTheory.IntegrableOn
      (fun y : Vec d => matVecMul (streamCutoff omega b y - streamCutoff omega a y)
        (w.toH1Function.grad y) i)
      (openCubeSet z) volume :=
  CorrectionFieldData.integrableOn_coord_of_memVectorL2
    (memVectorL2_matVecMul_of_continuous z
      (continuous_streamCutoff_sub_entries omega hab)
      w.toH1Function.grad_memVectorL2) i

end

end SuperdiffusionCLT.Section3.Terms