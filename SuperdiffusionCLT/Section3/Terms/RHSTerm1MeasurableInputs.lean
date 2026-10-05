/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section2.Annealed.Measurability
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOne
public import SuperdiffusionCLT.Section3.ResponseFields.RegboundsInputs

/-!
# Measurable inputs of the term-1 statement

The four measurability obligations (of the flux, of the `Ĥ̲^{-1}` norm, of the
depth moment and of the `L²` norm) concern the flux field
`fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
  (gluedGradientField hnu L k m F omega x) - qTilde`.  On each maximizer
sub-cube this field is the flux `a_L ∇u_{k,z}` of the single maximizer, and the
identity `averageFlux_setupMaximizer` (in `Section3.Setup`)
gives its cube mean explicitly:

`⨍_{z + cu_k} a_L ∇u_{k,z} = F - κ^T(z) (s_{L,*}^{-1}(z) F)`,

an expression in which no selection of a solution enters.  This file proves
that identity for the glued field and its measurability in the sample.

## Main results

* `volumeAverageVec_flux_gluedGradientField_eq`: the flux cube-mean identity for
  the glued field on every maximizer sub-cube.
* `measurable_volumeAverage_flux_gluedGradientField`: measurability of the flux
  cube mean in the sample.

## References

The paper: `e.v.ky.energy` and the surrounding definitions of the maximizers.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Entrywise measurability helpers -/

/-- One component of the matrix action on a fixed vector is measurable when the
matrix entries are. -/
private theorem measurable_matVecMul_apply_of_entries {Omega : Type*}
    [MeasurableSpace Omega] {M : Omega → Mat d}
    (hM : ∀ i j, Measurable fun omega => M omega i j) (F : Vec d) (i : Fin d) :
    Measurable fun omega => matVecMul (M omega) F i := by
  simp only [matVecMul]
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul_const (F j)

/-- One component of the matrix action on a sample-dependent vector is
measurable when the matrix entries and the vector components are. -/
private theorem measurable_matVecMulVec_apply {Omega : Type*}
    [MeasurableSpace Omega] {M : Omega → Mat d} {v : Omega → Vec d}
    (hM : ∀ i j, Measurable fun omega => M omega i j)
    (hv : ∀ j, Measurable fun omega => v omega j) (i : Fin d) :
    Measurable fun omega => matVecMul (M omega) (v omega) i := by
  simp only [matVecMul]
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j)

/-! ## The flux cube-mean identity for the glued field -/

/-- **The flux cube-mean identity for the glued field.**  On a maximizer
sub-cube `z` the glued field of `e.u.k.def` is the single maximizer gradient
`∇u_{k,z}`, so the flux identity `volumeAverageVec_cubeMaximizerFlux`
(in `RHSTerm1InputsF`) reads

`⨍_{z + cu_k} a_L ∇u_k = F - κ^T(z) (s_{L,*}^{-1}(z) F)`.

No selection of a solution enters. -/
theorem volumeAverageVec_flux_gluedGradientField_eq {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L k m : ℕ) (F : Vec d) {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) :
    volumeAverageVec (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) =
      F - matVecMul (matTranspose (kappaCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField))
        (matVecMul (sigmaStarInvCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField) F) := by
  have hG : ∀ i : Fin d,
      volumeAverage (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x) i) =
      volumeAverage (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (cubeMaximizerGradient hnu omega L F z x) i) := by
    intro i
    refine congrArg (fun t : ℝ => (MeasureTheory.volume (openCubeSet z)).toReal⁻¹ * t) ?_
    exact MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet z)
      (fun x hx => by
        rw [gluedGradientField_apply_of_mem_openCubeSet hnu L k m F omega hz hx])
  funext i
  rw [show volumeAverageVec (openCubeSet z)
      (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
        (gluedGradientField hnu L k m F omega x)) i
    = volumeAverage (openCubeSet z)
      (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
        (gluedGradientField hnu L k m F omega x) i) from rfl, hG i]
  exact congrFun (volumeAverageVec_cubeMaximizerFlux hnu omega L F z) i

/-! ## Measurability of the flux cube mean -/

/-- **The flux cube mean of the glued field is measurable.**  By the flux
cube-mean identity it is `F - κ^T(z) (s_{L,*}^{-1}(z) F)`, and the entries of
the coarse matrices `κ(z)` and `s_{L,*}^{-1}(z)` of the cutoff field are
measurable in the sample (`measurable_kappaCoarse_apply`,
`measurable_sigmaStarInvCoarse_apply`).  No selection of a solution enters. -/
theorem measurable_volumeAverage_flux_gluedGradientField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L k m : ℕ) (F : Vec d) {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) (i : Fin d) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) i) := by
  have hkappa : ∀ p q : Fin d, Measurable (fun omega : ShellSeq d =>
      kappaCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField p q) := by
    intro p q
    exact @measurable_kappaCoarse_apply d _ (ShellSeq d) _
      (fun omega : ShellSeq d => coefficientCutoff nu omega L)
      (measurable_coefficientCutoff nu L)
      (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z p q
  have hstar : ∀ p q : Fin d, Measurable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField p q) := by
    intro p q
    exact @measurable_sigmaStarInvCoarse_apply d _ (ShellSeq d) _
      (fun omega : ShellSeq d => coefficientCutoff nu omega L)
      (measurable_coefficientCutoff nu L)
      (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z p q
  have hEq : (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x)) i) =
    fun omega : ShellSeq d =>
      (F - matVecMul (matTranspose (kappaCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField))
        (matVecMul (sigmaStarInvCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField) F)) i := by
    funext omega
    exact congrArg (fun v : Vec d => v i)
      (volumeAverageVec_flux_gluedGradientField_eq hnu omega L k m F hz)
  rw [hEq]
  show Measurable (fun omega : ShellSeq d =>
    F i - matVecMul (matTranspose (kappaCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField))
      (matVecMul (sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField) F) i)
  exact (measurable_const : Measurable (fun _ : ShellSeq d => F i)).sub
    (measurable_matVecMulVec_apply
      (fun p q => measurable_matTranspose_apply hkappa p q)
      (fun j => measurable_matVecMul_apply_of_entries hstar F j) i)

/-! ## Measurability of the squared cube mean of the centred flux field -/

end

end SuperdiffusionCLT.Section3.Terms