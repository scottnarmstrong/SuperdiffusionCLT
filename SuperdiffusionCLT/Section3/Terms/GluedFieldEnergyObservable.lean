/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsG
public import SuperdiffusionCLT.Section2.Annealed.Measurability

/-!
# The cube-energy observable of the glued field

The cube energy of the glued field of `e.u.k.def` is not an opaque observable
of a chosen solution: it **equals** an explicit annealed quantity.  The
identity `responseJ_cubeMaximizer_eq_mul_volumeAverage_vecNormSq`
(from the module `RHSTerm1InputsG`) composed with `responseJ_setupMaximizer`
(`Section3/Setup/Scales.lean`) gives, for every scale-`k` cube `z`,

`⨍_{z + cu_k} |∇u_{k,z}|² = (1/nu) · F · s_{L,*}^{-1}(z + cu_k) F`,

and the starred inverse on the right is measurable in the sample
(`measurable_sigmaStarInvCoarse_apply`).  So the cube-energy observable is
measurable because it equals a measurable function, with no selection of a
response needed.

## Main results

* `volumeAverage_vecNormSq_cubeMaximizerGradient_eq`: the cube-energy identity
  for the single maximizer `∇u_{k,z}` on the cube `z + cu_k`.
* `measurable_volumeAverage_vecNormSq_cubeMaximizerGradient`: the
  measurability of `omega ↦ ⨍_{z + cu_k} |∇u_{k,z}|²` on the shell-sequence
  carrier, from the measurability of the starred inverse.
* `measurable_volumeAverage_vecNormSq_gluedGradientField`: the same for the
  glued field `∇u_k` on the centred cube `cu_r`, `k ≤ r ≤ m`, by the lattice
  partition `volumeAverage_avsum_openCubeSet` of `cu_r` into its scale-`k`
  sub-cubes.

## References

* The paper: `e.u.k.y.def`, `e.u.k.def` and `e.v.ky.energy`.
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

/-! ## The cube-energy identity -/

/-- **The cube-energy identity for the single maximizer.**  The two
equalities of `e.v.ky.energy` compose to the exact identity

`⨍_{z + cu_k} |∇u_{k,z}|² = (1/nu) · F · s_{L,*}^{-1}(z + cu_k) F`,

the response value of the pure-flux problem being `(nu/2)` times the cube mean
(`responseJ_cubeMaximizer_eq_mul_volumeAverage_vecNormSq`) and `(1/2)` times
the starred-inverse pairing (`responseJ_setupMaximizer`).  The starred inverse
is written in the raw `Homogenization` spelling, the one the measurability
engine below consumes. -/
theorem volumeAverage_vecNormSq_cubeMaximizerGradient_eq {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d) :
    volumeAverage (openCubeSet z)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x)) =
      (nu : ℝ)⁻¹ * vecDot F
        (matVecMul (sigmaStarInvCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField) F) := by
  have hconv : Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain z)
      (cubeCutoffCoeffOn hnu omega L z) =
      sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField := by
    rw [← sigmaStarInvCoarse_toCoeffField, ← cubeCutoffCoeffOn_toCoeffField]
    rfl
  have h := responseJ_cubeMaximizer_eq_mul_volumeAverage_vecNormSq hnu omega L F z
  rw [responseJ_setupMaximizer (Book.Ch02.cubeDomain z)
    (cubeCutoffCoeffOn hnu omega L z) F, hconv] at h
  set A : ℝ := volumeAverage (openCubeSet z)
    (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x)) with hAeq
  set V : ℝ := vecDot F (matVecMul (sigmaStarInvCoarse (openCubeSet z)
    (coefficientCutoff nu omega L).toCoeffField) F) with hVeq
  have h2 : V = nu * A := by
    have h' : (2 : ℝ) * ((1 : ℝ) / 2 * V) = (2 : ℝ) * (nu / 2 * A) := by rw [h]
    rw [show V = (2 : ℝ) * ((1 : ℝ) / 2 * V) from by ring, h',
      show (2 : ℝ) * (nu / 2 * A) = nu * A from by ring]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hnu.ne', one_mul]

/-! ## Measurability of the cube-energy observable -/

/-- One component of the matrix action on a fixed vector is measurable when the
matrix entries are. -/
private theorem measurable_matVecMul_apply_of_entries {Omega : Type*}
    [MeasurableSpace Omega] {M : Omega → Mat d}
    (hM : ∀ i j, Measurable fun omega => M omega i j) (F : Vec d) (i : Fin d) :
    Measurable fun omega => matVecMul (M omega) F i := by
  simp only [matVecMul]
  exact Finset.measurable_sum _ fun j _ => (hM i j).mul_const (F j)

/-- Pairing a fixed vector with a vector-valued map with measurable components
is measurable. -/
private theorem measurable_vecDot_const_left {Omega : Type*} [MeasurableSpace Omega]
    (F : Vec d) {v : Omega → Vec d} (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot F (v omega) := by
  simp only [vecDot]
  exact Finset.measurable_sum _ fun i _ => (hv i).const_mul (F i)

/-- **The cube-energy observable of the glued field is measurable.**  For every
scale-`k` cube `z` the function `omega ↦ ⨍_{z + cu_k} |∇u_{k,z}|²` is
measurable on the shell-sequence carrier: by the cube-energy identity it is
`(1/nu) · F · s_{L,*}^{-1}(z + cu_k) F`, and the entries of the starred inverse
of the cutoff field are measurable in the sample.  No selection of a
solution enters. -/
theorem measurable_volumeAverage_vecNormSq_cubeMaximizerGradient [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L : ℕ) (F : Vec d) (z : TriadicCube d) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet z)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x))) := by
  have hEq : (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet z)
        (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F z x))) =
      fun omega : ShellSeq d => (nu : ℝ)⁻¹ * vecDot F
        (matVecMul (sigmaStarInvCoarse (openCubeSet z)
          (coefficientCutoff nu omega L).toCoeffField) F) := by
    funext omega
    exact volumeAverage_vecNormSq_cubeMaximizerGradient_eq hnu omega L F z
  rw [hEq]
  have hM : ∀ i j : Fin d, Measurable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField i j) := by
    intro i j
    exact @measurable_sigmaStarInvCoarse_apply d _ (ShellSeq d) _
      (fun omega : ShellSeq d => coefficientCutoff nu omega L)
      (measurable_coefficientCutoff nu L)
      (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) z i j
  refine (measurable_vecDot_const_left F
    (fun i => measurable_matVecMul_apply_of_entries hM F i)).const_mul _

/-! ## The glued field on an intermediate cube -/

/-- **The cube-energy observable of the glued field is measurable.**  For every
intermediate scale `k ≤ r ≤ m` the function `omega ↦ ⨍_{cu_r} |∇u_k|²` is
measurable on the shell-sequence carrier: the centred cube `cu_r` is the
disjoint union of its scale-`k` sub-cubes
(`volumeAverage_avsum_openCubeSet`), on each of which the glued field is the
single maximizer `∇u_{k,z}` (`gluedGradientField_apply_of_mem_openCubeSet`), so
the observable is a finite sum of the measurable cube-energy observables above.
No selection of a solution enters. -/
theorem measurable_volumeAverage_vecNormSq_gluedGradientField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {k r m : ℕ} (hkr : k ≤ r) (hrm : r ≤ m) (L : ℕ) (F : Vec d) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (r : ℤ)))
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))) := by
  classical
  have hint : ∀ omega : ShellSeq d, ∀ R ∈ largeCubeSubcubes d k r,
      IntegrableOn (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))
        (openCubeSet R) volume :=
    fun omega R _ => integrableOn_vecNormSq_gluedGradientField hnu L k m F omega R
  have hEq : (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (r : ℤ)))
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))) =
      fun omega : ShellSeq d => ((largeCubeSubcubes d k r).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d k r, volumeAverage (openCubeSet R)
          (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) := by
    funext omega
    exact volumeAverage_avsum_openCubeSet (hint omega)
  rw [hEq]
  have hterm : ∀ R ∈ largeCubeSubcubes d k r, Measurable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet R)
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))) := by
    intro R hR
    have hRm : R ∈ largeCubeSubcubes d k m :=
      mem_largeCubeSubcubes_of_mem_largeCubeSubcubes_le hkr hrm hR
    have hRq : (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))) =
        fun omega : ShellSeq d =>
          volumeAverage (openCubeSet R)
            (fun x => vecNormSq (cubeMaximizerGradient hnu omega L F R x)) := by
      funext omega
      refine congrArg (fun t : ℝ => (volume (openCubeSet R)).toReal⁻¹ * t) ?_
      refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet R) ?_
      intro x hx
      show vecNormSq (gluedGradientField hnu L k m F omega x) =
        vecNormSq (cubeMaximizerGradient hnu omega L F R x)
      rw [gluedGradientField_apply_of_mem_openCubeSet hnu L k m F omega hRm hx]
    rw [hRq]
    exact measurable_volumeAverage_vecNormSq_cubeMaximizerGradient hnu L F R
  exact (Finset.measurable_sum _ hterm).const_mul _

/-! ## Finiteness of the annealed squared cube norm -/

/-- **The annealed squared cube norm of the glued field is measurable.**  The
squared `L̲²(cu_r)` norm of `∇u_k` is the `ENNReal.ofReal` of the cube energy
(`vecCubeLpENorm_two_sq_eq_ofReal` with the normalized cube integral read as
the cube average), so it is measurable in the sample by the identity above;
no selection of a solution enters. -/
theorem measurable_vecCubeLpENorm_two_sq_gluedGradientField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {k r m : ℕ} (hkr : k ≤ r) (hrm : r ≤ m) (L : ℕ) (F : Vec d) :
    Measurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (r : ℤ)) 2
        (gluedGradientField hnu L k m F omega) ^ (2 : ℕ)) := by
  classical
  have hav : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (r : ℤ)))
        (fun x => vecNormSq (gluedGradientField hnu L k m F omega x)) =
      (cubeVolume (originCube d (r : ℤ)))⁻¹ *
        ∫ x in openCubeSet (originCube d (r : ℤ)),
          vecNormSq (gluedGradientField hnu L k m F omega x) := by
    intro omega
    show (volume (openCubeSet (originCube d (r : ℤ)))).toReal⁻¹ *
      ∫ x in openCubeSet (originCube d (r : ℤ)),
        vecNormSq (gluedGradientField hnu L k m F omega x) = _
    rw [volume_openCubeSet_toReal]
  have hEq : (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (r : ℤ)) 2
        (gluedGradientField hnu L k m F omega) ^ (2 : ℕ)) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal (volumeAverage (openCubeSet (originCube d (r : ℤ)))
          (fun x => vecNormSq (gluedGradientField hnu L k m F omega x))) := by
    funext omega
    rw [vecCubeLpENorm_two_sq_eq_ofReal
      (memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega
        (originCube d (r : ℤ))), integral_normalizedCubeMeasure_eq, ← hav omega]
  rw [hEq]
  exact (ENNReal.measurable_ofReal).comp
    (measurable_volumeAverage_vecNormSq_gluedGradientField hnu hkr hrm L F)

end

end SuperdiffusionCLT.Section3.Terms