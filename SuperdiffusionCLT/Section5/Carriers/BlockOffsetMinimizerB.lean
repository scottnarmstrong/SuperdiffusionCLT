/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.BlockOffsetMinimizer
public import Homogenization.CoarseGraining.OriginCubeEllipticRecovery

/-!
# Offset block minimizers on a triadic cube

For an elliptic coefficient on a triadic cube `Q` (the subcubes `z + cu_n` of `lem.localization`
are `⟨n, k⟩`) and an offset `F` with `L²` components there is a minimizer of the block energy over
`IsBlockOffsetAdmissible (cubeSet Q) F`, unique almost everywhere
(`exists_isBlockOffsetMinimizer_cubeSet`).

For a constant offset `P` the minimal energy is `½ P · A(Q) P` with `A(Q)` the coarse block matrix
(`volumeAverage_blockEnergyDensity_eq_half_coarseBlockMatrix`), the identity behind
`P_z · bfA_m(z + cu_n) P_z = ‖bfA_m^{1/2} S_z‖²`. For a non-constant offset no such closed form
exists in terms of `A(Q)`: the minimal energy is the energy of the projection of the offset.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization

variable {d : ℕ} {a : CoeffField d}

/-- Ellipticity of a translated coefficient field on the translated set. -/
theorem isEllipticFieldOn_translateCoeffField_of_translateSet' {lam Lam : ℝ} {U : Set (Vec d)}
    (z : Vec d) (hEll : IsEllipticFieldOn lam Lam (translateSet z U) a) :
    IsEllipticFieldOn lam Lam U (translateCoeffField z a) := by
  classical
  have hadd_sub : ∀ x : Vec d, x + z - z = x := fun x => by
    ext k
    simp [sub_eq_add_neg, add_assoc]
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x + z) :=
      (continuous_id.add continuous_const).measurable
    have hcomp :
        Measurable (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) :=
      hEll.1.comp hshift
    have hEq :
        (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) =
          (fun x i j => if x ∈ U then translateCoeffField z a x i j else 0) := by
      funext x i j
      by_cases hx : x ∈ U
      · have hxt : x + z ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem, hadd_sub]
          exact hx
        simp [hx, hxt]
        rfl
      · have hxt : x + z ∉ translateSet z U := by
          intro hmem
          rw [mem_translateSet_iff_sub_mem, hadd_sub] at hmem
          exact hx hmem
        simp [hx, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hxt : x + z ∈ translateSet z U := by
      rw [mem_translateSet_iff_sub_mem, hadd_sub]
      exact hx
    exact hEll.2 (x + z) hxt

/-- `Mu` is quadratic on a triadic half-open cube carrying an elliptic coefficient. -/
theorem hasQuadraticMu_cubeSet_of_isEllipticFieldOn [NeZero d] {lam Lam : ℝ} (Q : TriadicCube d)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    HasQuadraticMu (cubeSet Q) a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hEllO : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hEllT : IsEllipticFieldOn lam Lam (openCubeSet (originCube d Q.scale))
      (translateCoeffField z a) := by
    refine isEllipticFieldOn_translateCoeffField_of_translateSet' z ?_
    simpa [z, openCubeSet_eq_translateSet_originCube_of_triadicCube Q] using! hEllO
  obtain ⟨R, hData⟩ := openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
    Q.scale (translateCoeffField z a) hEllT
  exact hasQuadraticMu_cubeSet_of_triadicCube_of_hasOpenCubeEllipticRecoveryData Q R hData

/-- **Existence and almost-everywhere uniqueness of the offset minimizer on a triadic cube.** -/
theorem exists_isBlockOffsetMinimizer_cubeSet [NeZero d] {lam Lam : ℝ} (Q : TriadicCube d)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) {F : BlockState d}
    (hFp : MemVectorL2 (cubeSet Q) F.potential) (hFf : MemVectorL2 (cubeSet Q) F.flux) :
    ∃ X : BlockState d, IsBlockOffsetMinimizer a (cubeSet Q) F X ∧
      ∀ W : BlockState d, IsBlockOffsetMinimizer a (cubeSet Q) F W →
        W.potential =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] X.potential ∧
          W.flux =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] X.flux := by
  have hEllO : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hRealize := PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
  have hvol : 0 < (MeasureTheory.volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let Rd := potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
    hRealize
  let Op := (Rd.toMuOperatorSystemDataOfIsEllipticFieldOn hEllO hvol).toMuOperatorRealization
  obtain ⟨X, hX, huniq⟩ := exists_isBlockOffsetMinimizer_of_recovery
    Rd.toMuCorrectionSpaceRecoveryData Op
    ((memVectorL2_cubeSet_iff_openCubeSet Q _).1 hFp) ((memVectorL2_cubeSet_iff_openCubeSet Q _).1 hFf)
  refine ⟨X, (isBlockOffsetMinimizer_cubeSet_iff_openCubeSet Q a F X).2 hX, fun W hW => ?_⟩
  have := huniq W ((isBlockOffsetMinimizer_cubeSet_iff_openCubeSet Q a F W).1 hW)
  simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using this

/-- **The minimal energy for a constant offset is the coarse block quadratic form.** -/
theorem volumeAverage_blockEnergyDensity_eq_half_coarseBlockMatrix [NeZero d] {lam Lam : ℝ}
    (Q : TriadicCube d) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (P : BlockVec d)
    {X : BlockState d} (hX : IsBlockOffsetMinimizer a (cubeSet Q) (constBlockState P) X) :
    volumeAverage (cubeSet Q) (blockEnergyDensity a X) =
      (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  rw [← Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu
    (hasQuadraticMu_cubeSet_of_isEllipticFieldOn Q hEll) P]
  symm
  refine IsLeast.csInf_eq ⟨muValueSet_mem hX.1, ?_⟩
  rintro _ ⟨Y, hY, rfl⟩
  exact hX.2 Y hY

/-! ## Witnesses -/

/-- The identity coefficient is elliptic with constants `1, 1`. -/
theorem isEllipticFieldOn_one {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn 1 1 U (fun _ => (1 : Mat d)) := by
  classical
  have hmv : ∀ ξ : Vec d, matVecMul (1 : Mat d) ξ = ξ := by
    intro ξ; funext i
    simp only [matVecMul, Matrix.one_apply]
    simp
  refine ⟨?_, fun x _ => ⟨one_pos, le_rfl, fun ξ => ?_, fun ξ => ?_⟩⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact Measurable.ite hU measurable_const measurable_const
  · rw [hmv]; simp [vecNormSq, vecDot]
  ·     simp only [inv_one, hmv]; simp [vecNormSq, vecDot]

/-- Satisfiability: identity coefficient on the unit cube, offset `0`. The minimizer exists, and its
energy is the coarse quadratic form `½ 0 · A 0 = 0`. -/
example [NeZero d] :
    ∃ X : BlockState d,
      IsBlockOffsetMinimizer (fun _ => (1 : Mat d)) (cubeSet (originCube d 0))
        (constBlockState 0) X ∧
      volumeAverage (cubeSet (originCube d 0)) (blockEnergyDensity (fun _ => (1 : Mat d)) X) = 0 := by
  obtain ⟨X, hX, -⟩ := exists_isBlockOffsetMinimizer_cubeSet (a := fun _ => (1 : Mat d))
    (lam := 1) (Lam := 1) (originCube d 0)
    (isEllipticFieldOn_one (measurableSet_cubeSet _)) (F := constBlockState 0)
    (memVectorL2_const _) (memVectorL2_const _)
  refine ⟨X, hX, ?_⟩
  rw [volumeAverage_blockEnergyDensity_eq_half_coarseBlockMatrix (originCube d 0)
    (isEllipticFieldOn_one (measurableSet_cubeSet _)) 0 hX]
  simp [blockVecDot, vecDot]

end SuperdiffusionCLT.Section5
