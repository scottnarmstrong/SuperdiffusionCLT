/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideFinal
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3IntegrabilityC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3QuadZc
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SideConditionsB

/-!
# Term 3: the two `P`-integrability leaves of the final assembly, both discharged

The final assembly of `e.RHS.term3` carries seven obligation
binders; two of them are pure `P`-integrability and are removed here:

* `_hPair`, the `P`-integrability of the conclusion's own left-hand side;
* `_hbHalfInt`, the half-weight carrier on the range of `e.bL.to.bhomell`:
  `z'` a triadic sub-cube of `cu_m` and `z` a sub-cube of `z'`.

## `_hPair`

Already discharged by `hPair_discharged_B`
(`Section3/Terms/RHSTerm3IntegrabilityC.lean`) from the binders of the final assembly
alone, with no hypothesis left.  Its engine is `integrable_volumeAverage_pairing_final`
(`Section3/Terms/RHSTerm3Integrability.lean`): measurability of the response
gradient class is *not* blocked by the `Classical.choose` in
`dirichletResponse`, because `IsDirichletResponse` pins the weak-gradient class
(`gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse`), so
the class of any selection is the class of the canonical response, which is
measurable (`measurable_gradToHilbertVectorL2_dirichletResponse`).  This module
therefore *cites* that discharge rather than repeating it.

## `_hbHalfInt`

`sideCondition_hbHalfInt_final` (`Section3/Terms/RHSTerm3SideFinal.lean`)
discharges the carrier with every hypothesis on the *membership* range
`z' ∈ largeCubeSubcubes d k S.m`.  The binder of the final assembly, however, is stated on the
*containment* range `openCubeSet z' ⊆ openCubeSet cu_m`, which is strictly
larger: the scale-`(-1)` cube at the origin is contained in `cu_m` but is a
descendant of it at no depth.  Earlier reductions therefore left a residual for the
cubes off the descendant lattice.  That residual is unnecessary: containment
in `cu_m` is exactly the hypothesis the two carriers need.

* Measurability.  `measurable_volumeAverageVec_matVecMul_grad_of_canonical`
  (`Section3/Setup/ResponseMeasurability.lean`) reads the cube mean of `∇w`
  over *any* `V ⊆ openCubeSet cu_m` off the canonical response, whose cube mean
  is measurable (`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`).
* The annealed square moment.  `ofReal_vecNormSq_volumeAverageVec_sq_le`
  (`Section3/Terms/RHSTerm3SourceGaps.lean`) bounds the squared cube mean on
  `z'` by `‖∇w‖^4_{L̲^4(z')}`, and the comparison
  `cubeLpENorm_four_pow_le_of_openCubeSet_subset` below bounds that by
  `|cu_m| / |z'|` times `‖∇w‖^4_{L̲^4(cu_m)}`, whose `P`-integral is finite by
  `gradFour_finite_of_regbounds`.  No descendant lattice is involved.

The second half is `hbHalfInt_discharged`, which removes the binder
with no hypothesis at all.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Elementary carriers -/

/-- The identity matrix acts trivially on a vector. -/
private theorem matVecMul_one_vec_leaves (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- `vecNormSq` is measurable as soon as the coordinates are. -/
private theorem measurable_vecNormSq_of_components_leaves {Omega : Type*} [MeasurableSpace Omega]
    {v : Omega → Vec d} (hv : ∀ i : Fin d, Measurable fun omega => v omega i) :
    Measurable fun omega => vecNormSq (v omega) := by
  show Measurable fun omega => vecDot (v omega) (v omega)
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hv i)

/-- The quadratic form of a measurable vector through a measurable matrix is
measurable. -/
private theorem measurable_vecDot_matVecMul_self_leaves {Omega : Type*}
    [MeasurableSpace Omega] {M : Omega → Mat d} {v : Omega → Vec d}
    (hM : ∀ i j, Measurable fun omega => M omega i j)
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecDot (v omega) (matVecMul (M omega) (v omega)) := by
  simp only [vecDot, matVecMul]
  exact Finset.measurable_sum _ fun i _ =>
    (hv i).mul (Finset.measurable_sum _ fun j _ => (hM i j).mul (hv j))

/-! ## The cube mean of `∇w` on a sub-cube of `cu_m`: measurability -/

/-- **The coordinates of the cube mean of `∇w` are measurable in the sample on
any subset of `cu_m`.**  The response condition pins the weak-gradient class to
that of the canonical response
(`measurable_volumeAverageVec_matVecMul_grad_of_canonical`), so the cube mean is
the cube mean of the canonical response, which is measurable by
`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp` with the
constant coefficient field `1`. -/
private theorem measurable_volumeAverageVec_grad_component_leaves [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (i : Fin d) :
    Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad) i) := by
  have hcan : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d))
          ((dirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e)).toH1Function.grad y))) := by
    refine measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
      (alpha := ShellSeq d) (fun omega => omega) (fun _ _ => (1 : Mat d)) ?_ ?_
      S.LPrime S.ellPrime S.m (testVector nu S.LPrime P S.n e) hsub
      (measurableSet_openCubeSet z') ?_
    · intro a i j
      exact continuous_const
    · intro y i j
      exact measurable_const
    · intro x
      exact measurable_dirichletRhsField_apply S.LPrime S.ellPrime
        (testVector nu S.LPrime P S.n e) x
  have hv1 : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y))) :=
    measurable_volumeAverageVec_matVecMul_grad_of_canonical hsub
      (fun _ _ => (1 : Mat d)) hw hcan
  have hEq : (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad) i) =
      fun omega : ShellSeq d => volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y)) i := by
    funext omega
    exact congrArg (fun v : Vec d => v i)
      (congrArg (volumeAverageVec (openCubeSet z'))
        (funext fun y => (matVecMul_one_vec_leaves _).symm))
  rw [hEq]
  exact (measurable_pi_apply i).comp hv1

/-- **The squared cube mean of `∇w` is measurable in the sample on any sub-cube
of `cu_m`.** -/
private theorem measurable_vecNormSq_volumeAverageVec_grad_leaves [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad))) :=
  measurable_vecNormSq_of_components_leaves fun i =>
    measurable_volumeAverageVec_grad_component_leaves P S w hw hsub i

/-- **The half-weight carrier is measurable in the sample on any sub-cube of
`cu_m`.**  It is the quadratic form `v · (b v)` of the translated coarse block
at the cube mean `v` of `∇w`. -/
private theorem measurable_translatedBlockHalfWeight_leaves [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)))
    (z : TriadicCube d) :
    Measurable (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z) := by
  have hv : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad) i) :=
    fun i => measurable_volumeAverageVec_grad_component_leaves P S w hw hsub i
  have hEq : (fun omega : ShellSeq d =>
      translatedBlockHalfWeight nu S.LPrime w omega z' z) =
      fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))
          (matVecMul (translatedCoarseBlock nu S.LPrime omega z)
            (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) := by
    funext omega
    exact SuperdiffusionCLT.Section2.Localization.vecNormSq_sqrt_matVecMul_eq_vecDot_matVecMul
      (posSemidef_translatedCoarseBlock hnu S.LPrime omega z) _
  rw [hEq]
  exact measurable_vecDot_matVecMul_self_leaves
    (fun i j => measurable_translatedCoarseBlock_apply hnu S.LPrime z i j) hv

/-! ## The fourth-power comparison of the cube norms of nested cubes -/

/-- **The fourth power of the normalized `L̲^4` norm on a sub-cube is bounded by
the volume ratio times the fourth power on the containing cube.**  The
normalized cube measure of a cube is its volume-normalized Lebesgue measure of
the open cube (`normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet`), so
containment of the open cubes makes the restricted measures comparable. -/
theorem cubeLpENorm_four_pow_le_of_openCubeSet_subset {E : Type*} [NormedAddCommGroup E]
    {Q z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet Q) (f : Vec d → E) :
    (SuperdiffusionCLT.Section2.Norms.cubeLpENorm z' 4 f) ^ (4 : ℕ) ≤
      ENNReal.ofReal (cubeVolume Q / cubeVolume z') *
        (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 f) ^ (4 : ℕ) := by
  have hz'pos : 0 < cubeVolume z' := cubeVolume_pos z'
  have hQpos : 0 < cubeVolume Q := cubeVolume_pos Q
  by_cases hfQ : AEStronglyMeasurable f (normalizedCubeMeasure Q)
  swap
  · have htop : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 f = ⊤ := by
      rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm]
      exact eLpNorm_of_not_aestronglyMeasurable hfQ
    rw [htop, ENNReal.top_pow (by norm_num), ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.2 (div_pos hQpos hz'pos)).ne'
  have hfz : AEStronglyMeasurable f (normalizedCubeMeasure z') := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet] at hfQ ⊢
    have hc0 : ∀ R : TriadicCube d, ENNReal.ofReal ((cubeVolume R)⁻¹) ≠ 0 := fun R =>
      (ENNReal.ofReal_pos.2 (inv_pos.2 (cubeVolume_pos R))).ne'
    have h1 : AEStronglyMeasurable f (volume.restrict (openCubeSet Q)) := by
      have h' := hfQ.smul_measure (ENNReal.ofReal ((cubeVolume Q)⁻¹))⁻¹
      rwa [smul_smul, ENNReal.inv_mul_cancel (hc0 Q) ENNReal.ofReal_ne_top, one_smul] at h'
    exact h1.mono_measure (Measure.restrict_mono hsub le_rfl) |>.smul_measure _
  have hper : ∀ R : TriadicCube d, AEStronglyMeasurable f (normalizedCubeMeasure R) →
      (SuperdiffusionCLT.Section2.Norms.cubeLpENorm R 4 f) ^ (4 : ℕ) =
        ENNReal.ofReal ((cubeVolume R)⁻¹) *
          ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (openCubeSet R)) := by
    intro R hR
    rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm, eLpNorm_four_pow _ f hR,
      normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet, lintegral_smul_measure,
      smul_eq_mul]
  have hQne : cubeVolume Q ≠ 0 := ne_of_gt hQpos
  have hreal : cubeVolume Q / cubeVolume z' * (cubeVolume Q)⁻¹ = (cubeVolume z')⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc, mul_comm (cubeVolume z')⁻¹ (cubeVolume Q)⁻¹,
      ← mul_assoc, mul_inv_cancel₀ hQne, one_mul]
  have hid : ENNReal.ofReal (cubeVolume Q / cubeVolume z') *
      ENNReal.ofReal ((cubeVolume Q)⁻¹) = ENNReal.ofReal ((cubeVolume z')⁻¹) := by
    rw [← ENNReal.ofReal_mul (div_nonneg hQpos.le hz'pos.le), hreal]
  have hmono : ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (openCubeSet z')) ≤
      ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (openCubeSet Q)) :=
    lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
  rw [hper z' hfz, hper Q hfQ]
  calc ENNReal.ofReal ((cubeVolume z')⁻¹) *
        ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (openCubeSet z'))
      ≤ ENNReal.ofReal ((cubeVolume z')⁻¹) *
        ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (openCubeSet Q)) :=
        mul_le_mul' le_rfl hmono
    _ = ENNReal.ofReal (cubeVolume Q / cubeVolume z') *
        (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂(volume.restrict (openCubeSet Q))) := by
        rw [← mul_assoc, hid]

/-! ## The annealed square moment of the cube mean on a sub-cube of `cu_m` -/

/-- **`E[|⍍_{z'} ∇w|⁴] < ∞` on every sub-cube `z'` of `cu_m`.**  Jensen on the
cube (`ofReal_vecNormSq_volumeAverageVec_sq_le`) bounds the squared mean by the
fourth normalized norm on `z'`; the volume-ratio comparison above bounds that by
`|cu_m|/|z'|` times the fourth norm on `cu_m`; and the fourth moment of the
latter is finite by `gradFour_finite_of_regbounds`. -/
theorem memLp_vecNormSq_volumeAverageVec_grad_of_containment [NeZero d] (hd : 2 ≤ d)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    {z' : TriadicCube d} (hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ))) :
    MemLp (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad))) 2 P.toMeasure := by
  classical
  have hfin := gradFour_finite_of_regbounds hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    he w hw
  have hmeas := measurable_vecNormSq_volumeAverageVec_grad_leaves P S w hw hsub
  have hnn : ∀ omega : ShellSeq d, (0 : ℝ) ≤
      vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
    fun _ => pow_nonneg (vecNormSq_nonneg _) 2
  have hpt : ∀ omega : ShellSeq d,
      ENNReal.ofReal (vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) ^ (2 : ℕ)) ≤
        ENNReal.ofReal (cubeVolume (originCube d (S.m : ℤ)) / cubeVolume z') *
          (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
            ((w omega).toH1Function.grad)) ^ (4 : ℕ) := by
    intro omega
    refine le_trans (ofReal_vecNormSq_volumeAverageVec_sq_le
      (memVectorL2_mono hsub (w omega).toH1Function.grad_memVectorL2)) ?_
    show (SuperdiffusionCLT.Section2.Norms.cubeLpENorm z' 4
        (hilbertifyVecField ((w omega).toH1Function.grad))) ^ (4 : ℕ) ≤
      ENNReal.ofReal (cubeVolume (originCube d (S.m : ℤ)) / cubeVolume z') *
        (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (S.m : ℤ)) 4
          (hilbertifyVecField ((w omega).toH1Function.grad))) ^ (4 : ℕ)
    exact cubeLpENorm_four_pow_le_of_openCubeSet_subset hsub _
  refine (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr ?_
  refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [MeasureTheory.lintegral_const_mul'
    (r := ENNReal.ofReal (cubeVolume (originCube d (S.m : ℤ)) / cubeVolume z'))
    (f := fun omega : ShellSeq d =>
      (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
        ((w omega).toH1Function.grad)) ^ (4 : ℕ))
    ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hfin)

/-! ## The two leaves, one carrier smaller -/

/-- **The `_hbHalfInt` binder of the final assembly, discharged with no hypothesis.**
The range of the binder is containment in `cu_m` -- not membership in the
descendant lattice -- and containment is exactly what the two carriers of the
half weight need. -/
theorem hbHalfInt_discharged [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ1V2 : ShellLawJ1Restriction d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    {e : Vec d} (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    ∀ z' z : TriadicCube d,
      openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)) →
        openCubeSet z ⊆ openCubeSet z' →
          Integrable (fun omega : ShellSeq d =>
            translatedBlockHalfWeight nu S.LPrime w omega z' z) P.toMeasure := by
  intro z' z hsub _
  have hsq := memLp_vecNormSq_volumeAverageVec_grad_of_containment hd hnu hnu1 hPrefix
    hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw hsub
  have hprod : Integrable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)) *
        translatedBlockNorm nu S.LPrime omega z) P.toMeasure :=
    hsq.integrable_mul (memLp_two_translatedBlockNorm_final hnu hPrefix hJ2 hJ3 hJ4 S.LPrime z)
  have hmeas := measurable_translatedBlockHalfWeight_leaves hnu P S w hw hsub z
  refine Integrable.mono' hprod hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  have hnn : 0 ≤ translatedBlockHalfWeight nu S.LPrime w omega z' z :=
    vecNormSq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact translatedBlockHalfWeight_le hnu S.LPrime w omega z' z

end

end SuperdiffusionCLT.Section3.Terms
