/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Obligations
public import SuperdiffusionCLT.Section3.Terms.ResponseHessianMeasurableB
public import SuperdiffusionCLT.Section3.Terms.HatNegNormMeasurable

/-!
# Subcube Hessian measurability for the V4 conclusion

Restriction to a smaller measure is a contraction on L² classes. Applying
this to the measurable Hessian class proves sample measurability of the
Hessian seminorm on each subcube, independently of its chosen representative.
The centered negative norm is measurable on L² classes as a supremum of
continuous pairings. The measurable glued flux class then removes the second
sample measurability obligation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

/-- Passing an L² class to a dominated measure is a contraction. -/
theorem rhsTerm3Measurable_lipschitz_toLp_monoMeasure
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ ν : MeasureTheory.Measure α} (hν : ν ≤ μ) :
    LipschitzWith 1 (fun f : MeasureTheory.Lp E 2 μ =>
      ((MeasureTheory.Lp.memLp f).mono_measure hν).toLp (fun x => f x)) := by
  intro f g
  simp only [ENNReal.coe_one, one_mul]
  rw [MeasureTheory.Lp.edist_def, MeasureTheory.Lp.edist_def]
  have heq :
      (fun x => ((MeasureTheory.Lp.memLp f).mono_measure hν).toLp (fun x => f x) x -
        ((MeasureTheory.Lp.memLp g).mono_measure hν).toLp (fun x => g x) x) =ᵐ[ν]
      (fun x => f x - g x) := by
    filter_upwards [((MeasureTheory.Lp.memLp f).mono_measure hν).coeFn_toLp,
      ((MeasureTheory.Lp.memLp g).mono_measure hν).coeFn_toLp] with x hx hy
    exact congrArg₂ (fun a b : E => a - b) hx hy
  exact (MeasureTheory.eLpNorm_congr_ae heq).le.trans
    (MeasureTheory.eLpNorm_mono_measure _ hν)

/-- The L² norm of a measurable Hessian class is measurable on any subcube. -/
theorem rhsTerm3Measurable_measurable_hessian_subcube
    {d : ℕ} [NeZero d] {LPrime ellPrime m : ℕ} {p : Homogenization.Vec d}
    {w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
      Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)))}
    (hw : ∀ ω, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
      ω LPrime ellPrime m p (w ω))
    (H : ∀ ω, Homogenization.HasWeakHessianOn
      (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) (w ω).toH1Function)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) :
    Measurable (fun ω => centredSeminormAt (H ω) R) := by
  let U := Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))
  let μ := Homogenization.volumeMeasureOn U
  let ν := Homogenization.volumeMeasureOn (Homogenization.openCubeSet R)
  have hν : ν ≤ μ := MeasureTheory.Measure.restrict_mono hR le_rfl
  let E := MeasureTheory.Lp (Homogenization.HilbertMat d) 2 μ
  let F := MeasureTheory.Lp (Homogenization.HilbertMat d) 2 ν
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have : MeasureTheory.IsFiniteMeasure μ :=
    SuperdiffusionCLT.Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet _
  let A : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → E := fun ω =>
    hessianCarrierLp (U := U) (fun x i j => (H ω).hess i j x)
      (fun i j => (H ω).hess_memL2 i j)
  have hA : Measurable A :=
    measurable_hessianCarrierLp
      (Homogenization.isOpen_openCubeSet _) (ne_of_lt (Homogenization.volume_openCubeSet_lt_top _))
      (measurable_gradToHilbertVectorL2_of_isDirichletResponse hw)
  let T : E → F := fun f =>
    ((MeasureTheory.Lp.memLp f).mono_measure hν).toLp (fun x => f x)
  have hT : Measurable T := (rhsTerm3Measurable_lipschitz_toLp_monoMeasure hν).continuous.measurable
  have hnorm : Measurable (fun ω => ‖T (A ω)‖ₑ) := (hT.comp hA).enorm
  have heq : ∀ ω, ‖T (A ω)‖ₑ = MeasureTheory.eLpNorm
      (fun x => Homogenization.HilbertMat.ofMat (fun i j => (H ω).hess i j x)) 2 ν := by
    intro ω
    rw [MeasureTheory.Lp.enorm_def]
    apply MeasureTheory.eLpNorm_congr_ae
    exact (((MeasureTheory.Lp.memLp (A ω)).mono_measure hν).coeFn_toLp).trans
      (MeasureTheory.ae_mono hν (hessianCarrierLp_coeFn_ae
        (fun i j => (H ω).hess_memL2 i j)))
  have hEnorm : Measurable (fun ω => MeasureTheory.eLpNorm
      (fun x => Homogenization.HilbertMat.ofMat (fun i j => (H ω).hess i j x)) 2 ν) := by
    simpa only [heq] using hnorm
  unfold centredSeminormAt
  simp_rw [cubeLpENorm_eq_const_mul_eLpNorm R (by norm_num : (2 : ENNReal) ≠ ⊤)]
  exact (Measurable.const_smul (M := ENNReal) hEnorm _).ennreal_toReal

/-- The sample-side Hessian seminorm premise at the actual oscillation witness. -/
theorem rhsTerm3Measurable_aestronglyMeasurable_osc
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {S : SuperdiffusionCLT.Section3.Setup.ScaleSelection}
    (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S)
    {p : Homogenization.Vec d}
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
      Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (hw : ∀ ω, SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
      ω S.LPrime S.ellPrime S.m p (w ω))
    {μ : MeasureTheory.Measure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m) :
    MeasureTheory.AEStronglyMeasurable
      (fun ω => centredSeminormAt (oscHessianWitness hd hSorder w hw ω) R) μ := by
  rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
  exact (rhsTerm3Measurable_measurable_hessian_subcube hw
    (oscHessianWitness hd hSorder w hw) R
    (Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hR)).aestronglyMeasurable

/-- The centered negative norm is measurable as a supremum of continuous
linear pairings on the L² class space. -/
theorem rhsTerm3Measurable_aemeasurable_centredNegNorm
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {R : Homogenization.TriadicCube d} {F : Ω → Homogenization.Vec d → Homogenization.Vec d}
    (hF : ∀ ω, Homogenization.MemVectorL2 (Homogenization.openCubeSet R) (F ω))
    (hclass : AEMeasurable
      (fun ω => Homogenization.toHilbertVectorL2OfVecField (hF ω)) μ) :
    AEMeasurable (fun ω => (centredSeminormNegNorm R (F ω)).toReal) μ := by
  have htest : ∀ T : CentredSeminormTestField R,
      Homogenization.MemVectorL2 (Homogenization.openCubeSet R) T.toField := by
    intro T
    have h := SuperdiffusionCLT.Section2.Estimates.Stream.memLp_two_volume_restrict_of_memLp R
      (SuperdiffusionCLT.Section3.ResponseFields.memLp_hilbertifyVecField_iff.mp
        (memLp_hilbertifyVecField_toField T))
    rwa [Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at h
  let N : Homogenization.HilbertVectorL2 (Homogenization.openCubeSet R) → ENNReal :=
    fun V => ⨆ T : CentredSeminormTestField R,
      ENNReal.ofReal ((Homogenization.cubeVolume R)⁻¹ *
        inner ℝ V (Homogenization.toHilbertVectorL2OfVecField (htest T)))
  have hN : Measurable N := by
    apply LowerSemicontinuous.measurable
    apply lowerSemicontinuous_iSup
    intro T
    exact (ENNReal.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).lowerSemicontinuous
  have heq : ∀ ω, centredSeminormNegNorm R (F ω) =
      N (Homogenization.toHilbertVectorL2OfVecField (hF ω)) := by
    intro ω
    unfold centredSeminormNegNorm N
    congr 1
    funext T
    rw [volumeAverage_vecDot_eq_inv_mul_inner (hF ω) (htest T)]
  simp_rw [heq]
  exact (hN.comp_aemeasurable hclass).ennreal_toReal

/-- The flux L² class is sample measurable on the large cube. -/
theorem rhsTerm3Measurable_aemeasurable_fluxClass
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (e : Homogenization.Vec d) :
    ∃ hF : ∀ ω, Homogenization.MemVectorL2
        (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)))
        (fluxFieldCarrier nu S ω (oscGluedGradM nu hnu S P e ω) (oscGluedGradN nu hnu S P e ω)),
      AEMeasurable (fun ω => Homogenization.toHilbertVectorL2OfVecField (hF ω)) P.toMeasure := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let Q := Homogenization.originCube d (S.m : ℤ)
  let F := SuperdiffusionCLT.Section3.Setup.fluxSlot nu S.LPrime P S.n e
  have hM := fun ω => memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.m S.m F ω Q
  have hN := fun ω => memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F ω Q
  have hmul := fun ω f (hf : Homogenization.MemVectorL2 (Homogenization.openCubeSet Q) f) =>
    memVectorL2_matVecMul_coefficientCutoff hnu ω S.LPrime Q hf
  refine ⟨fun ω => hmul ω _ ((hM ω).sub (hN ω)), ?_⟩
  have hmeas := measurable_matFieldMulClass_family (mu := P.toMeasure)
    (Homogenization.measurableSet_openCubeSet Q)
    (fun ω x => (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω S.LPrime).toCoeffField x)
    (measurable_prod_coefficientCutoff nu S.LPrime) hmul
    (fun ω => SuperdiffusionCLT.Section3.Setup.exists_matVecMul_bound_openCubeSet Q
      (fun i j => continuous_coefficientCutoff_entry nu ω S.LPrime i j))
    (continuous_sub.measurable.comp_aemeasurable
      ((measurable_gluedGradientClass hnu S.LPrime S.m S.m F).aemeasurable.prodMk
        (measurable_gluedGradientClass hnu S.LPrime S.n S.m F).aemeasurable))
  have heq : ∀ ω,
      SuperdiffusionCLT.Section3.Setup.matFieldMulClass
        (fun x => (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu ω S.LPrime).toCoeffField x)
        (hmul ω)
        (Homogenization.toHilbertVectorL2OfVecField (hM ω) -
          Homogenization.toHilbertVectorL2OfVecField (hN ω)) =
        Homogenization.toHilbertVectorL2OfVecField (hmul ω _ ((hM ω).sub (hN ω))) := by
    intro ω
    rw [← Homogenization.toHilbertVectorL2OfVecField_sub (hM ω) (hN ω),
      SuperdiffusionCLT.Section3.Setup.matFieldMulClass_toHilbertVectorL2OfVecField]
  simp only [Function.comp_def, heq] at hmeas
  exact hmeas

/-- The seminorm flux observable is sample measurable on every subcube. -/
theorem rhsTerm3Measurable_aestronglyMeasurable_flux
    {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (e : Homogenization.Vec d) {R : Homogenization.TriadicCube d}
    (hR : R ∈ SuperdiffusionCLT.Section2.Estimates.Stream.largeCubeSubcubes d S.n S.m) :
    MeasureTheory.AEStronglyMeasurable (fun ω => seminormFluxNeg nu hnu S P e ω R) P.toMeasure := by
  obtain ⟨hF, hclass⟩ := rhsTerm3Measurable_aemeasurable_fluxClass hnu S P e
  have hsub : Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
    exact Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hμ : Homogenization.volumeMeasureOn (Homogenization.openCubeSet R) ≤
      Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) :=
    MeasureTheory.Measure.restrict_mono hsub le_rfl
  let A := fun ω => Homogenization.toHilbertVectorL2OfVecField (hF ω)
  let T := fun f : Homogenization.HilbertVectorL2
      (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))) =>
    ((MeasureTheory.Lp.memLp f).mono_measure hμ).toLp (fun x => f x)
  have hsmall := fun ω => (hF ω).mono_measure hμ
  have heq : ∀ ω, T (A ω) = Homogenization.toHilbertVectorL2OfVecField (hsmall ω) := by
    intro ω
    apply MeasureTheory.Lp.ext
    have hlarge : (fun x => A ω x) =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet R)]
        Homogenization.hilbertifyVecField
          (fluxFieldCarrier nu S ω (oscGluedGradM nu hnu S P e ω) (oscGluedGradN nu hnu S P e ω)) :=
      MeasureTheory.ae_mono hμ (Homogenization.coeFn_toHilbertVectorL2OfVecField (hF ω))
    exact (((MeasureTheory.Lp.memLp (A ω)).mono_measure hμ).coeFn_toLp).trans
      (hlarge.trans (Homogenization.coeFn_toHilbertVectorL2OfVecField (hsmall ω)).symm)
  have hsmallMeas : AEMeasurable
      (fun ω => Homogenization.toHilbertVectorL2OfVecField (hsmall ω)) P.toMeasure := by
    have hT : Measurable T := (rhsTerm3Measurable_lipschitz_toLp_monoMeasure hμ).continuous.measurable
    have h := hT.comp_aemeasurable hclass
    change AEMeasurable (fun ω => T (A ω)) _ at h
    simpa only [heq] using h
  exact (rhsTerm3Measurable_aemeasurable_centredNegNorm hsmall hsmallMeas).aestronglyMeasurable

end SuperdiffusionCLT.Section3.Terms
