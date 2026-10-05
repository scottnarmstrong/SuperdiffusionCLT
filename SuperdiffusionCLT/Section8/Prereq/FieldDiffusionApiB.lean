/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApi
public import SuperdiffusionCLT.Section8.Brownian.BrownianMotion

@[expose] public section

open scoped ZeroAtInfty NNReal ENNReal

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess Filter Topology ProbabilityTheory
  SuperdiffusionCLT.Section8.Brownian

variable {d : ℕ}

/-- Composition with `x ↦ ε x` on `C₀(ℝ^d)`, as a contraction. -/
noncomputable def fd_dilC0 (ε : ℝ) (hε : ε ≠ 0) : C₀(Vec d, ℝ) →L[ℝ] C₀(Vec d, ℝ) :=
  LinearMap.mkContinuous
    (ZeroAtInftyContinuousMap.compLinearMap (R := ℝ)
      (Homeomorph.smulOfNeZero ε hε).toCocompactMap) 1 (fun f => by
    rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun x => ?_
    have := f.toBCF.norm_coe_le_norm (ε • x)
    change ‖f (ε • x)‖ ≤ _
    simpa only [Real.norm_eq_abs, ZeroAtInftyContinuousMap.toBCF_apply, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using this)

theorem fd_dilC0_apply (ε : ℝ) (hε : ε ≠ 0) (f : C₀(Vec d, ℝ)) (x : Vec d) :
    fd_dilC0 ε hε f x = f (ε • x) := rfl

theorem fd_dilC0_dilC0 (ε : ℝ) (hε : ε ≠ 0) (f : C₀(Vec d, ℝ)) :
    fd_dilC0 ε⁻¹ (inv_ne_zero hε) (fd_dilC0 ε hε f) = f := by
  ext x
  simp [fd_dilC0_apply, smul_smul, mul_inv_cancel₀ hε]

/-- Scalar multiples of the coefficient scale `divForm`. -/
theorem divForm_smul_coeff (A : CoeffField d) {r : ℝ} (hr : r ≠ 0) (u : Vec d → ℝ) (x : Vec d) :
    divForm 1 (fun y => r • A y) u x = r * divForm 1 A u x := by
  unfold divForm
  rw [one_mul, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun y => ∑ j : Fin d, (r • A y) i j * fderiv ℝ u y (Pi.single j 1)) =
      fun y => r * ∑ j : Fin d, A y i j * fderiv ℝ u y (Pi.single j 1) := by
    funext y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]
  rw [hfun]
  by_cases hd : DifferentiableAt ℝ (fun y => ∑ j : Fin d, A y i j * fderiv ℝ u y (Pi.single j 1)) x
  · rw [fderiv_const_mul hd]
    simp
  · have hd' : ¬ DifferentiableAt ℝ
        (fun y => r * ∑ j : Fin d, A y i j * fderiv ℝ u y (Pi.single j 1)) x := by
      intro h
      apply hd
      have := h.const_mul r⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ hr, one_mul] using this
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']
    simp

section Conjugate

variable (S S' : SubMarkovKernelSemigroup (Vec d)) {ε : ℝ} (hε : ε ≠ 0) {τ : ℝ≥0}

include hε

theorem fd_kernelIntegral_conj
    (hS' : ∀ t x, S' t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y)) (t : ℝ≥0)
    (f : C₀(Vec d, ℝ)) (x : Vec d) :
    kernelIntegral (S' t) f x = kernelIntegral (S (τ * t)) (fd_dilC0 ε hε f) (ε⁻¹ • x) := by
  unfold kernelIntegral
  rw [hS' t x, integral_map (continuous_const_smul ε).measurable.aemeasurable
    (map_continuous f).aestronglyMeasurable]
  rfl

theorem fd_mapsC0_conj (hS' : ∀ t x, S' t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y))
    (hC0 : S.MapsC0) : S'.MapsC0 := by
  intro t f
  set g := S.c0KernelIntegral hC0 (τ * t) (fd_dilC0 ε hε f) with hg
  have hfun : kernelIntegral (S' t) f = ⇑(fd_dilC0 ε⁻¹ (inv_ne_zero hε) g) := by
    funext x
    rw [fd_kernelIntegral_conj S S' hε hS']
    rfl
  rw [hfun]
  exact ⟨map_continuous (fd_dilC0 ε⁻¹ (inv_ne_zero hε) g),
    ZeroAtInftyContinuousMapClass.zero_at_infty (fd_dilC0 ε⁻¹ (inv_ne_zero hε) g)⟩

theorem fd_c0Operator_conj (hS' : ∀ t x, S' t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y))
    (hC0 : S.MapsC0) (hC0' : S'.MapsC0) (t : ℝ≥0) (f : C₀(Vec d, ℝ)) :
    S'.c0Operator hC0' t f =
      fd_dilC0 ε⁻¹ (inv_ne_zero hε) (S.c0Operator hC0 (τ * t) (fd_dilC0 ε hε f)) := by
  ext x
  rw [SubMarkovKernelSemigroup.c0Operator_apply, fd_kernelIntegral_conj S S' hε hS']
  rfl

theorem fd_feller_conj (hS' : ∀ t x, S' t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y))
    (hF : S.IsFellerKernelSemigroup) : S'.IsFellerKernelSemigroup := by
  obtain ⟨hC0, hT⟩ := hF
  have hC0' := fd_mapsC0_conj S S' hε hS' hC0
  refine ⟨hC0', fun f => ?_⟩
  have hfun : (fun t : ℝ≥0 => S'.c0Operator hC0' t f) = fun t =>
      fd_dilC0 ε⁻¹ (inv_ne_zero hε) (S.c0Operator hC0 (τ * t) (fd_dilC0 ε hε f)) :=
    funext fun t => fd_c0Operator_conj S S' hε hS' hC0 hC0' t f
  rw [hfun]
  exact (fd_dilC0 ε⁻¹ (inv_ne_zero hε)).continuous.comp
    ((hT (fd_dilC0 ε hε f)).comp (continuous_const.mul continuous_id))

end Conjugate

/-- The rescaled-conjugacy hypothesis in the form used by `MarkovProcess`. -/
theorem fd_isRescaledConjugate {S S' : SubMarkovKernelSemigroup (Vec d)} {ε : ℝ} (hε : ε ≠ 0)
    {τ : ℝ≥0} (hS' : ∀ t x, S' t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y)) :
    SubMarkovKernelSemigroup.IsRescaledConjugate S S' (Homeomorph.smulOfNeZero ε hε) τ :=
  fun t x => hS' t x

/-- **Induced map of `IsDivergenceFormFeller` under space-time dilation.**  If `S'` is the
space-time dilation of `S` (space `ε`, time `τ`), that is
`S' t x = (S (τ t) (ε⁻¹ x)).map (ε · )`, and `S` is a conservative Feller semigroup with generator
`∇·(a∇·)`, then `S'` is a conservative Feller semigroup with generator
`∇·(ε² τ a(ε⁻¹ ·) ∇·)`. -/
theorem isDivergenceFormFeller_dilate (a : CoeffField d) {S S' : SubMarkovKernelSemigroup (Vec d)}
    {ε : ℝ} (hε : ε ≠ 0) {τ : ℝ≥0} (hτ : 0 < τ)
    (hS' : ∀ t x, S' t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y))
    (h : IsDivergenceFormFeller a S) :
    IsDivergenceFormFeller (fun y => (ε ^ 2 * (τ : ℝ)) • a (ε⁻¹ • y)) S' := by
  obtain ⟨hcons, hF, hgen⟩ := h
  have hτ' : (τ : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hτ).ne'
  have hr : ε ^ 2 * (τ : ℝ) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hε) hτ'
  have hF' : S'.IsFellerKernelSemigroup := fd_feller_conj S S' hε hS' hF
  refine ⟨(fd_isRescaledConjugate hε hS').isConservative hcons, hF', ?_⟩
  intro u v hu hv
  set w : C₀(Vec d, ℝ) := fd_dilC0 ε hε u with hw
  have hwc : ContDiff ℝ 2 (⇑w) := hu.comp (contDiff_const_smul ε)
  have hvw : ∀ z, ((τ : ℝ)⁻¹ • fd_dilC0 ε hε v) z = divForm 1 a (⇑w) z := by
    intro z
    have h1 : divForm 1 a (⇑w) z =
        ε ^ 2 * divForm 1 (fun y => a (ε⁻¹ • y)) u (ε • z) :=
      divForm_comp_smul 1 a (⇑u) hε z
    have h2 := hv (ε • z)
    rw [divForm_smul_coeff (fun y => a (ε⁻¹ • y)) hr] at h2
    rw [h1]
    change (τ : ℝ)⁻¹ * v (ε • z) = _
    rw [h2]
    field_simp
  obtain ⟨hwdom, hgw⟩ := hgen w ((τ : ℝ)⁻¹ • fd_dilC0 ε hε v) hwc hvw
  have hlim := hF.c0Semigroup.tendsto_generator' ⟨w, hwdom⟩
  rw [hgw] at hlim
  have htime : Tendsto (fun t : ℝ≥0 => τ * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ≥0 => τ * t) (𝓝 0) (𝓝 (τ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa only [mul_zero] using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hτ ht
  have hlim2 := ((fd_dilC0 ε⁻¹ (inv_ne_zero hε)).continuous.tendsto _).comp (hlim.comp htime)
  have hlim3 := hlim2.const_smul (τ : ℝ)
  have hfun : (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (hF'.c0Semigroup t u - u)) =
      fun t => (τ : ℝ) • (fd_dilC0 ε⁻¹ (inv_ne_zero hε)
        (((τ * t : ℝ≥0) : ℝ)⁻¹ • (hF.c0Semigroup (τ * t) w - w))) := by
    funext t
    have hop : hF'.c0Semigroup t u = fd_dilC0 ε⁻¹ (inv_ne_zero hε) (hF.c0Semigroup (τ * t) w) :=
      fd_c0Operator_conj S S' hε hS' hF.mapsC0 hF'.mapsC0 t u
    have hu' : u = fd_dilC0 ε⁻¹ (inv_ne_zero hε) w := (fd_dilC0_dilC0 ε hε u).symm
    rw [hop, map_smul, map_sub, ← hu', smul_smul]
    by_cases ht : (t : ℝ) = 0
    · simp [ht]
    · congr 1
      push_cast
      field_simp
  have hlim4 : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (hF'.c0Semigroup t u - u)) (𝓝[>] 0)
      (𝓝 v) := by
    have hv' : (τ : ℝ) • fd_dilC0 ε⁻¹ (inv_ne_zero hε) ((τ : ℝ)⁻¹ • fd_dilC0 ε hε v) = v := by
      rw [map_smul, fd_dilC0_dilC0, smul_smul, mul_inv_cancel₀ hτ', one_smul]
    rw [hfun, ← hv']
    exact hlim3
  exact ⟨hF'.c0Semigroup.mem_generatorDomain_of_tendsto hlim4,
    hF'.c0Semigroup.generator_mk_eq hlim4⟩

section Construction

/-- The space-time dilation of a kernel semigroup: space `ε`, time `τ`. -/
noncomputable def fd_dilateSemigroup (S : SubMarkovKernelSemigroup (Vec d)) {ε : ℝ} (hε : ε ≠ 0)
    (τ : ℝ≥0) : SubMarkovKernelSemigroup (Vec d) where
  kernel t := Kernel.comap (Kernel.map (S (τ * t)) (fun y : Vec d => ε • y))
    (fun x : Vec d => ε⁻¹ • x) (continuous_const_smul ε⁻¹).measurable
  measurable_kernel := by
    have hm : Measurable (fun y : Vec d => ε • y) := (continuous_const_smul ε).measurable
    have h1 : Measurable (fun p : ℝ≥0 × Vec d => (τ * p.1, ε⁻¹ • p.2)) :=
      (measurable_const.mul measurable_fst).prodMk
        ((continuous_const_smul ε⁻¹).measurable.comp measurable_snd)
    have h2 := (Measure.measurable_map _ hm).comp (S.measurable_kernel.comp h1)
    convert h2 using 1
    funext p
    rw [Kernel.comap_apply, Kernel.map_apply _ hm]
    rfl
  kernel_zero := by
    refine Kernel.ext fun x => ?_
    have hm : Measurable (fun y : Vec d => ε • y) := (continuous_const_smul ε).measurable
    rw [Kernel.comap_apply, Kernel.map_apply _ hm, mul_zero, S.zero, Kernel.id_apply,
      Kernel.id_apply]
    exact (Measure.map_dirac' hm (ε⁻¹ • x)).trans (by rw [smul_inv_smul₀ hε])
  kernel_add := by
    intro s t
    refine Kernel.ext fun x => ?_
    have hm : Measurable (fun y : Vec d => ε • y) := (continuous_const_smul ε).measurable
    refine Measure.ext fun B hB => ?_
    have hpre : MeasurableSet ((fun y : Vec d => ε • y) ⁻¹' B) := hm hB
    rw [Kernel.comp_apply, Measure.bind_apply hB (Kernel.aemeasurable _)]
    simp only [Kernel.comap_apply, Kernel.map_apply _ hm]
    have hf : Measurable (fun a : Vec d =>
        ((S.kernel (τ * t)) (ε⁻¹ • a)) ((fun y : Vec d => ε • y) ⁻¹' B)) :=
      (Kernel.measurable_coe _ hpre).comp (continuous_const_smul ε⁻¹).measurable
    have hrw : ∀ a : Vec d, (Measure.map (fun y : Vec d => ε • y)
        ((S.kernel (τ * t)) (ε⁻¹ • a))) B =
        ((S.kernel (τ * t)) (ε⁻¹ • a)) ((fun y : Vec d => ε • y) ⁻¹' B) :=
      fun a => Measure.map_apply hm hB
    simp only [hrw]
    rw [Measure.map_apply hm hB, mul_add, S.add_apply' _ _ _ hpre, lintegral_map hf hm]
    refine lintegral_congr fun y => ?_
    rw [inv_smul_smul₀ hε]
  isSubMarkovKernel t := by
    intro x
    have hm : Measurable (fun y : Vec d => ε • y) := (continuous_const_smul ε).measurable
    rw [Kernel.comap_apply, Kernel.map_apply _ hm, Measure.map_apply hm MeasurableSet.univ]
    exact S.measure_le_one _ _ _

theorem fd_dilateSemigroup_apply (S : SubMarkovKernelSemigroup (Vec d)) {ε : ℝ} (hε : ε ≠ 0)
    (τ : ℝ≥0) (t : ℝ≥0) (x : Vec d) :
    fd_dilateSemigroup S hε τ t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y) := by
  have hm : Measurable (fun y : Vec d => ε • y) := (continuous_const_smul ε).measurable
  show (Kernel.comap (Kernel.map (S (τ * t)) (fun y : Vec d => ε • y))
    (fun x : Vec d => ε⁻¹ • x) (continuous_const_smul ε⁻¹).measurable) x = _
  rw [Kernel.comap_apply, Kernel.map_apply _ hm]

end Construction

section PathLaw

open SubMarkovKernelSemigroup

/-- The finite-dimensional distributions of a path law at arbitrary ordered times. -/
theorem fd_pathLaw_map_finiteEvaluation_ordered {S : SubMarkovKernelSemigroup (Vec d)}
    (hP : S.IsConservative) {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw S Q) {n : ℕ} (times : FiniteOrderedTimes n) (x : Vec d) :
    (Q x).map (ContinuousPath.finiteEvaluation (fun i => times i)) =
      finiteTimeKernel S times x := by
  classical
  have hmem : ∀ i : Fin n,
      times i ∈ Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n)) :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  let I : Finset ℝ≥0 := Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n))
  let phi : Fin n ↪o I :=
    OrderEmbedding.ofStrictMono (fun i ↦ (⟨times i, hmem i⟩ : I))
      (fun _ _ hij ↦ times.strictMono hij)
  let emb : Fin n ↪o Fin I.card := phi.trans (I.orderIsoOfFin rfl).symm.toOrderEmbedding
  have hphi : ∀ i : Fin n, ((phi i : I) : ℝ≥0) = times i := fun _ ↦ rfl
  have hsel : Measurable (fun w : I → Vec d ↦ w ∘ (phi : Fin n → I)) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (phi i)
  have hfinset : Measurable (ContinuousPath.finsetEvaluation (alpha := Vec d) I) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finiteEvaluation (α := Vec d) (fun i ↦ times i) =
      (fun w : I → Vec d ↦ w ∘ (phi : Fin n → I)) ∘
        ContinuousPath.finsetEvaluation (alpha := Vec d) I := rfl
  have hrestrict : (fun w : I → Vec d ↦ w ∘ (phi : Fin n → I)) ∘
      orderedPathToFiniteSet (α := Vec d) I = FiniteOrderedTimes.restrictPath emb := rfl
  have htimes : (finiteSetTimes I).restrict emb = times := by
    apply DFunLike.ext _ _
    intro i
    show finiteSetTimes I ((I.orderIsoOfFin rfl).symm (phi i)) = times i
    rw [finiteSetTimes_orderIsoOfFin_symm_apply, hphi i]
  have hker := hP.finiteTimeKernel_map_restrictPath S (finiteSetTimes I) emb
  have hres : Measurable (FiniteOrderedTimes.restrictPath (α := Vec d) emb) := by
    rw [← hrestrict]
    exact hsel.comp (measurable_orderedPathToFiniteSet I)
  rw [hcomp, ← Measure.map_map hsel hfinset, (hQ x).2 I, finiteSetKernel_eq_map,
    Kernel.map_apply _ (measurable_orderedPathToFiniteSet I) x,
    Measure.map_map hsel (measurable_orderedPathToFiniteSet I), hrestrict,
    ← Kernel.map_apply _ hres x, hker, htimes]

/-- **`IsContinuousPathLaw` is preserved by space-time dilation**: if `Q` is a path law of `S` and
`S'` is the dilation of `S` (space `ε`, time `τ`), then `x ↦ (Q (ε⁻¹ x)).map (scalePath ε τ)` is a
path law of `S'`. -/
theorem isContinuousPathLaw_dilate {S S' : SubMarkovKernelSemigroup (Vec d)}
    (hP : S.IsConservative) {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw S Q) {ε : ℝ} (hε : ε ≠ 0) {τ : ℝ≥0} (hτ : 0 < τ)
    (hS' : ∀ t x, S' t x = (S (τ * t) (ε⁻¹ • x)).map (fun y => ε • y)) :
    IsContinuousPathLaw S' (fun x => (Q (ε⁻¹ • x)).map (scalePath ε τ)) := by
  intro x
  have hmeas : Measurable (scalePath (d := d) ε τ) := (continuous_scalePath ε τ).measurable
  have : IsProbabilityMeasure (Q (ε⁻¹ • x)) := (hQ (ε⁻¹ • x)).1
  refine ⟨(Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 inferInstance, fun I => ?_⟩
  let e : Vec d ≃ₜ Vec d := Homeomorph.smulOfNeZero ε hε
  have hconj := fd_isRescaledConjugate hε hS'
  have hmapPath : Measurable
      ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
        orderedPathToFiniteSet (α := Vec d) I) :=
    (FiniteOrderedTimes.measurable_mapPath e.measurable).comp
      (measurable_orderedPathToFiniteSet I)
  have hfinite : Measurable (ContinuousPath.finiteEvaluation (α := Vec d)
      (fun i ↦ ((finiteSetTimes I).rescale τ hτ) i)) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finsetEvaluation (alpha := Vec d) I ∘ scalePath ε τ =
      ((FiniteOrderedTimes.mapPath e : (I → Vec d) → I → Vec d) ∘
        orderedPathToFiniteSet (α := Vec d) I) ∘
        ContinuousPath.finiteEvaluation (α := Vec d)
          (fun i ↦ ((finiteSetTimes I).rescale τ hτ) i) := by
    funext omega t
    show e (omega (τ * (t : ℝ≥0))) =
      e (omega (τ * finiteSetTimes I ((I.orderIsoOfFin rfl).symm t)))
    rw [finiteSetTimes_orderIsoOfFin_symm_apply]
  have hK := hconj.finiteSetKernel_eq hτ hP I
  rw [Measure.map_map (ContinuousPath.measurable_finiteEvaluation _) hmeas, hcomp,
    ← Measure.map_map hmapPath hfinite, fd_pathLaw_map_finiteEvaluation_ordered hP hQ _ _, hK,
    Kernel.map_apply _ hmapPath, Kernel.comap_apply]
  rfl

end PathLaw

/-- `IsDivergenceFormFeller` for the explicit space-time dilation `fd_dilateSemigroup`. -/
theorem isDivergenceFormFeller_dilateSemigroup (a : CoeffField d) {S : SubMarkovKernelSemigroup (Vec d)}
    {ε : ℝ} (hε : ε ≠ 0) {τ : ℝ≥0} (hτ : 0 < τ) (h : IsDivergenceFormFeller a S) :
    IsDivergenceFormFeller (fun y => (ε ^ 2 * (τ : ℝ)) • a (ε⁻¹ • y))
      (fd_dilateSemigroup S hε τ) :=
  isDivergenceFormFeller_dilate a hε hτ (fd_dilateSemigroup_apply S hε τ) h

/-! Witnesses. -/

private theorem fd_isContinuousPathLaw_brownianMotion (d : ℕ) :
    IsContinuousPathLaw (heatSemigroup d) (fun x => brownianMotion d x) := by
  intro x
  refine ⟨inferInstance, fun I => ?_⟩
  have h := (isFellerKernelSemigroup_heatSemigroup d).continuousProcess_map_finiteEvaluation
    (heatSemigroup d) (isConservative_heatSemigroup d) (kolmogorovRegular_heatSemigroup d) I
  have h2 := congrArg (fun κ : ProbabilityTheory.Kernel (Vec d) (I → Vec d) => κ x) h
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_finiteEvaluation _)] at h2
  exact h2

/-- The dilation of Brownian motion is a path law of the dilated heat semigroup. -/
example (d : ℕ) :
    IsContinuousPathLaw (fd_dilateSemigroup (heatSemigroup d) (two_ne_zero : (2 : ℝ) ≠ 0) 1)
      (fun x => (brownianMotion d ((2 : ℝ)⁻¹ • x)).map (scalePath 2 1)) :=
  isContinuousPathLaw_dilate (isConservative_heatSemigroup d) (fd_isContinuousPathLaw_brownianMotion d)
    two_ne_zero one_pos (fd_dilateSemigroup_apply _ _ _)

example (d : ℕ) (f : C₀(Vec d, ℝ)) : fd_dilC0 1 one_ne_zero f = f := by
  ext x
  simp [fd_dilC0_apply]

example (d : ℕ) (x : Vec d) :
    divForm 1 (fun _ => (3 : ℝ) • (1 : Mat d)) (fun y : Vec d => ∑ i, y i ^ 2) x =
      3 * divForm 1 (fun _ => (1 : Mat d)) (fun y : Vec d => ∑ i, y i ^ 2) x :=
  divForm_smul_coeff (fun _ => (1 : Mat d)) (by norm_num) _ x

end SuperdiffusionCLT.Section8
