module

public import SuperdiffusionCLTAudit.TheoremA.SolutionBasic
public import SuperdiffusionCLTAudit.TheoremA.Support.ProjectionTransport
public import SuperdiffusionCLTAudit.TheoremA.Support.BrownianUniqueness

/-!
# Theorem A — bridges between the challenge vocabulary and the library

Each challenge definition is identified with its library counterpart: definitionally where the
challenge copies the library's body, and through explicit equivalences for the two structures the
challenge restates (regular coefficient fields, as a subtype, and kernel semigroups).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace SuperdiffusionCLT.StatementAudit.TheoremA

variable {d : ℕ}

/-! ## Shell laws -/

theorem shellLawPrefix_lib {P : ProbabilityMeasure (ℕ → ShellField d)} (h : ShellLawPrefix d P) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P :=
  ⟨h.1, h.2⟩

theorem shellLawJ2_lib {P : ProbabilityMeasure (ℕ → ShellField d)} (h : ShellLawJ2 d P) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P :=
  ⟨h.1⟩

theorem shellLawJ3_lib {P : ProbabilityMeasure (ℕ → ShellField d)} (h : ShellLawJ3 d P) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P :=
  ⟨h.1⟩

theorem shellLawJ4_lib {P : ProbabilityMeasure (ℕ → ShellField d)} (h : ShellLawJ4 d P) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P :=
  ⟨fun R hR ↦ h.1 R hR, h.2⟩

/-! ## Regular coefficient fields -/

/-- A challenge regular field as a library regular field. -/
def toLibReg (a : RegField d) : Homogenization.RegCoeffField d := ⟨a.1, a.2.1, a.2.2⟩

/-- A library regular field as a challenge regular field. -/
def ofLibReg (a : Homogenization.RegCoeffField d) : RegField d :=
  ⟨a.toFun, a.entry_measurable, a.entry_locInt⟩

theorem comap_toLibReg :
    MeasurableSpace.comap (toLibReg (d := d)) inferInstance =
      (inferInstance : MeasurableSpace (RegField d)) := by
  change MeasurableSpace.comap toLibReg
      (Homogenization.pointwiseSigmaR d ⊔ Homogenization.entryTestSigmaR d) = _
  rw [MeasurableSpace.comap_sup, Homogenization.pointwiseSigmaR,
    Homogenization.entryTestSigmaR, MeasurableSpace.comap_comp, MeasurableSpace.comap_generateFrom]
  congr 2
  ext s
  constructor
  · rintro ⟨_, ⟨i, j, φ, hφ, t, ht, rfl⟩, rfl⟩
    exact ⟨i, j, φ, ⟨hφ.1, hφ.2, hφ.3⟩, t, ht, rfl⟩
  · rintro ⟨i, j, φ, hφ, t, ht, rfl⟩
    exact ⟨_, ⟨i, j, φ, ⟨hφ.1, hφ.2.1, hφ.2.2⟩, t, ht, rfl⟩, rfl⟩

/-- The measurable equivalence between the two presentations of regular fields. -/
def regEquiv : RegField d ≃ᵐ Homogenization.RegCoeffField d where
  toFun := toLibReg
  invFun := ofLibReg
  left_inv _ := Subtype.ext rfl
  right_inv _ := Homogenization.RegCoeffField.ext fun _ ↦ rfl
  measurable_toFun := by
    change Measurable toLibReg
    rw [measurable_iff_comap_le, comap_toLibReg]
  measurable_invFun := by
    change Measurable ofLibReg
    rw [measurable_iff_comap_le, show instMeasurableSpaceRegField d =
      MeasurableSpace.comap toLibReg inferInstance from comap_toLibReg.symm,
      MeasurableSpace.comap_comp]
    exact le_of_eq MeasurableSpace.comap_id

theorem toLibReg_block (F : ℕ → ShellField d) (n m : ℕ) :
    toLibReg (RegField.ofContinuous (∑ k ∈ Finset.Ioc n m, (F k).1.1)) =
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement F n m := by
  refine Homogenization.RegCoeffField.ext fun x ↦ ?_
  exact (ContinuousMap.sum_apply _ _ x).trans
    (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply F n m x).symm

theorem blockLaw_eq (P : ProbabilityMeasure (ℕ → ShellField d)) (n m : ℕ) :
    blockLaw P n m =
      (SuperdiffusionCLT.Section2.Cutoff.blockRegLaw P n m).toMeasure.map regEquiv.symm := by
  have hfun : (fun F : ℕ → ShellField d ↦ RegField.ofContinuous (∑ k ∈ Finset.Ioc n m, (F k).1.1)) =
      regEquiv.symm ∘ fun F ↦ SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement F n m := by
    funext F
    change _ = ofLibReg (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement F n m)
    rw [← toLibReg_block]
    exact Subtype.ext rfl
  have h2 := Measure.map_map (μ := P.toMeasure) regEquiv.symm.measurable
    (SuperdiffusionCLT.Section2.Cutoff.measurable_finiteShellIncrement (d := d) n m)
  exact (congrArg (fun f ↦ Measure.map f P.toMeasure) hfun).trans h2.symm

theorem map_blockLaw (P : ProbabilityMeasure (ℕ → ShellField d)) (n m : ℕ) :
    (blockLaw P n m).map regEquiv = (SuperdiffusionCLT.Section2.Cutoff.blockRegLaw P n m).toMeasure := by
  rw [blockLaw_eq, Measure.map_map regEquiv.measurable regEquiv.symm.measurable]
  simp

/-! ## The stationary projection -/

theorem starProjection_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K₁ K₂ : Submodule ℝ E} [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection]
    (h : K₁ = K₂) : K₁.starProjection = K₂.starProjection := by
  subst h
  rfl

theorem potentialProjection_eq {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
    [MeasurableConstVAdd (Vec d) Ω] {μ : Measure Ω} [VAddInvariantMeasure (Vec d) Ω μ] :
    potentialProjection (μ := μ) =
      SuperdiffusionCLT.Probability.Stationary.stationaryPotentialProjection (μ := μ) (d := d) := by
  unfold potentialProjection SuperdiffusionCLT.Probability.Stationary.stationaryPotentialProjection
  apply starProjection_congr
  unfold SuperdiffusionCLT.Probability.Stationary.stationaryPotentialSubspace
  congr 1
  exact Submodule.span_eq (SuperdiffusionCLT.Probability.Stationary.horizontalGradientRange
    (μ := μ) (d := d))

theorem shellLawJ5_lib {P : ProbabilityMeasure (ℕ → ShellField d)} {cStar K : ℝ}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (h : ShellLawJ5 d P cStar K) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 := by
  refine ⟨h.cStar_pos, h.K_pos, fun n m hnm e he ↦ ?_⟩
  have hstat := SuperdiffusionCLT.Section2.Cutoff.blockRegLaw_stationary hPrefix hJ2 n m
  have hmem := SuperdiffusionCLT.Section2.Cutoff.memLp_originForcing_blockRegLaw hJ3 n m e he
  have hvadd : ∀ (z : Vec d) (a : RegField d), regEquiv (z +ᵥ a) = Homogenization.translateReg z
      (regEquiv a) := fun _ _ ↦ rfl
  have : MeasurableConstVAdd (Vec d) (RegField d) :=
    ⟨fun z ↦ by
      have hc : (fun a : RegField d ↦ z +ᵥ a) =
          regEquiv.symm ∘ Homogenization.translateReg z ∘ regEquiv := by
        funext a
        exact (regEquiv.symm_apply_apply _).symm.trans (congrArg regEquiv.symm (hvadd z a))
      rw [hc]
      exact regEquiv.symm.measurable.comp
        ((Homogenization.measurable_translateReg z).comp regEquiv.measurable)⟩
  have : VAddInvariantMeasure (Vec d) (RegField d) (blockLaw P n m) :=
    ⟨fun z s hs ↦ by
      rw [blockLaw_eq, Measure.map_apply regEquiv.symm.measurable hs,
        Measure.map_apply regEquiv.symm.measurable (measurable_const_vadd z hs)]
      have hpre : regEquiv.symm ⁻¹' ((fun a : RegField d ↦ z +ᵥ a) ⁻¹' s) =
          Homogenization.translateReg z ⁻¹' (regEquiv.symm ⁻¹' s) := by
        ext a
        change z +ᵥ ofLibReg a ∈ s ↔ ofLibReg (Homogenization.translateReg z a) ∈ s
        rfl
      rw [hpre, ← Measure.map_apply (Homogenization.measurable_translateReg z)
        (regEquiv.symm.measurable hs), hstat z]⟩
  have hmem' : MemLp (fun a : RegField d ↦
      (WithLp.toLp 2 (Matrix.mulVec (a.1 0) e) : EuclideanSpace ℝ (Fin d))) 2 (blockLaw P n m) := by
    have h' : MemLp (SuperdiffusionCLT.Section2.Cutoff.originForcing e) 2
        ((blockLaw P n m).map regEquiv) := by
      rw [map_blockLaw]
      exact hmem
    exact (memLp_map_measure_iff
      (SuperdiffusionCLT.Section2.Cutoff.measurable_originForcing e).aestronglyMeasurable
      regEquiv.measurable.aemeasurable).mp h'
  have hJ := h.nondegenerate n m hnm e he hmem'
  have := SuperdiffusionCLT.Section2.Cutoff.blockRegLaw_vaddInvariant P n m hstat
  have hnorm := norm_stationaryPotentialProjection_congr (μ₁ := blockLaw P n m)
    (μ₂ := (SuperdiffusionCLT.Section2.Cutoff.blockRegLaw P n m).toMeasure) regEquiv hvadd
    (map_blockLaw P n m) (SuperdiffusionCLT.Section2.Cutoff.originForcing e) hmem hmem'
  rw [potentialProjection_eq] at hJ
  unfold SuperdiffusionCLT.Section2.Cutoff.blockPotentialResponse
    SuperdiffusionCLT.Section2.Cutoff.blockForcingL2
  rw [← hnorm]
  exact hJ

/-- The restriction σ-algebras coincide. -/
theorem shellLawJ1Restriction_lib {P : ProbabilityMeasure (ℕ → ShellField d)}
    (h : ShellLawJ1Restriction d P) :
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P := by
  refine ⟨fun n U V hU hV hsep ↦ ?_⟩
  have key : ∀ (W : Set (Vec d)) (hW : MeasurableSet W),
      MeasurableSpace.comap (fun j : ShellField d ↦
        RegField.restrict W hW (RegField.ofContinuous j.1.1)) inferInstance =
      SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma W hW := by
    intro W hW
    rw [← comap_toLibReg, MeasurableSpace.comap_comp]
    rfl
  have := h.1 n U V hU hV hsep
  rw [key, key] at this
  exact this

/-! ## Semigroups, paths and the heat kernel -/

/-- A challenge semigroup as a library semigroup. -/
def SubMarkovKernelSemigroup.toLib {α : Type*} [MeasurableSpace α]
    (S : SubMarkovKernelSemigroup α) : MarkovProcess.SubMarkovKernelSemigroup α :=
  ⟨S.kernel, S.measurable_kernel, S.kernel_zero, S.kernel_add, S.isSubMarkovKernel⟩

/-- A library semigroup as a challenge semigroup. -/
def SubMarkovKernelSemigroup.ofLib {α : Type*} [MeasurableSpace α]
    (S : MarkovProcess.SubMarkovKernelSemigroup α) : SubMarkovKernelSemigroup α :=
  ⟨S.kernel, S.measurable_kernel, S.kernel_zero, S.kernel_add, S.isSubMarkovKernel⟩

theorem finiteTimeKernel_eq {α : Type*} [MeasurableSpace α]
    (P : MarkovProcess.SubMarkovKernelSemigroup α) :
    ∀ {n : ℕ} (τ : OrderedTimes n),
      finiteTimeKernel (⇑P) τ = MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel P τ
  | 0, _ => rfl
  | n + 1, τ => by
      show Kernel.mapOfMeasurable
          (P (τ 0) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel (⇑P) τ.relativeTail)) _ _ = _
      rw [finiteTimeKernel_eq P τ.relativeTail]
      rfl

theorem finiteSetKernel_eq {α : Type*} [MeasurableSpace α]
    (P : MarkovProcess.SubMarkovKernelSemigroup α) (I : Finset ℝ≥0) :
    finiteSetKernel (⇑P) I = MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel P I := by
  unfold finiteSetKernel MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
  rw [finiteTimeKernel_eq]
  rfl

theorem isContinuousPathLaw_iff (P : MarkovProcess.SubMarkovKernelSemigroup (Vec d))
    (Q : Vec d → Measure (ContinuousPath (Vec d))) :
    IsContinuousPathLaw (⇑P) Q ↔ SuperdiffusionCLT.Section8.IsContinuousPathLaw P Q := by
  unfold IsContinuousPathLaw SuperdiffusionCLT.Section8.IsContinuousPathLaw
  simp only [finiteSetKernel_eq]
  rfl

theorem isDivergenceFormFeller_iff (a : CoeffField d) (S : SubMarkovKernelSemigroup (Vec d)) :
    IsDivergenceFormFeller a S ↔ SuperdiffusionCLT.Section8.IsDivergenceFormFeller a S.toLib := by
  constructor
  · rintro ⟨hcons, hC0, horb, hgen⟩
    have hF : S.toLib.IsFellerKernelSemigroup := ⟨hC0, horb⟩
    exact ⟨hcons, hF, fun u v hu hv ↦ (generator_eq_iff_tendsto S.toLib hF u v).mpr (hgen u v hu hv)⟩
  · rintro ⟨hcons, hF, hgen⟩
    exact ⟨hcons, hF.mapsC0, hF.hasContinuousC0Orbits,
      fun u v hu hv ↦ (generator_eq_iff_tendsto S.toLib hF u v).mp (hgen u v hu hv)⟩

theorem brownian_exists :
    ∃ W : Vec d → Measure (ContinuousPath (Vec d)), IsContinuousPathLaw (heatKernel d) W :=
  ⟨fun x ↦ SuperdiffusionCLT.Section8.Brownian.brownianMotion d x,
    (isContinuousPathLaw_iff (SuperdiffusionCLT.Section8.Brownian.heatSemigroup d) _).mpr
      (SuperdiffusionCLT.Section8.isContinuousPathLaw_brownianMotion d)⟩

theorem eq_brownianMotion {W : Vec d → Measure (ContinuousPath (Vec d))}
    (hW : IsContinuousPathLaw (heatKernel d) W) :
    W 0 = SuperdiffusionCLT.Section8.Brownian.brownianMotion d 0 :=
  eq_brownianMotion_of_isContinuousPathLaw d W
    ((isContinuousPathLaw_iff (SuperdiffusionCLT.Section8.Brownian.heatSemigroup d) W).mp hW) 0

end SuperdiffusionCLT.StatementAudit.TheoremA
