/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.SampleMeasurabilityD
public import SuperdiffusionCLT.Section8.Prereq.SampleMeasurabilityC
public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputL
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationD
public import MarkovProcess.Killed.GluingLocal

/-!
# The quenched transition measures of the marginal process are measurable in the sample

For the constructed semigroups, the transition measure `ω ↦ (R ω).kernelSemigroup t x` is almost
everywhere measurable, because the resolvent values on nonnegative `C₀` functions are the real
parts of the analytic minimal resolvent (`KernelResolventIdentifiesAnalyticMinimal`), which is
measurable on any measurable set of samples where the field is continuous and skew
(`SampleMeasurabilityC.lean`), and a family of positive contractive resolvents with this property
has measurable transition measures (`SampleMeasurabilityD.lean`).

The semigroups are produced by `Classical.choice` on an almost sure event; the statements here are
about any family with the identification property.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess MarkovProcess.Semigroup
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.DivergenceForm
open scoped ZeroAtInfty ENNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The normalization of a function in `C₀` to sup norm at most one. -/
def sampleMeas_normalize (f : C₀(Vec d, ℝ)) : C₀(Vec d, ℝ) := (max 1 ‖f‖)⁻¹ • f

theorem sampleMeas_normalize_apply (f : C₀(Vec d, ℝ)) (y : Vec d) :
    sampleMeas_normalize f y = (max 1 ‖f‖)⁻¹ * f y := by
  simp only [sampleMeas_normalize, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]

theorem sampleMeas_normalize_nonneg (f : C₀(Vec d, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (y : Vec d) :
    0 ≤ sampleMeas_normalize f y := by
  rw [sampleMeas_normalize_apply]
  exact mul_nonneg (inv_nonneg.2 (le_max_of_le_left zero_le_one)) (hf0 y)

theorem sampleMeas_normalize_abs_le (f : C₀(Vec d, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (y : Vec d) :
    |sampleMeas_normalize f y| ≤ 1 := by
  have hcpos : 0 < max 1 ‖f‖ := lt_max_of_lt_left one_pos
  rw [abs_of_nonneg (sampleMeas_normalize_nonneg f hf0 y), sampleMeas_normalize_apply,
    inv_mul_le_iff₀ hcpos, mul_one]
  have : ‖f y‖ ≤ ‖f‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF y
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_right _ _))

/-- For a nonnegative `f ∈ C₀` the resolvent value is a multiple of the real part of the analytic
minimal resolvent of the normalized function, whenever the kernel resolvent is identified with
it. -/
theorem sampleMeas_operator_eq_minimal [NeZero d] {A : WholeSpaceAnalyticData d}
    {R : PositiveC0ContractiveResolvent (Vec d)}
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) (mu : PositiveShift)
    (f : C₀(Vec d, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (x : Vec d) :
    R.toContractiveResolvent.operator mu f x = max 1 ‖f‖ *
      (A.analyticMinimalResolvent mu (fun y => sampleMeas_normalize f y)
        (sampleMeas_normalize f).continuous.measurable (sampleMeas_normalize_abs_le f hf0) x).toReal := by
  set c : ℝ := max 1 ‖f‖ with hc
  have hcpos : 0 < c := lt_max_of_lt_left one_pos
  set g : C₀(Vec d, ℝ) := sampleMeas_normalize f with hg
  have hg0 := sampleMeas_normalize_nonneg f hf0
  have hg1 := sampleMeas_normalize_abs_le f hf0
  have h2 := PositiveC0ContractiveResolvent.kernelResolvent_ofReal_eq_operator R mu g hg0 x
  have h5 := hid mu (f := fun y => g y) g.continuous.measurable hg0 hg1 x
  have h6 : ENNReal.ofReal (R.toContractiveResolvent.operator mu g x) =
      A.analyticMinimalResolvent mu (fun y => g y) g.continuous.measurable hg1 x := h2.symm.trans h5
  have h3 : (R.toContractiveResolvent.operator mu g x) =
      (A.analyticMinimalResolvent mu (fun y => g y) g.continuous.measurable hg1 x).toReal := by
    rw [← h6, ENNReal.toReal_ofReal (R.isPositive mu g hg0 x)]
  have h4 : R.toContractiveResolvent.operator mu f x =
      c * R.toContractiveResolvent.operator mu g x := by
    have : f = c • g := by
      ext y
      simp only [hg, sampleMeas_normalize_apply, ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply,
        smul_eq_mul, hc]
      field_simp
    conv_lhs => rw [this]
    rw [map_smul]
    rfl
  rw [h4, h3]

/-- **H4, the quenched transition measures are measurable in the sample.**  For the constructed
semigroups, that is, for any family of positive contractive `C₀` resolvents identified, for almost
every sample, with the analytic minimal resolvent of `∇·(ν Id + k_ω)∇`, and for every time and
starting point, there is a finite kernel `κ` from the samples to `ℝ^d`, of total mass at most one,
which is almost surely the transition measure `(R ω).kernelSemigroup t x`.  Hence `ω ↦ (R ω).kernelSemigroup t x`
is almost everywhere measurable and so are all its integrals
(`sampleMeas_aemeasurable_integral`). -/
theorem sampleMeas_exists_kernel [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu)
    (A : ShellSeq d → WholeSpaceAnalyticData d)
    (R : ShellSeq d → PositiveC0ContractiveResolvent (Vec d))
    (hAR : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      (A omega).a = fullCoefficientRecentered nu omega ∧ (A omega).nu = nu ∧
        (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega))
    (t : NNReal) (x : Vec d) :
    ∃ κ : ProbabilityTheory.Kernel (ShellSeq d) (Vec d), ProbabilityTheory.IsFiniteKernel κ ∧
      (∀ omega, κ omega Set.univ ≤ 1) ∧
      ∀ᵐ omega ∂P.toMeasure, κ omega = (R omega).kernelSemigroup t x := by
  classical
  have hae : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      Continuous (fullStreamRecentered omega) ∧ (∀ y, matTranspose (fullStreamRecentered omega y) =
        -fullStreamRecentered omega y) ∧ ((A omega).a = fullCoefficientRecentered nu omega ∧
        (A omega).nu = nu ∧ (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega)) := by
    filter_upwards [ae_contDiff_fullStreamRecentered hJ3, hAR] with omega h1 h2
    exact ⟨h1.continuous, fieldInput_matTranspose_recentered omega, h2⟩
  obtain ⟨T, hsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  set G : Set (ShellSeq d) := Tᶜ with hG
  have hgood : ∀ omega ∈ G, Continuous (fullStreamRecentered omega) ∧
      (∀ y, matTranspose (fullStreamRecentered omega y) = -fullStreamRecentered omega y) ∧
      ((A omega).a = fullCoefficientRecentered nu omega ∧ (A omega).nu = nu ∧
        (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega)) := by
    intro omega hω
    by_contra hcon
    exact hω (hsub hcon)
  have hK : Measurable fun q : Vec d × ShellSeq d => fullStreamRecentered q.2 q.1 :=
    measurable_fullStreamRecentered_uncurry
  have hR' : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun omega : G => (R omega).toContractiveResolvent.operator mu f x := by
    intro mu f hf0 x
    have hmin := sampleMeas_measurable_minimalResolvent G hnu (fun omega => fullStreamRecentered omega)
      hK (fun omega hω => ⟨(hgood omega hω).1, (hgood omega hω).2.1⟩) A
      (fun omega hω => ⟨(hgood omega hω).2.2.1, (hgood omega hω).2.2.2.1⟩) mu
      (sampleMeas_normalize f).continuous.measurable (sampleMeas_normalize_abs_le f hf0) x
    have h1 := (measurable_const (a := max 1 ‖f‖)).mul hmin.ennreal_toReal
    have : (fun omega : G => (R omega).toContractiveResolvent.operator mu f x) =
        fun omega : G => max 1 ‖f‖ * ((A omega).analyticMinimalResolvent mu
          (fun y => sampleMeas_normalize f y) (sampleMeas_normalize f).continuous.measurable
          (sampleMeas_normalize_abs_le f hf0) x).toReal := by
      funext omega
      exact sampleMeas_operator_eq_minimal (hgood omega omega.2).2.2.2.2 mu f hf0 x
    rw [this]
    exact h1
  have hmeas := sampleMeas_measurable_kernelSemigroup (fun omega : G => R omega) hR' t x
  have hmG : MeasurableSet G := hTm.compl
  refine ⟨⟨fun omega => if h : omega ∈ G then (R omega).kernelSemigroup t x else 0,
    Measurable.dite hmeas measurable_const hmG⟩, ?_, ?_, ?_⟩
  · refine ⟨⟨1, ENNReal.one_lt_top, fun omega => ?_⟩⟩
    show (if h : omega ∈ G then (R omega).kernelSemigroup t x else 0) Set.univ ≤ 1
    by_cases hω : omega ∈ G
    · simpa only [hω, ↓reduceDIte] using
        ((R omega).kernelSemigroup.isSubMarkovKernel t).measure_le_one x Set.univ
    · simp [hω]
  · intro omega
    show (if h : omega ∈ G then (R omega).kernelSemigroup t x else 0) Set.univ ≤ 1
    by_cases hω : omega ∈ G
    · simpa only [hω, ↓reduceDIte] using
        ((R omega).kernelSemigroup.isSubMarkovKernel t).measure_le_one x Set.univ
    · simp [hω]
  · have : ∀ᵐ omega ∂P.toMeasure, omega ∈ G := by
      rw [ae_iff]
      simpa only [hG, Set.mem_compl_iff, Decidable.not_not, Set.ofPred_mem_eq] using hT0
    filter_upwards [this] with omega hω
    show (if h : omega ∈ G then (R omega).kernelSemigroup t x else 0) = _
    simp only [hω, ↓reduceDIte]

/-- The quenched transition measure is almost everywhere measurable in the sample. -/
theorem sampleMeas_aemeasurable_kernelSemigroup [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu)
    (A : ShellSeq d → WholeSpaceAnalyticData d)
    (R : ShellSeq d → PositiveC0ContractiveResolvent (Vec d))
    (hAR : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      (A omega).a = fullCoefficientRecentered nu omega ∧ (A omega).nu = nu ∧
        (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega))
    (t : NNReal) (x : Vec d) :
    AEMeasurable (fun omega => (R omega).kernelSemigroup t x) P.toMeasure := by
  obtain ⟨κ, _, _, hκ⟩ := sampleMeas_exists_kernel hJ3 hnu A R hAR t x
  exact κ.measurable.aemeasurable.congr (by filter_upwards [hκ] with omega h using h)

/-- The quenched Bochner integrals of a strongly measurable function are almost everywhere
measurable in the sample (for the real moment `‖y‖²` and for the vector mean `y`). -/
theorem sampleMeas_aemeasurable_integral [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu)
    (A : ShellSeq d → WholeSpaceAnalyticData d)
    (R : ShellSeq d → PositiveC0ContractiveResolvent (Vec d))
    (hAR : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      (A omega).a = fullCoefficientRecentered nu omega ∧ (A omega).nu = nu ∧
        (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega))
    (t : NNReal) (x : Vec d) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {φ : Vec d → E} (hφ : Measurable φ) :
    AEMeasurable (fun omega => ∫ y, φ y ∂((R omega).kernelSemigroup t x)) P.toMeasure := by
  obtain ⟨κ, hfin, _, hκ⟩ := sampleMeas_exists_kernel hJ3 hnu A R hAR t x
  have h := StronglyMeasurable.integral_kernel_prod_right (κ := κ)
    (f := fun (_ : ShellSeq d) (y : Vec d) => φ y) (hφ.comp measurable_snd).stronglyMeasurable
  exact h.measurable.aemeasurable.congr (by filter_upwards [hκ] with omega h; rw [h])

/-- **H4 for the constructed semigroup.**  There are families `A`, `R` such that, for almost every
sample, `A ω` is the analytic datum of `ν Id + k_ω - k_ω(0)`, `R ω` is the positive contractive
`C₀` resolvent identified with its analytic minimal resolvent, and the kernel semigroup
`(R ω).kernelSemigroup` satisfies the divergence-form specification; and, for every time and
starting point, the quenched transition measure is almost everywhere measurable in the sample. -/
theorem sampleMeas_constructed [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∃ (A : ShellSeq d → WholeSpaceAnalyticData d)
      (R : ShellSeq d → PositiveC0ContractiveResolvent (Vec d)),
      (∀ᵐ omega : ShellSeq d ∂P.toMeasure,
        (A omega).a = fullCoefficientRecentered nu omega ∧ (A omega).nu = nu ∧
          (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega) ∧
          IsDivergenceFormFeller (fullCoefficientRecentered nu omega) (R omega).kernelSemigroup) ∧
      ∀ (t : NNReal) (x : Vec d),
        AEMeasurable (fun omega => (R omega).kernelSemigroup t x) P.toMeasure := by
  classical
  set Q : ShellSeq d → WholeSpaceAnalyticData d → PositiveC0ContractiveResolvent (Vec d) → Prop :=
    fun omega A R => A.a = fullCoefficientRecentered nu omega ∧ A.nu = nu ∧
      R.kernelSemigroup.IsConservative ∧ A.KernelResolventIdentifiesAnalyticMinimal R with hQ
  have hex : ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∃ p : WholeSpaceAnalyticData d ×
      PositiveC0ContractiveResolvent (Vec d), Q omega p.1 p.2 := by
    filter_upwards [fieldInput_ae_processInput hPrefix hJ3 hnu] with omega hω
    obtain ⟨A, R, h1, h2, h3, h4, -⟩ := hω
    exact ⟨(A, R), h1, h2, h3, h4⟩
  obtain ⟨omega0, p0, hp0⟩ := hex.exists
  let pick : ShellSeq d → WholeSpaceAnalyticData d × PositiveC0ContractiveResolvent (Vec d) :=
    fun omega => if h : ∃ p : WholeSpaceAnalyticData d × PositiveC0ContractiveResolvent (Vec d),
      Q omega p.1 p.2 then h.choose else p0
  have hpick : ∀ᵐ omega : ShellSeq d ∂P.toMeasure, Q omega (pick omega).1 (pick omega).2 := by
    filter_upwards [hex] with omega h
    simp only [pick, h, ↓reduceDIte]
    exact h.choose_spec
  have hAR : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      (pick omega).1.a = fullCoefficientRecentered nu omega ∧ (pick omega).1.nu = nu ∧
        (pick omega).1.KernelResolventIdentifiesAnalyticMinimal (pick omega).2 := by
    filter_upwards [hpick] with omega h
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  refine ⟨fun omega => (pick omega).1, fun omega => (pick omega).2, ?_, fun t x =>
    sampleMeas_aemeasurable_kernelSemigroup hJ3 hnu _ _ hAR t x⟩
  filter_upwards [hpick, ae_contDiff_fullStreamRecentered hJ3] with omega h hreg
  refine ⟨h.1, h.2.1, h.2.2.2, ?_⟩
  rw [← h.1]
  exact domId_isDivergenceFormFeller (pick omega).1
    (fun i j => by rw [h.1]; exact domId_entries_contDiff hreg i j) h.2.2.2 h.2.2.1

/-! ## Satisfiability witnesses -/

/-- The hypotheses of the constructed-family statement are met by the law concentrated on the zero
shell sequence, where the field is the constant coefficient `ν Id`. -/
example [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∃ (A : ShellSeq d → WholeSpaceAnalyticData d)
      (R : ShellSeq d → PositiveC0ContractiveResolvent (Vec d)),
      (∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
        (A omega).a = fullCoefficientRecentered nu omega ∧ (A omega).nu = nu ∧
          (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega) ∧
          IsDivergenceFormFeller (fullCoefficientRecentered nu omega) (R omega).kernelSemigroup) ∧
      ∀ (t : NNReal) (x : Vec d),
        AEMeasurable (fun omega => (R omega).kernelSemigroup t x)
          (SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure :=
  sampleMeas_constructed
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end

end SuperdiffusionCLT.Section8
