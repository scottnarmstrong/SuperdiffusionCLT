/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationC
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxUpperKernelBridge
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ResolventTail
public import MarkovProcess.Feller.Resolvent
public import SuperdiffusionCLT.Section8.Prereq.ProcessConstructionC
public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad
public import SuperdiffusionCLT.Section8.Prereq.HeatWitnessC

/-!
# The generator of the minimal semigroup contains `C² ∩ C₀`

For `A` with `C¹` coefficient and `R` a positive contractive `C₀` resolvent whose kernel
resolvent is the analytic minimal resolvent of `A`, every `u ∈ C² ∩ C₀` with
`divForm 1 A.a u ∈ C₀` satisfies `u = R_μ (μ u - divForm 1 A.a u)` for every `μ > 0`.  Hence `u`
lies in the domain of the generator of the Feller semigroup of `R` and the generator acts on it
as `divForm 1 A.a`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ZeroAtInfty Matrix.Norms.Elementwise
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem domId_mem_cube {m : ℕ} {x : Vec d} (hx : ‖x‖ < (3 : ℝ) ^ m) : x ∈ wholeSpaceCube d m := by
  rw [mem_wholeSpaceCube_iff]
  intro i
  have h : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  exact abs_lt.mp (lt_of_le_of_lt h hx)

/-- **Pointwise convergence of the cube resolvents.**  For `u ∈ C²` vanishing at infinity and
`g = μ u - divForm 1 a u` bounded, the zero-extended cube resolvents of `g` converge to `u`. -/
theorem domId_tendsto_cubeResolvent [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ A.a y i j) (mu : MarkovProcess.Semigroup.PositiveShift)
    {u g : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (hu0 : Tendsto u (cocompact (Vec d)) (𝓝 0))
    (hgm : Measurable g) {D : ℝ} (hgD : ∀ x, |g x| ≤ D)
    (hg : ∀ x, g x = (mu : ℝ) * u x - divForm 1 A.a u x) (x : Vec d) :
    Tendsto (fun m ↦ A.analyticCubeResolvent mu g hgm hgD m x) atTop (𝓝 (u x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev := hu0.eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
  rw [Filter.Eventually, mem_cocompact] at hev
  obtain ⟨K, hK, hKc⟩ := hev
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (max R ‖x‖) (by norm_num : (1 : ℝ) < 3)
  refine ⟨N, fun m hm ↦ ?_⟩
  have h3 : (3 : ℝ) ^ N ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hKU : K ⊆ wholeSpaceCube d m := fun y hy ↦ by
    have : ‖y‖ ≤ R := by simpa only [mem_closedBall_zero_iff] using hR hy
    exact domId_mem_cube (lt_of_le_of_lt this
      (lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN h3)))
  have hxU : x ∈ wholeSpaceCube d m :=
    domId_mem_cube (lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN h3))
  have hb := domId_cube_bound A ha mu hu hgm hgD hg m hK hKU (half_pos hε).le
    (fun y hy ↦ by
      have : u y ∈ Metric.ball (0 : ℝ) (ε / 2) := hKc hy
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at this
      exact this.le) x hxU
  rw [Real.dist_eq, abs_sub_comm]
  linarith only [hb, hε]

/-- **The analytic minimal resolvent of `μ u - divForm 1 a u` is `u`.** -/
theorem domId_analyticMinimalResolventReal_eq [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ A.a y i j) (mu : MarkovProcess.Semigroup.PositiveShift)
    {u g : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (hu0 : Tendsto u (cocompact (Vec d)) (𝓝 0))
    (hgm : Measurable g) {D : ℝ} (hgD : ∀ x, |g x| ≤ D)
    (hg : ∀ x, g x = (mu : ℝ) * u x - divForm 1 A.a u x) (x : Vec d) :
    A.analyticMinimalResolventReal mu g hgm hgD x = u x :=
  tendsto_nhds_unique (A.tendsto_analyticCubeResolvent_real mu hgm hgD x)
    (domId_tendsto_cubeResolvent A ha mu hu hu0 hgm hgD hg x)

theorem domId_abs_le_norm (f : C₀(Vec d, ℝ)) (x : Vec d) : |f x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

/-- The datum `μ u - v` of the resolvent equation, as an element of `C₀`. -/
theorem domId_resolvent_eq [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ A.a y i j) {R : MarkovProcess.PositiveC0ContractiveResolvent (Vec d)}
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (hF : R.kernelSemigroup.IsFellerKernelSemigroup)
    (mu : MarkovProcess.Semigroup.PositiveShift) (u v : C₀(Vec d, ℝ))
    (hu : ContDiff ℝ 2 (⇑u)) (hv : ∀ x, v x = divForm 1 A.a (⇑u) x) :
    hF.c0Semigroup.resolvent mu ((mu : ℝ) • u - v) = u := by
  ext x
  have hg : ∀ y, ((mu : ℝ) • u - v) y = (mu : ℝ) * u y - divForm 1 A.a (⇑u) y := fun y ↦ by
    rw [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, hv y]
  have h1 := MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.kernelResolventReal_eq_resolvent
    hF mu ((mu : ℝ) • u - v) x
  rw [← h1]
  have h2 := A.kernelResolventReal_eq_analyticMinimalResolventReal R hid mu
      (f := fun y ↦ ((mu : ℝ) • u - v) y) (((mu : ℝ) • u - v).continuous.measurable)
      (D := ‖(mu : ℝ) • u - v‖) (domId_abs_le_norm _) x
  rw [h2]
  exact domId_analyticMinimalResolventReal_eq A ha mu hu u.zero_at_infty'
    (((mu : ℝ) • u - v).continuous.measurable) (domId_abs_le_norm _) hg x

/-- **The generator clause for a `C¹` coefficient.**  Whichever Feller structure `hF` the kernel
semigroup of `R` carries, its generator contains every `u ∈ C² ∩ C₀` with
`divForm 1 A.a u ∈ C₀` and acts on it as `divForm 1 A.a`. -/
theorem domId_generator_clause [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ A.a y i j)
    {R : MarkovProcess.PositiveC0ContractiveResolvent (Vec d)}
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (hF : R.kernelSemigroup.IsFellerKernelSemigroup) (u v : C₀(Vec d, ℝ))
    (hu : ContDiff ℝ 2 (⇑u)) (hv : ∀ x, v x = divForm 1 A.a (⇑u) x) :
    ∃ hu' : u ∈ hF.c0Semigroup.generatorDomain, hF.c0Semigroup.generator ⟨u, hu'⟩ = v := by
  set mu : MarkovProcess.Semigroup.PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩ with hmu
  have hres := domId_resolvent_eq A ha hid hF mu u v hu hv
  have hdom : u ∈ hF.c0Semigroup.generatorDomain := by
    rw [← hres]
    exact hF.c0Semigroup.resolvent_mem_generatorDomain mu _
  refine ⟨hdom, ?_⟩
  have h := hF.c0Semigroup.generator_eq_of_resolvent_eq mu hdom hres
  refine h.trans ?_
  ext x
  have hmu1 : (mu : ℝ) = 1 := rfl
  simp [hmu1]

/-- **Resolvent form.**  For every `μ > 0`, `u = R_μ (μ u - v)`. -/
theorem domId_operator_eq [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ A.a y i j)
    {R : MarkovProcess.PositiveC0ContractiveResolvent (Vec d)}
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (mu : MarkovProcess.Semigroup.PositiveShift) (u v : C₀(Vec d, ℝ))
    (hu : ContDiff ℝ 2 (⇑u)) (hv : ∀ x, v x = divForm 1 A.a (⇑u) x) :
    R.toContractiveResolvent.operator mu ((mu : ℝ) • u - v) = u := by
  rw [← MarkovProcess.PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup R mu]
  exact domId_resolvent_eq A ha hid R.isFellerKernelSemigroup_kernelSemigroup mu u v hu hv

/-- **The divergence-form specification for the kernel semigroup of `R`.** -/
theorem domId_isDivergenceFormFeller [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ A.a y i j)
    {R : MarkovProcess.PositiveC0ContractiveResolvent (Vec d)}
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    (hcons : R.kernelSemigroup.IsConservative) :
    IsDivergenceFormFeller A.a R.kernelSemigroup :=
  ⟨hcons, R.isFellerKernelSemigroup_kernelSemigroup, fun u v hu hv ↦
    domId_generator_clause A ha hid _ u v hu hv⟩

/-- The recentred coefficient field is entrywise `C¹` once the recentred stream is. -/
theorem domId_entries_contDiff {nu : ℝ} {omega : ShellSeq d}
    (h : ContDiff ℝ 1 (fullStreamRecentered omega)) (i j : Fin d) :
    ContDiff ℝ 1 fun y ↦ fullCoefficientRecentered nu omega y i j := by
  have h1 : ContDiff ℝ 1 (fullCoefficientRecentered nu omega) := contDiff_const.add h
  exact contDiff_pi.1 (contDiff_pi.1 h1 i) j

/-- **Existence of the process of the marginal field.**  For almost every sample there is a
conservative Feller kernel semigroup `S` with a continuous-path law `Q` from every starting point,
whose generator is `∇·(ν Id + k - k(0))∇` on `C² ∩ C₀`. -/
theorem domId_ae_exists_process [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ (S : MarkovProcess.SubMarkovKernelSemigroup (Vec d))
        (Q : Vec d → Measure (MarkovProcess.ContinuousPath (Vec d))),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S ∧
          IsContinuousPathLaw S Q := by
  filter_upwards [procConstr_ae_exists_process hPrefix hJ3 hnu,
    ae_contDiff_fullStreamRecentered hJ3] with omega hω hreg
  obtain ⟨S, Q, -, hcons, hQ, A, R, hA, -, rfl, hid⟩ := hω
  refine ⟨R.kernelSemigroup, Q, ?_, hQ⟩
  rw [← hA]
  exact domId_isDivergenceFormFeller A
    (fun i j ↦ by rw [hA]; exact domId_entries_contDiff hreg i j) hid hcons

/-! ## Satisfiability witnesses -/

/-- The hypotheses on `(u, v)` are met by a nonzero pair for the constant coefficient `½ Id`:
`u` in the heat core, `v = ½ Δ u ≠ 0`.  The normalization `divForm 1 (c Id) = c Δ` agrees with the
generator `c Δ` of the analytic operator of `c Id`. -/
example {d : ℕ} (hd : 0 < d) :
    ∃ u v : C₀(Vec d, ℝ), ContDiff ℝ 2 (⇑u) ∧
      (∀ x, v x = divForm 1 (fun _ ↦ (1 / 2 : ℝ) • (1 : Mat d)) (⇑u) x) ∧ v ≠ 0 := by
  obtain ⟨f, hf⟩ := Brownian.heatWitness_exists_laplacian_ne hd
  refine ⟨(f : C₀(Vec d, ℝ)), (2 : ℝ)⁻¹ • Convergence.heatCoreLaplacian f, f.2.1,
    fun x ↦ ?_, fun h ↦ hf ?_⟩
  · rw [Brownian.heatWitness_divForm _ f.2.1]
    simp [one_div]
  · have h2 := congrArg (fun w : C₀(Vec d, ℝ) ↦ (2 : ℝ) • w) h
    simpa using h2

/-- The generator statement holds for the law concentrated on the zero shell sequence, where the
field is the constant coefficient `ν Id`. -/
example [NeZero d] (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ (S : MarkovProcess.SubMarkovKernelSemigroup (Vec d))
        (Q : Vec d → Measure (MarkovProcess.ContinuousPath (Vec d))),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S ∧
          IsContinuousPathLaw S Q :=
  domId_ae_exists_process
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

end SuperdiffusionCLT.Section8
