/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.HeatWitnessB
public import SuperdiffusionCLT.Section8.Brownian.BrownianMotion
public import MarkovProcess.Parameterized.ContinuousProcessProperties

/-!
# Satisfiability of the carriers by the heat semigroup, and a negative control

* `isDivergenceFormFeller_heatSemigroup`: the heat semigroup is a conservative Feller semigroup
  whose generator is `∇·(½ Id ∇·) = ½ Δ` on every `C² ∩ C₀` function with Laplacian in `C₀`.
* `isContinuousPathLaw_brownianMotion`: Brownian motion is a continuous-path law of the heat
  semigroup.
* `not_isDivergenceFormFeller_heatSemigroup_one`: the specification discriminates; with
  coefficient `Id` in place of `½ Id` it fails for the heat semigroup in every positive dimension
  (equivalently, a Brownian motion of another variance does not satisfy the specification with
  coefficient `½ Id`).
-/

@[expose] public section

open scoped ContDiff ZeroAtInfty NNReal

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization MeasureTheory Topology

variable {d : ℕ}

/-- The standard Gaussian vector has no atom at the origin in positive dimension. -/
theorem heatWitness_stdGaussian_singleton (hd : 0 < d) : stdGaussian d {0} = 0 := by
  rw [stdGaussian, Measure.pi_singleton]
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd⟩)
    (ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp))

/-- Along `t → ∞`, the Gaussian averages of a `C₀` function tend to zero pointwise. -/
theorem heatWitness_tendsto_gaussianAverage (hd : 0 < d) (u : C₀(Vec d, ℝ)) (x : Vec d) :
    Tendsto (fun t : ℝ≥0 ↦ ∫ z, u (x + Real.sqrt t • z) ∂(stdGaussian d)) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := stdGaussian d)
    (l := (atTop : Filter ℝ≥0)) (F := fun (t : ℝ≥0) (z : Vec d) ↦ u (x + Real.sqrt t • z))
    (f := fun _ ↦ (0 : ℝ)) (bound := fun _ ↦ ‖u‖) ?_ ?_ ?_ ?_
  · simpa using h
  · exact Eventually.of_forall fun t ↦
      (u.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun t ↦ Eventually.of_forall fun z ↦ by
      simpa using norm_apply_le_norm_c0 u (x + Real.sqrt t • z)
  · exact integrable_const _
  · have hae : ∀ᵐ z ∂(stdGaussian d), z ≠ 0 := by
      rw [ae_iff]
      simpa using heatWitness_stdGaussian_singleton hd
    filter_upwards [hae] with z hz
    have hnorm : Tendsto (fun t : ℝ≥0 ↦ ‖x + Real.sqrt t • z‖) atTop atTop := by
      have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have h1 : Tendsto (fun t : ℝ≥0 ↦ Real.sqrt t * ‖z‖ - ‖x‖) atTop atTop := by
        refine tendsto_atTop_add_const_right _ _ ?_
        refine Tendsto.atTop_mul_const hz' ?_
        exact Real.tendsto_sqrt_atTop.comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)
      refine tendsto_atTop_mono (fun t ↦ ?_) h1
      calc Real.sqrt t * ‖z‖ - ‖x‖ = ‖Real.sqrt t • z‖ - ‖x‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ ‖x + Real.sqrt t • z‖ := by
            have := norm_sub_le_norm_add (Real.sqrt t • z) x
            rw [add_comm] at this
            linarith only [this]
    have hco : Tendsto (fun t : ℝ≥0 ↦ x + Real.sqrt t • z) atTop (cocompact (Vec d)) := by
      rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      exact hnorm
    exact u.zero_at_infty'.comp hco


/-- A nonzero smooth compactly supported `C₀` function. -/
theorem heatWitness_exists_bump (d : ℕ) :
    ∃ g : C₀(Vec d, ℝ), ContDiff ℝ ∞ (g : Vec d → ℝ) ∧ HasCompactSupport (g : Vec d → ℝ) ∧
      g 0 = 1 := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  have hcs : HasCompactSupport (b : Vec d → ℝ) := b.hasCompactSupport
  refine ⟨⟨⟨b, b.continuous⟩, hcs.is_zero_at_infty⟩, b.contDiff, hcs, ?_⟩
  exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)

/-- **Some function of the differentiable class of the heat generator has nonzero Laplacian**,
in every positive dimension: a function of the class with zero Laplacian lies in the kernel of
the generator, hence is invariant under the semigroup, hence vanishes by the decay of Gaussian
averages. -/
theorem heatWitness_exists_laplacian_ne {d : ℕ} (hd : 0 < d) :
    ∃ f : Convergence.heatCore d, Convergence.heatCoreLaplacian f ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨g, hg1, hgc, hg0⟩ := heatWitness_exists_bump d
  set mu : MarkovProcess.Semigroup.PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩ with hmu
  have hmu1 : (mu : ℝ) = 1 := rfl
  set S := Convergence.heatC0Semigroup d with hS
  set f : Convergence.heatCore d :=
    ⟨S.resolvent mu g, heatCore_resolvent_mem mu g hg1 hgc⟩ with hf
  set u : C₀(Vec d, ℝ) := (f : C₀(Vec d, ℝ)) with hu0
  have hdom : u ∈ S.generatorDomain := Convergence.mem_generatorDomain_heatCore f
  have hz : S.generator ⟨u, hdom⟩ = 0 := by
    have h : S.generator ⟨u, hdom⟩ = (2 : ℝ)⁻¹ • Convergence.heatCoreLaplacian f :=
      Convergence.generator_heatCore f
    rw [h, hall f, smul_zero]
  have hres : S.resolvent mu g = u := rfl
  have hug : u = g := by
    have h := S.generator_eq_of_resolvent_eq mu hdom hres
    rw [hz, hmu1] at h
    exact sub_eq_zero.mp (by simpa using h.symm)
  have horb : ∀ t : ℝ≥0, S t u = u := fun t ↦ by
    have h := S.operator_sub_eq_integral ⟨u, hdom⟩ t
    rw [hz] at h
    simp only [map_zero, intervalIntegral.integral_zero] at h
    exact sub_eq_zero.mp h
  have hx : ∀ t : ℝ≥0, ∫ z, u (0 + Real.sqrt t • z) ∂(stdGaussian d) = u 0 := fun t ↦ by
    have h := congrArg (fun w : C₀(Vec d, ℝ) ↦ w 0) (horb t)
    have h2 : S t u 0 = ∫ z, u (0 + Real.sqrt t • z) ∂(stdGaussian d) := by
      rw [hS, Convergence.heatC0Semigroup, c0Semigroup_heatSemigroup_apply, gaussianAverage_apply]
      exact integral_heatKernel_eq u.continuous t 0
    rw [← h2]
    exact h
  have hlim := heatWitness_tendsto_gaussianAverage hd u 0
  have hconst : Tendsto (fun t : ℝ≥0 ↦ ∫ z, u (0 + Real.sqrt t • z) ∂(stdGaussian d)) atTop
      (𝓝 (u 0)) := by
    simpa only [hx] using tendsto_const_nhds
  have hu00 : u 0 = 0 := tendsto_nhds_unique hconst hlim
  have : g 0 = 0 := by rw [← hug]; exact hu00
  rw [hg0] at this
  exact one_ne_zero this

section TimeChange

/-- **The heat semigroup run at twice the speed**: Brownian motion of variance `2 t` at time `t`,
whose generator is `Δ`. -/
noncomputable def heatWitness_twice (d : ℕ) : MarkovProcess.SubMarkovKernelSemigroup (Vec d) where
  kernel t := heatKernel d (2 * t)
  measurable_kernel := (heatSemigroup d).measurable_kernel.comp
    ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  kernel_zero := by simpa using heatKernel_zero d
  kernel_add s t := by
    rw [mul_add]
    exact (heatKernel_comp (2 * s) (2 * t)).symm
  isSubMarkovKernel _ := MarkovProcess.IsSubMarkovKernel.of_isMarkovKernel _

/-- The doubled-speed heat semigroup is Feller. -/
theorem heatWitness_twice_feller (d : ℕ) : (heatWitness_twice d).IsFellerKernelSemigroup := by
  have hC0 : (heatWitness_twice d).MapsC0 := fun t f ↦ mapsC0_heatSemigroup d (2 * t) f
  refine ⟨hC0, fun f ↦ ?_⟩
  have h := hasContinuousC0Orbits_heatSemigroup d f
  have h2 : Continuous fun t : ℝ≥0 ↦
      (heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) (2 * t) f :=
    h.comp (continuous_const.mul continuous_id)
  exact h2

/-- The `C₀` semigroup of the doubled-speed heat semigroup is the heat `C₀` semigroup at twice
the time. -/
theorem heatWitness_twice_c0Semigroup_apply (d : ℕ) (hF : (heatWitness_twice d).IsFellerKernelSemigroup)
    (t : ℝ≥0) (f : C₀(Vec d, ℝ)) :
    hF.c0Semigroup t f = (Convergence.heatC0Semigroup d) (2 * t) f :=
  ZeroAtInftyContinuousMap.ext fun _ ↦ rfl

end TimeChange

end SuperdiffusionCLT.Section8.Brownian

namespace SuperdiffusionCLT.Section8

open Filter Homogenization MeasureTheory MarkovProcess Topology
open SuperdiffusionCLT.Section8.Brownian

/-- **The heat semigroup satisfies the divergence-form specification with coefficient `½ Id`.**
It is conservative and Feller, and its generator is `½ Δ` on every `u ∈ C² ∩ C₀` with
`½ Δ u ∈ C₀`. -/
theorem isDivergenceFormFeller_heatSemigroup (d : ℕ) :
    IsDivergenceFormFeller (fun _ ↦ (1 / 2 : ℝ) • (1 : Mat d)) (heatSemigroup d) := by
  refine ⟨isConservative_heatSemigroup d, isFellerKernelSemigroup_heatSemigroup d,
    fun u v hu hv ↦ ?_⟩
  have hv' : ∀ x, v x = 2⁻¹ * vecLaplacian (⇑u) x := fun x ↦ by
    rw [hv x, heatWitness_divForm _ hu]
    norm_num
  have hres := heatWitness_resolvent_eq u v hu hv'
  set mu : MarkovProcess.Semigroup.PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩ with hmu
  have hdom : u ∈ (Convergence.heatC0Semigroup d).generatorDomain := by
    rw [← hres]
    exact (Convergence.heatC0Semigroup d).resolvent_mem_generatorDomain mu _
  refine ⟨hdom, ?_⟩
  have h := (Convergence.heatC0Semigroup d).generator_eq_of_resolvent_eq mu hdom hres
  refine h.trans ?_
  ext x
  have hmu1 : (mu : ℝ) = 1 := rfl
  simp [hmu1]

/-- **Brownian motion is a continuous-path law of the heat semigroup.** -/
theorem isContinuousPathLaw_brownianMotion (d : ℕ) :
    IsContinuousPathLaw (heatSemigroup d) (fun x ↦ brownianMotion d x) := by
  intro x
  refine ⟨inferInstance, fun I ↦ ?_⟩
  have h := (isFellerKernelSemigroup_heatSemigroup d).continuousProcess_map_finiteEvaluation
    (heatSemigroup d) (isConservative_heatSemigroup d) (kolmogorovRegular_heatSemigroup d) I
  have h2 := congrArg (fun κ : ProbabilityTheory.Kernel (Vec d) (I → Vec d) ↦ κ x) h
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)] at h2
  exact h2

/-- **Negative control: the specification discriminates the coefficient.**  In every positive
dimension the heat semigroup does not satisfy the divergence-form specification with the
coefficient `Id` in place of `½ Id`: its generator is `½ Δ`, not `Δ`. -/
theorem not_isDivergenceFormFeller_heatSemigroup_one {d : ℕ} (hd : 0 < d) :
    ¬ IsDivergenceFormFeller (fun _ ↦ (1 : ℝ) • (1 : Mat d)) (heatSemigroup d) := by
  rintro ⟨-, hF, hspec⟩
  obtain ⟨f, hf⟩ := heatWitness_exists_laplacian_ne hd
  set u : C₀(Vec d, ℝ) := (f : C₀(Vec d, ℝ)) with hu0
  set v : C₀(Vec d, ℝ) := Convergence.heatCoreLaplacian f with hv0
  have hv : ∀ x, v x = divForm 1 (fun _ ↦ (1 : ℝ) • (1 : Mat d)) (⇑u) x := fun x ↦ by
    rw [heatWitness_divForm _ f.2.1, one_mul]
    rfl
  obtain ⟨hdom, hgen⟩ := hspec u v f.2.1 hv
  have hgen' : (Convergence.heatC0Semigroup d).generator ⟨u, hdom⟩ = v := hgen
  have hgen2 : (Convergence.heatC0Semigroup d).generator ⟨u, hdom⟩ = (2 : ℝ)⁻¹ • v :=
    Convergence.generator_heatCore f
  apply hf
  ext x
  have h := congrArg (fun w : C₀(Vec d, ℝ) ↦ w x) (hgen'.symm.trans hgen2)
  simp only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul] at h
  have : v x = 0 := by linarith only [h]
  simpa using this

/-- **Negative control: Brownian motion of another variance.**  The heat semigroup run at twice
the speed (Brownian motion of variance `2 t`) is conservative and Feller but does not satisfy the
divergence-form specification with coefficient `½ Id`, in any positive dimension: its generator
is `Δ`, not `½ Δ`. -/
theorem not_isDivergenceFormFeller_heatWitness_twice {d : ℕ} (hd : 0 < d) :
    ¬ IsDivergenceFormFeller (fun _ ↦ (1 / 2 : ℝ) • (1 : Mat d)) (heatWitness_twice d) := by
  rintro ⟨-, hF, hspec⟩
  obtain ⟨f, hf⟩ := heatWitness_exists_laplacian_ne hd
  set u : C₀(Vec d, ℝ) := (f : C₀(Vec d, ℝ)) with hu0
  set L : C₀(Vec d, ℝ) := Convergence.heatCoreLaplacian f with hL0
  have hv : ∀ x, ((2 : ℝ)⁻¹ • L) x = divForm 1 (fun _ ↦ (1 / 2 : ℝ) • (1 : Mat d)) (⇑u) x :=
    fun x ↦ by
      rw [heatWitness_divForm _ f.2.1]
      simp [hL0, one_div]
  obtain ⟨hdom, hgen⟩ := hspec u _ f.2.1 hv
  have h1 := hF.c0Semigroup.tendsto_generator' ⟨u, hdom⟩
  have hdomH : u ∈ (Convergence.heatC0Semigroup d).generatorDomain :=
    Convergence.mem_generatorDomain_heatCore f
  have h2 : Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ • ((Convergence.heatC0Semigroup d) t u - u))
      (𝓝[>] 0) (𝓝 ((2 : ℝ)⁻¹ • L)) :=
    tendsto_differenceQuotient_heatSemigroup u L f.2.1 f.2.2 fun _ ↦ rfl
  have h3 : Tendsto (fun t : ℝ≥0 ↦ 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun t : ℝ≥0 ↦ 2 * t) (𝓝 0) (𝓝 (2 * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos two_pos (Set.mem_Ioi.mp ht)
  have h4 := (h2.comp h3).const_smul (2 : ℝ)
  have h5 : Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ • (hF.c0Semigroup t u - u)) (𝓝[>] 0)
      (𝓝 ((2 : ℝ) • (2 : ℝ)⁻¹ • L)) := by
    refine h4.congr fun t ↦ ?_
    simp only [Function.comp, heatWitness_twice_c0Semigroup_apply, NNReal.coe_mul,
      NNReal.coe_ofNat, mul_inv, smul_smul]
    congr 1
    ring
  have h6 := tendsto_nhds_unique h1 h5
  apply hf
  ext x
  have h := congrArg (fun w : C₀(Vec d, ℝ) ↦ w x) (h6.symm.trans hgen)
  simp only [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul] at h
  have : L x = 0 := by linarith only [h]
  simpa using this

end SuperdiffusionCLT.Section8
