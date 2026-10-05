/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Kernel.PositiveC0Resolvent
public import MarkovProcess.Kernel.PositiveC0OperatorKernel
public import MarkovProcess.Semigroup.Generation
public import Homogenization.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import MarkovProcess.Semigroup.YosidaApproximation

/-!
# Measurability in a parameter of the kernel semigroups of positive `C₀` resolvents

A parameterized family of positive contractive resolvents on `C₀(ℝ^d)` whose point values on every
nonnegative `C₀` function are measurable in the parameter has transition measures that are
measurable in the parameter.

* The values of the resolvents are jointly measurable in the parameter and the point
  (continuity in the point), and so are the sub-Markov kernels of the normalized resolvents
  `α R_α` (Riesz measures, with the measurability criterion of `MarkovProcess`).
* Iterates of `α R_α` are jointly measurable: integrate the previous iterate against the kernel.
* The bounded Yosida approximations are `e^{-tα} ∑ (tα)^k (α R_α)^k / k!`, a limit of
  measurable partial sums, and the generated semigroup is their limit as `α → ∞`.
* The transition measure is measurable because its integrals against compactly supported
  continuous functions are.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open MarkovProcess MarkovProcess.Semigroup MeasureTheory ProbabilityTheory Homogenization
open scoped ZeroAtInfty CompactlySupported

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem sampleMeas_measurable_operator_uncurry (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) (hf0 : ∀ y, 0 ≤ f y) :
    Measurable fun q : Ω × Vec d => (R q.1).toContractiveResolvent.operator mu f q.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : Vec d) (ω : Ω) => (R ω).toContractiveResolvent.operator mu f x)
    (fun ω => ((R ω).toContractiveResolvent.operator mu f).continuous) (hR mu f hf0)
  exact h.comp measurable_swap

theorem sampleMeas_c0_eq_sub (g : C_c(Vec d, ℝ)) :
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap g =
      PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap (g ⊔ 0) -
        PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap (-g ⊔ 0) := by
  ext x
  simp [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply]

theorem sampleMeas_isPositive_scaled (R : PositiveC0ContractiveResolvent (Vec d))
    (α : PositiveShift) :
    PositiveC0OperatorMeasure.IsPositive (R.toContractiveResolvent.scaledOperator α) :=
  fun _ hf x => R.preservesSet_scaledOperator_nonnegative α hf x

theorem sampleMeas_measurable_scaled_cc (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (α : PositiveShift) (g : C_c(Vec d, ℝ)) :
    Measurable fun q : Ω × Vec d => (R q.1).toContractiveResolvent.scaledOperator α
      (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap g) q.2 := by
  have hpos : ∀ h : C_c(Vec d, ℝ), (∀ y, 0 ≤ h y) → Measurable fun q : Ω × Vec d =>
      (R q.1).toContractiveResolvent.scaledOperator α
        (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap h) q.2 := by
    intro h hh
    have h1 := sampleMeas_measurable_operator_uncurry R hR α
      (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap h) (fun y => by
        simpa [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using hh y)
    exact h1.const_mul (α : ℝ)
  have e : ∀ q : Ω × Vec d, (R q.1).toContractiveResolvent.scaledOperator α
      (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap g) q.2 =
      (R q.1).toContractiveResolvent.scaledOperator α
        (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap (g ⊔ 0)) q.2 -
      (R q.1).toContractiveResolvent.scaledOperator α
        (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap (-g ⊔ 0)) q.2 := by
    intro q
    rw [sampleMeas_c0_eq_sub g, map_sub]
    rfl
  have hp1 := hpos (g ⊔ 0) (fun y => by simp)
  have hp2 := hpos (-g ⊔ 0) (fun y => by simp)
  rw [show (fun q : Ω × Vec d => (R q.1).toContractiveResolvent.scaledOperator α
      (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap g) q.2) = _ from funext e]
  exact hp1.sub hp2

/-- The sub-Markov kernel of the normalized resolvent `α R_α`, jointly measurable in the sample
and the starting point. -/
def sampleMeas_scaledKernel (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (α : PositiveShift) : Kernel (Ω × Vec d) (Vec d) := by
  letI : ∀ q : Ω × Vec d, IsFiniteMeasure (PositiveC0OperatorMeasure.measure
      ((R q.1).toContractiveResolvent.scaledOperator α) (sampleMeas_isPositive_scaled (R q.1) α)
      q.2) := fun q => PositiveC0OperatorMeasure.isFiniteMeasure_measure _ _
        ((R q.1).toContractiveResolvent.opNorm_scaledOperator_le_one α) q.2
  exact
    { toFun := fun q => PositiveC0OperatorMeasure.measure
        ((R q.1).toContractiveResolvent.scaledOperator α) (sampleMeas_isPositive_scaled (R q.1) α)
        q.2
      measurable' :=
        measurable_measure_of_measurable_integral_compactlySupported _ fun g => by
          have := sampleMeas_measurable_scaled_cc R hR α g
          convert this using 1
          funext q
          exact PositiveC0OperatorMeasure.integral_measure _ _ q.2 g }

theorem sampleMeas_scaledKernel_apply (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (α : PositiveShift) (q : Ω × Vec d) :
    sampleMeas_scaledKernel R hR α q = PositiveC0OperatorMeasure.measure
      ((R q.1).toContractiveResolvent.scaledOperator α) (sampleMeas_isPositive_scaled (R q.1) α)
      q.2 := rfl

theorem sampleMeas_scaledKernel_isFinite (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (α : PositiveShift) : IsFiniteKernel (sampleMeas_scaledKernel R hR α) := by
  have : IsSubMarkovKernel (sampleMeas_scaledKernel R hR α) := by
    intro q
    rw [sampleMeas_scaledKernel_apply]
    exact PositiveC0OperatorMeasure.measure_univ_le_one _ _
      ((R q.1).toContractiveResolvent.opNorm_scaledOperator_le_one α) q.2
  exact this.isFiniteKernel

theorem sampleMeas_integral_scaledKernel (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (α : PositiveShift) (q : Ω × Vec d) (f : C₀(Vec d, ℝ)) :
    ∫ y, f y ∂(sampleMeas_scaledKernel R hR α q) =
      (R q.1).toContractiveResolvent.scaledOperator α f q.2 := by
  rw [sampleMeas_scaledKernel_apply]
  exact PositiveC0OperatorKernel.integral_kernel
    ((R q.1).toContractiveResolvent.scaledOperator α) (sampleMeas_isPositive_scaled (R q.1) α)
    ((R q.1).toContractiveResolvent.opNorm_scaledOperator_le_one α) q.2 f

/-- Iterates of the normalized resolvent are jointly measurable in the sample and the point. -/
theorem sampleMeas_measurable_iterate (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (α : PositiveShift) (φ : C₀(Vec d, ℝ)) (k : ℕ) :
    Measurable fun q : Ω × Vec d =>
      (((fun g => (R q.1).toContractiveResolvent.scaledOperator α g)^[k]) φ) q.2 := by
  have := sampleMeas_scaledKernel_isFinite R hR α
  induction k with
  | zero => exact φ.continuous.measurable.comp measurable_snd
  | succ k ih =>
      have h1 : (fun q : Ω × Vec d =>
          (((fun g => (R q.1).toContractiveResolvent.scaledOperator α g)^[k + 1]) φ) q.2) =
          fun q => ∫ z, (((fun g => (R q.1).toContractiveResolvent.scaledOperator α g)^[k]) φ) z
            ∂(sampleMeas_scaledKernel R hR α q) := by
        funext q
        rw [Function.iterate_succ_apply',
          sampleMeas_integral_scaledKernel R hR α q]
      rw [h1]
      have h2 : Measurable (Function.uncurry fun (q : Ω × Vec d) (z : Vec d) =>
          (((fun g => (R q.1).toContractiveResolvent.scaledOperator α g)^[k]) φ) z) :=
        ih.comp (measurable_fst.fst.prodMk measurable_snd)
      exact (StronglyMeasurable.integral_kernel_prod_right (κ := sampleMeas_scaledKernel R hR α)
        h2.stronglyMeasurable).measurable

theorem sampleMeas_pow_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E →L[ℝ] E) (k : ℕ) (v : E) : (S ^ k) v = ((fun g => S g)^[k]) v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp, Function.iterate_succ_apply]
      exact ih (S v)

private noncomputable instance sampleMeasNormedAlgebraRatCLM {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)

/-- The exponential series of the Yosida approximation, under a bounded linear functional. -/
theorem sampleMeas_yosida_hasSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (R : ContractiveResolvent E) (α : PositiveShift) (t : NNReal) (φ : E)
    (Λ : E →L[ℝ] ℝ) :
    HasSum (fun k : ℕ => Real.exp (-((t : ℝ) * (α : ℝ))) *
      (((k.factorial : ℝ))⁻¹ * ((t : ℝ) * (α : ℝ)) ^ k *
        Λ (((fun g => R.scaledOperator α g)^[k]) φ)))
      (Λ (R.yosidaOperator α t φ)) := by
  set S := R.scaledOperator α with hS
  set a : ℝ := (t : ℝ) * (α : ℝ) with ha
  have hgen : ((t : ℝ) • R.yosidaGenerator α) = a • S + (algebraMap ℝ (E →L[ℝ] E) (-a)) := by
    ext f
    simp only [smul_apply, add_apply,
      sub_apply, ContinuousLinearMap.id_apply, ContractiveResolvent.yosidaGenerator,
      Algebra.algebraMap_eq_smul_one, one_apply_eq_self, ha, hS, smul_sub, smul_smul]
    module
  have hcomm : Commute (a • S) (algebraMap ℝ (E →L[ℝ] E) (-a)) :=
    (Algebra.commutes (-a) (a • S)).symm
  have hexp : R.yosidaOperator α t = NormedSpace.exp (a • S) *
      algebraMap ℝ (E →L[ℝ] E) (Real.exp (-a)) := by
    rw [ContractiveResolvent.yosidaOperator, hgen, NormedSpace.exp_add_of_commute hcomm,
      ← NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (-a), Real.exp_eq_exp_ℝ]
  have hsum := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • S)).mul_right
    (algebraMap ℝ (E →L[ℝ] E) (Real.exp (-a)))
  let L : (E →L[ℝ] E) →L[ℝ] ℝ := Λ.comp (ContinuousLinearMap.apply ℝ E φ)
  have hΛ := hsum.mapL L
  rw [← hexp] at hΛ
  have hfun : (fun k : ℕ => Real.exp (-((t : ℝ) * (α : ℝ))) *
      (((k.factorial : ℝ))⁻¹ * ((t : ℝ) * (α : ℝ)) ^ k *
        Λ (((fun g => R.scaledOperator α g)^[k]) φ))) =
      fun b : ℕ => L ((↑b.factorial : ℝ)⁻¹ • (a • S) ^ b *
        (algebraMap ℝ (E →L[ℝ] E)) (Real.exp (-a))) := by
    funext k
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      Algebra.algebraMap_eq_smul_one, smul_pow, smul_apply, mul_apply_eq_comp,
      one_apply_eq_self]
    have hpow : (S ^ k) (Real.exp (-a) • φ) =
        Real.exp (-a) • ((fun g => R.scaledOperator α g)^[k]) φ := by
      rw [map_smul, sampleMeas_pow_apply]
    rw [hpow]
    simp only [map_smul, smul_eq_mul, ha]
    ring
  rw [hfun]
  exact hΛ

theorem sampleMeas_measurable_yosida (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (α : PositiveShift) (t : NNReal) (φ : C₀(Vec d, ℝ)) (x : Vec d) :
    Measurable fun ω => ((R ω).toContractiveResolvent.yosidaOperator α t φ) x := by
  have hsum : ∀ ω, HasSum (fun k : ℕ => Real.exp (-((t : ℝ) * (α : ℝ))) *
      (((k.factorial : ℝ))⁻¹ * ((t : ℝ) * (α : ℝ)) ^ k *
        (c0EvalCLM x) (((fun g => (R ω).toContractiveResolvent.scaledOperator α g)^[k]) φ)))
      ((c0EvalCLM x) ((R ω).toContractiveResolvent.yosidaOperator α t φ)) := fun ω =>
    sampleMeas_yosida_hasSum (R ω).toContractiveResolvent α t φ (c0EvalCLM x)
  have hterm : ∀ k : ℕ, Measurable fun ω => Real.exp (-((t : ℝ) * (α : ℝ))) *
      (((k.factorial : ℝ))⁻¹ * ((t : ℝ) * (α : ℝ)) ^ k *
        (c0EvalCLM x) (((fun g => (R ω).toContractiveResolvent.scaledOperator α g)^[k]) φ)) := by
    intro k
    have h1 := (sampleMeas_measurable_iterate R hR α φ k).comp
      (measurable_id.prodMk (measurable_const (a := x)))
    exact (measurable_const.mul ((measurable_const.mul h1)))
  have hpart : ∀ n : ℕ, Measurable fun ω => ∑ k ∈ Finset.range n,
      Real.exp (-((t : ℝ) * (α : ℝ))) *
      (((k.factorial : ℝ))⁻¹ * ((t : ℝ) * (α : ℝ)) ^ k *
        (c0EvalCLM x) (((fun g => (R ω).toContractiveResolvent.scaledOperator α g)^[k]) φ)) :=
    fun n => Finset.measurable_sum _ fun k _ => hterm k
  exact measurable_of_tendsto_metrizable hpart (tendsto_pi_nhds.2 fun ω => (hsum ω).tendsto_sum_nat)

theorem sampleMeas_measurable_generated (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (t : NNReal) (φ : C₀(Vec d, ℝ)) (x : Vec d) :
    Measurable fun ω => ((R ω).toContractiveResolvent.generatedSemigroup t φ) x := by
  refine measurable_of_tendsto_metrizable
    (f := fun n ω => ((R ω).toContractiveResolvent.yosidaOperator (naturalShift n) t φ) x)
    (fun n => sampleMeas_measurable_yosida R hR (naturalShift n) t φ x) ?_
  rw [tendsto_pi_nhds]
  intro ω
  exact ((c0EvalCLM x).continuous.tendsto _).comp
    ((R ω).toContractiveResolvent.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t φ)

/-- **The kernel semigroup of a family of positive `C₀` resolvents is measurable in the
parameter.**  If, for every nonnegative `f ∈ C₀`, the values of the resolvents at each point are
measurable in the parameter, then the transition measures of the represented kernel semigroups
are measurable in the parameter. -/
theorem sampleMeas_measurable_kernelSemigroup (R : Ω → PositiveC0ContractiveResolvent (Vec d))
    (hR : ∀ (mu : PositiveShift) (f : C₀(Vec d, ℝ)), (∀ y, 0 ≤ f y) → ∀ x,
      Measurable fun ω => (R ω).toContractiveResolvent.operator mu f x)
    (t : NNReal) (x : Vec d) :
    Measurable fun ω => (R ω).kernelSemigroup t x := by
  have hfin : ∀ ω, IsFiniteMeasure ((R ω).kernelSemigroup t x) := fun ω => by
    have := ((R ω).kernelSemigroup.isSubMarkovKernel t).isFiniteKernel
    infer_instance
  have hreg : ∀ ω, ((R ω).kernelSemigroup t x).Regular := fun ω => by
    unfold PositiveC0ContractiveResolvent.kernelSemigroup
    rw [PositiveC0SemigroupKernel.kernelSemigroup_apply]
    exact PositiveC0OperatorMeasure.regular_measure _ _ x
  exact measurable_measure_of_measurable_integral_compactlySupported
    (fun ω => (R ω).kernelSemigroup t x) fun f => by
      have h := sampleMeas_measurable_generated R hR t
        (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f) x
      convert h using 1
      funext ω
      have := (R ω).integral_kernelSemigroup t
        (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f) x
      simpa only [PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply] using this

end

end SuperdiffusionCLT.Section8
