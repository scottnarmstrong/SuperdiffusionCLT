/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.BrownianMotion
public import MarkovProcess.Trajectory.WeakConvergence

/-!
# Finite-dimensional convergence of Feller processes with moving starting points

Let `S n` and `S` be conservative Feller kernel semigroups on a locally compact Polish metric
space whose `C₀` semigroups converge strongly (that is, uniformly on `C₀`, for every time).  Let
`x n → x`.  Then the finite-dimensional distributions of the processes started at `x n` converge
weakly to those of the process of `S` started at `x`.  No moment hypothesis is used.

The processes are carried by arbitrary probability laws on continuous paths whose
finite-dimensional marginals are the finite-set kernels of the semigroups; no construction of a
path law is assumed or performed.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence

open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty CompactlySupported BoundedContinuousFunction

noncomputable section

variable {α : Type*} [MetricSpace α] [CompleteSpace α] [MeasurableSpace α]
  [BorelSpace α] [SecondCountableTopology α] [LocallyCompactSpace α]
variable {ι : Type*} {l : Filter ι}

omit [CompleteSpace α] in
/-- Compactly supported tests: the finite-set laws from moving starting points converge. -/
theorem sgConv_tendsto_integral_compactlySupported_finiteSetKernel
    {S : ι → SubMarkovKernelSemigroup α} {T : SubMarkovKernelSemigroup α}
    (hS : ∀ i, (S i).IsFellerKernelSemigroup) (hSc : ∀ i, (S i).IsConservative)
    (hT : T.IsFellerKernelSemigroup) (hTc : T.IsConservative)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun i ↦ (hS i).c0Semigroup t f) l (nhds (hT.c0Semigroup t f)))
    (I : Finset ℝ≥0) (g : C_c(I → α, ℝ)) {x : ι → α} {x₀ : α}
    (hx : Tendsto x l (nhds x₀)) :
    Tendsto (fun i ↦ ∫ path, g path ∂finiteSetKernel (S i) I (x i)) l
      (nhds (∫ path, g path ∂finiteSetKernel T I x₀)) := by
  have hunif := tendstoUniformly_integral_compactlySupported_finiteSetKernel hS hSc hT hTc
    hconv I g
  have hcont := (hT.continuous_integral_compactlySupported_finiteSetKernel hTc I g).tendsto x₀
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 := Metric.tendstoUniformly_iff.mp hunif (ε / 2) (half_pos hε)
  have h2 := Metric.tendsto_nhds.mp (hcont.comp hx) (ε / 2) (half_pos hε)
  filter_upwards [h1, h2] with i hi1 hi2
  have h3 := hi1 (x i)
  rw [Function.comp_apply] at hi2
  calc dist (∫ path, g path ∂finiteSetKernel (S i) I (x i))
        (∫ path, g path ∂finiteSetKernel T I x₀)
      ≤ dist (∫ path, g path ∂finiteSetKernel (S i) I (x i))
          (∫ path, g path ∂finiteSetKernel T I (x i)) +
        dist (∫ path, g path ∂finiteSetKernel T I (x i))
          (∫ path, g path ∂finiteSetKernel T I x₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        have h3' : dist (∫ path, g path ∂finiteSetKernel (S i) I (x i))
            (∫ path, g path ∂finiteSetKernel T I (x i)) < ε / 2 := by
          rw [dist_comm]; exact h3
        exact add_lt_add h3' hi2
    _ = ε := by ring

/-- **T1.**  Finite-dimensional distributions converge from moving starting points: for every
finite set of times and every bounded continuous test function on the product, the expectation
under the path law of `S i` from `x i` converges to that under the path law of `T` from `x₀`. -/
theorem sgConv_tendsto_integral_finsetEvaluation
    {S : ι → SubMarkovKernelSemigroup α} {T : SubMarkovKernelSemigroup α}
    (hS : ∀ i, (S i).IsFellerKernelSemigroup) (hSc : ∀ i, (S i).IsConservative)
    (hT : T.IsFellerKernelSemigroup) (hTc : T.IsConservative)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun i ↦ (hS i).c0Semigroup t f) l (nhds (hT.c0Semigroup t f)))
    {x : ι → α} {x₀ : α} (hx : Tendsto x l (nhds x₀))
    {Q : ι → Measure (ContinuousPath α)} {Q₀ : Measure (ContinuousPath α)}
    (hfdd : ∀ i (I : Finset ℝ≥0), (Q i).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (S i) I (x i))
    (hfdd₀ : ∀ I : Finset ℝ≥0, Q₀.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel T I x₀)
    (I : Finset ℝ≥0) (f : (I → α) →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ ω, f (ContinuousPath.finsetEvaluation I ω) ∂(Q i)) l
      (nhds (∫ ω, f (ContinuousPath.finsetEvaluation I ω) ∂Q₀)) := by
  have hmeas := ContinuousPath.measurable_finsetEvaluation (alpha := α) I
  have hrw : ∀ (μ : Measure (ContinuousPath α)) (ν : Measure (I → α)),
      μ.map (ContinuousPath.finsetEvaluation I) = ν →
      ∫ ω, f (ContinuousPath.finsetEvaluation I ω) ∂μ = ∫ p, f p ∂ν := by
    intro μ ν h
    rw [← h, integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
  simp only [hrw _ _ (hfdd _ I), hrw _ _ (hfdd₀ I)]
  have hprob : ∀ i, IsProbabilityMeasure (finiteSetKernel (S i) I (x i)) := fun i ↦ by
    have := (hSc i).isMarkovKernel_finiteSetKernel (S i) I
    infer_instance
  have hprob₀ : IsProbabilityMeasure (finiteSetKernel T I x₀) := by
    have := hTc.isMarkovKernel_finiteSetKernel T I
    infer_instance
  exact tendsto_integral_boundedContinuous_of_tendsto_compactlySupported
    (fun i ↦ finiteSetKernel (S i) I (x i)) (finiteSetKernel T I x₀)
    (fun g ↦ sgConv_tendsto_integral_compactlySupported_finiteSetKernel hS hSc hT hTc hconv
      I g hx) f

/-- Satisfiability of `sgConv_tendsto_integral_finsetEvaluation`: the constant sequence of heat
semigroups, started at a convergent sequence of points, with Brownian motion as the path law. -/
example (d : ℕ) {x : ℕ → Vec d} {x₀ : Vec d} (hx : Tendsto x atTop (nhds x₀))
    (I : Finset ℝ≥0) (f : (I → Vec d) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ ω, f (ContinuousPath.finsetEvaluation I ω)
        ∂(Brownian.brownianMotion d (x n))) atTop
      (nhds (∫ ω, f (ContinuousPath.finsetEvaluation I ω) ∂(Brownian.brownianMotion d x₀))) := by
  refine sgConv_tendsto_integral_finsetEvaluation (S := fun _ ↦ Brownian.heatSemigroup d)
    (T := Brownian.heatSemigroup d) (fun _ ↦ Brownian.isFellerKernelSemigroup_heatSemigroup d)
    (fun _ ↦ Brownian.isConservative_heatSemigroup d)
    (Brownian.isFellerKernelSemigroup_heatSemigroup d)
    (Brownian.isConservative_heatSemigroup d) (fun _ _ ↦ tendsto_const_nhds) hx
    (Q := fun n ↦ Brownian.brownianMotion d (x n)) (Q₀ := Brownian.brownianMotion d x₀)
    (fun n I ↦ ?_) (fun I ↦ ?_) I f
  · rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I),
      Brownian.brownianMotion_map_finsetEvaluation]
  · rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I),
      Brownian.brownianMotion_map_finsetEvaluation]

end

end SuperdiffusionCLT.Section8.Convergence
