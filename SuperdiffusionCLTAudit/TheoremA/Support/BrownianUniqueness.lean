module

public import SuperdiffusionCLT.Frozen.Section8.TheoremA

/-!
Brownian motion is the only continuous-path law of the heat semigroup, and the generator clause
of `IsDivergenceFormFeller` in difference-quotient form.
-/

@[expose] public section

namespace SuperdiffusionCLT.StatementAudit.TheoremA
open MeasureTheory ProbabilityTheory Homogenization MarkovProcess

/-- Brownian motion is the only continuous-path law of the heat semigroup. -/
theorem eq_brownianMotion_of_isContinuousPathLaw (d : ℕ)
    (W : Homogenization.Vec d → Measure (MarkovProcess.ContinuousPath (Homogenization.Vec d)))
    (hW : SuperdiffusionCLT.Section8.IsContinuousPathLaw
      (SuperdiffusionCLT.Section8.Brownian.heatSemigroup d) W) (x : Homogenization.Vec d) :
    W x = SuperdiffusionCLT.Section8.Brownian.brownianMotion d x := by
  have : IsProbabilityMeasure (W x) := (hW x).1
  have hker : (Kernel.const Unit (W x)) =
      Kernel.const Unit (SuperdiffusionCLT.Section8.Brownian.brownianMotion d x) := by
    refine Kernel.eq_of_map_denseFiniteEvaluation_eq _ _ ?_
    intro I
    ext y : 1
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
      Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _), Kernel.const_apply,
      Kernel.const_apply, (hW x).2,
      ← SuperdiffusionCLT.Section8.Brownian.brownianMotion_map_finsetEvaluation d,
      Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
  simpa using congrArg (fun k => k ()) hker

/-- The generator clause of `IsDivergenceFormFeller`, in difference-quotient form. -/
theorem generator_eq_iff_tendsto {d : ℕ}
    (S : MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d)) (hF : S.IsFellerKernelSemigroup)
    (u v : ZeroAtInftyContinuousMap (Homogenization.Vec d) ℝ) :
    (∃ hu : u ∈ hF.c0Semigroup.generatorDomain, hF.c0Semigroup.generator ⟨u, hu⟩ = v) ↔
      Filter.Tendsto
        (fun t : NNReal ↦ (t : ℝ)⁻¹ • (S.c0KernelIntegral hF.mapsC0 t u - u))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds v) := by
  constructor
  · rintro ⟨hu, h⟩
    have := hF.c0Semigroup.tendsto_generator' ⟨u, hu⟩
    rw [h] at this
    exact this
  · intro h
    refine ⟨hF.c0Semigroup.mem_generatorDomain_of_tendsto h, ?_⟩
    exact tendsto_nhds_unique (hF.c0Semigroup.tendsto_generator'
      ⟨u, hF.c0Semigroup.mem_generatorDomain_of_tendsto h⟩) h

end SuperdiffusionCLT.StatementAudit.TheoremA
