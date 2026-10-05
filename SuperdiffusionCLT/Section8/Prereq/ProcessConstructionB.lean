/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Parameterized.ContinuousProcessProperties
public import SuperdiffusionCLT.Section8.Prereq.ProcessConstruction

/-!
# Continuous-path laws read through a measurable embedding

Let `e : α → β` be a measurable embedding of metric spaces which is also a topological embedding,
let `P'` be a conservative kernel semigroup on `β` whose kernels at points `e x` are the images
under `e` of the kernels of a conservative semigroup `S` on `α`, and let `κ` be a Markov kernel
on continuous paths of `β` with the finite-dimensional distributions of `P'`.  If the path from
every `e x` almost surely never leaves the range of `e`, then the paths read back in `α`, through
the measurable inverse of the post-composition with `e`, form a continuous-path law of `S`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction
open scoped ENNReal NNReal

noncomputable section

section Generic

variable {α β : Type*}

/-- A measurable left inverse of a measurable embedding, applied coordinatewise, cancels the
coordinatewise image of laws. -/
theorem procConstr_map_coord_cancel [MeasurableSpace α] [MeasurableSpace β] {e : α → β}
    (hme : MeasurableEmbedding e) {ι : Type*} (a0 : α) (μ ν : Measure (ι → α))
    (h : μ.map (fun f : ι → α ↦ fun i ↦ e (f i)) =
      ν.map (fun f : ι → α ↦ fun i ↦ e (f i))) : μ = ν := by
  set g : β → α := Function.extend e id (fun _ ↦ a0) with hg
  have hgm : Measurable g := hme.measurable_extend measurable_id measurable_const
  have hge : ∀ a, g (e a) = a := fun a ↦ hme.injective.extend_apply _ _ _
  have hE : Measurable (fun f : ι → α ↦ fun i ↦ e (f i)) :=
    measurable_pi_iff.mpr fun i ↦ hme.measurable.comp (measurable_pi_apply i)
  have hG : Measurable (fun f : ι → β ↦ fun i ↦ g (f i)) :=
    measurable_pi_iff.mpr fun i ↦ hgm.comp (measurable_pi_apply i)
  have hcomp : (fun f : ι → β ↦ fun i ↦ g (f i)) ∘ (fun f : ι → α ↦ fun i ↦ e (f i)) = id := by
    funext f i
    exact hge (f i)
  have key : ∀ ρ : Measure (ι → α),
      (ρ.map (fun f : ι → α ↦ fun i ↦ e (f i))).map (fun f : ι → β ↦ fun i ↦ g (f i)) = ρ := by
    intro ρ
    rw [Measure.map_map hG hE, hcomp, Measure.map_id]
  rw [← key μ, ← key ν, h]

section Corestriction

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A path of `β` all of whose values lie in the range of a topological embedding is the
post-composition of a path of `α`. -/
theorem procConstr_exists_pathPostcomp_eq {e : α → β} (he : Topology.IsEmbedding e)
    (omega : ContinuousPath β) (hmem : ∀ t : ℝ≥0, omega t ∈ Set.range e) :
    ∃ w : ContinuousPath α, pathPostcomp ⟨e, he.continuous⟩ w = omega := by
  have hcont : Continuous fun t : ℝ≥0 ↦ (hmem t).choose := by
    refine he.continuous_iff.mpr ?_
    have hfun : (e ∘ fun t : ℝ≥0 ↦ (hmem t).choose) = fun t ↦ omega t := by
      funext t
      exact (hmem t).choose_spec
    rw [hfun]
    exact omega.continuous
  refine ⟨⟨fun t ↦ (hmem t).choose, hcont⟩, ?_⟩
  ext t
  exact (hmem t).choose_spec

/-- Post-composition with an injective map is injective on paths. -/
theorem procConstr_injective_pathPostcomp {e : α → β} (he : Topology.IsEmbedding e) :
    Function.Injective (pathPostcomp (⟨e, he.continuous⟩ : C(α, β))) := by
  intro a b h
  ext t
  exact he.injective (congrArg (fun w : ContinuousPath β ↦ w t) h)

end Corestriction

variable [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [MeasurableSpace α]
  [BorelSpace α] [MetricSpace β] [MeasurableSpace β] [BorelSpace β]

/-- **Reading the laws back through a measurable embedding.**  For every point `x`, the path law
`κ (e x)` almost surely stays in the range of `e`; then the image under the measurable inverse of
post-composition is a probability law on paths of `α` with the finite-dimensional distributions of
`S` started at `x`. -/
theorem procConstr_exists_pathLaw
    {e : α → β} (he : Topology.IsEmbedding e) (hme : MeasurableEmbedding e)
    {S : SubMarkovKernelSemigroup α} {P' : SubMarkovKernelSemigroup β}
    (hS : S.IsConservative) (hP' : P'.IsConservative)
    (hkern : ∀ t x, P' t (e x) = (S t x).map e)
    (κ : Kernel β (ContinuousPath β)) (hMarkov : IsMarkovKernel κ)
    (hκ : ∀ I : Finset ℝ≥0, κ.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P' I)
    (hlive : ∀ x, ∀ᵐ omega ∂κ (e x), ContinuousPath.exitTime (Set.range e) omega = ⊤) :
    ∃ Q : α → Measure (ContinuousPath α), ∀ x, IsProbabilityMeasure (Q x) ∧
      ∀ I : Finset ℝ≥0, (Q x).map (ContinuousPath.finsetEvaluation I) = finiteSetKernel S I x := by
  have := hMarkov
  set post : ContinuousPath α → ContinuousPath β := pathPostcomp (⟨e, he.continuous⟩ : C(α, β))
    with hpost
  have hinj : Function.Injective post := procConstr_injective_pathPostcomp he
  have hpe : MeasurableEmbedding post :=
    (continuous_pathPostcomp (⟨e, he.continuous⟩ : C(α, β))).measurableEmbedding hinj
  set r : α → ContinuousPath β → ContinuousPath α := fun x ↦
    Function.extend post id (fun _ ↦ ContinuousMap.const ℝ≥0 x) with hr
  have hrm : ∀ x, Measurable (r x) := fun x ↦
    hpe.measurable_extend measurable_id measurable_const
  have hrpost : ∀ x w, r x (post w) = w := fun x w ↦ hinj.extend_apply _ _ _
  refine ⟨fun x ↦ (κ (e x)).map (r x), fun x ↦ ?_⟩
  have hprob : IsProbabilityMeasure ((κ (e x)).map (r x)) :=
    inferInstance
  refine ⟨hprob, fun I ↦ ?_⟩
  have hEv : Measurable (ContinuousPath.finsetEvaluation (alpha := α) I) :=
    ContinuousPath.measurable_finsetEvaluation I
  have hEv' : Measurable (ContinuousPath.finsetEvaluation (alpha := β) I) :=
    ContinuousPath.measurable_finsetEvaluation I
  have hE : Measurable (fun f : I → α ↦ fun i ↦ e (f i)) :=
    measurable_pi_iff.mpr fun i ↦ hme.measurable.comp (measurable_pi_apply i)
  have hae : ContinuousPath.finsetEvaluation (alpha := β) I =ᵐ[κ (e x)]
      (fun f : I → α ↦ fun i ↦ e (f i)) ∘ ContinuousPath.finsetEvaluation (alpha := α) I ∘ r x := by
    filter_upwards [hlive x] with omega hom
    obtain ⟨w, hw⟩ := procConstr_exists_pathPostcomp_eq he omega
      ((ContinuousPath.exitTime_eq_top_iff _ omega).mp hom)
    have hw' : post w = omega := hw
    subst hw'
    rw [Function.comp_apply, Function.comp_apply, hrpost]
    rfl
  have h1 : (κ (e x)).map (ContinuousPath.finsetEvaluation (alpha := β) I) =
      (((κ (e x)).map (r x)).map (ContinuousPath.finsetEvaluation (alpha := α) I)).map
        (fun f : I → α ↦ fun i ↦ e (f i)) := by
    rw [Measure.map_map hE hEv, Measure.map_map (hE.comp hEv) (hrm x)]
    exact Measure.map_congr hae
  have h2 : finiteSetKernel P' I (e x) = (κ (e x)).map (ContinuousPath.finsetEvaluation I) := by
    rw [← Kernel.map_apply κ hEv' (e x), hκ I]
  refine procConstr_map_coord_cancel hme x _ _ ?_
  rw [← h1, ← h2]
  exact procConstr_finiteSetKernel_apply_map hS hP' hme.measurable hkern I x

end Generic

end

end SuperdiffusionCLT.Section8
