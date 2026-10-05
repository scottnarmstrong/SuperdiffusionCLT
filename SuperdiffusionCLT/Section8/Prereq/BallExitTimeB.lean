/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.BallExitTime
public import SuperdiffusionCLT.Section8.Prereq.ProcessConstructionC
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion

/-!
# The Laplace transform of the exit time, on paths of `ℝ^d`

Every continuous-path law `Q` of the kernel semigroup of the marginal-field resolvent, pushed into
the one-point compactification by the live embedding, is the canonical continuous process of the
compactified semigroup: both have the same finite-dimensional distributions.  The exit time of a
set `V` read on a path of `ℝ^d` is the exit time of the image `V` of the post-composed path, so
the one-point Laplace transform of `BallExitTime.lean` holds on paths of `ℝ^d` for every
continuous-path law.

* `ballExit_map_postcomp_eq_of_fdd`: path laws agree through an embedding when their
  finite-dimensional distributions do;
* `ballExit_map_pathPostcomp_eq`: the image of `Q x` in the compactification is the canonical
  continuous process;
* `ballExit_lintegral_exp_neg_exitTime`: `E^x[e^{-lam T_V}] = 1 - lam w x`;
* `ballExit_measure_exitTime_le_le`: `Q x {T_V ≤ t} ≤ e^{lam t} (1 - lam w x)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory ProbabilityTheory Set
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

section Generic

variable {α β : Type*} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] [MetricSpace β] [CompleteSpace β]
  [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β]

omit [CompleteSpace α] [SecondCountableTopology α] in
/-- **A path law is determined by its finite-dimensional distributions, through an embedding.**
If the finite-dimensional distributions of a law `Q` of paths of `α` read through the embedding
`e` are those of a law `κ` of paths of `β`, then the image of `Q` under post-composition with
`e` is `κ`. -/
theorem ballExit_map_postcomp_eq_of_fdd {e : α → β} (he : Topology.IsEmbedding e)
    (hme : MeasurableEmbedding e) {S : SubMarkovKernelSemigroup α}
    {P' : SubMarkovKernelSemigroup β} (hS : S.IsConservative) (hP' : P'.IsConservative)
    (hkern : ∀ t x, P' t (e x) = (S t x).map e) (x : α)
    (Q : Measure (ContinuousPath α)) [IsFiniteMeasure Q]
    (hQ : ∀ I : Finset ℝ≥0, Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel S I x)
    (κ : Measure (ContinuousPath β)) [IsFiniteMeasure κ]
    (hκ : ∀ I : Finset ℝ≥0, κ.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P' I (e x)) :
    Q.map (pathPostcomp (⟨e, he.continuous⟩ : C(α, β))) = κ := by
  have hpost : Measurable (pathPostcomp (⟨e, he.continuous⟩ : C(α, β))) :=
    (continuous_pathPostcomp (⟨e, he.continuous⟩ : C(α, β))).measurable
  have hfdd' : ∀ J : Finset ℝ≥0, (Q.map (pathPostcomp (⟨e, he.continuous⟩ : C(α, β)))).map
      (ContinuousPath.finsetEvaluation J) = κ.map (ContinuousPath.finsetEvaluation J) := by
    intro J
    have hEv : Measurable (ContinuousPath.finsetEvaluation (alpha := α) J) :=
      ContinuousPath.measurable_finsetEvaluation J
    have hEv' : Measurable (ContinuousPath.finsetEvaluation (alpha := β) J) :=
      ContinuousPath.measurable_finsetEvaluation J
    have hE : Measurable (fun f : J → α ↦ fun i ↦ e (f i)) :=
      measurable_pi_iff.mpr fun i ↦ hme.measurable.comp (measurable_pi_apply i)
    rw [hκ J, Measure.map_map hEv' hpost,
      procConstr_finiteSetKernel_apply_map hS hP' hme.measurable hkern J x, ← hQ J,
      Measure.map_map hE hEv]
    rfl
  have hk := Kernel.eq_of_map_denseFiniteEvaluation_eq
    (Kernel.const Unit (Q.map (pathPostcomp (⟨e, he.continuous⟩ : C(α, β)))))
    (Kernel.const Unit κ)
    (fun I ↦ by
      have hm : Measurable (ContinuousPath.finsetEvaluation (alpha := β)
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) :=
        measurable_pi_iff.mpr fun t ↦ ContinuousPath.measurable_coordinateProcess (t : ℝ≥0)
      rw [Kernel.map_const _ hm, Kernel.map_const _ hm]
      exact congrArg (Kernel.const Unit) (hfdd' _))
  simpa using DFunLike.congr_fun hk ()

end Generic

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k)

/-- **The path law read in the one-point compactification.**  Every continuous-path law of the
kernel semigroup of the marginal-field resolvent, pushed into the compactification, is the
canonical continuous process of the compactified semigroup. -/
theorem ballExit_map_pathPostcomp_eq
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q) (x : Vec d) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    (Q x).map (pathPostcomp (liveEmbedding (Vec d))) =
      IsConservative.continuousProcess
        D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (x : OnePoint (Vec d)) :=
  letI := D.logGrowthBounds.processInput.toOnePointRegular.metricSpace
  letI := D.logGrowthBounds.processInput.toOnePointRegular.completeSpace
  have hQ' := hQ x
  have : IsProbabilityMeasure (Q x) := hQ'.1
  ballExit_map_postcomp_eq_of_fdd (e := ((↑) : Vec d → OnePoint (Vec d)))
    OnePoint.isOpenEmbedding_coe.isEmbedding OnePoint.isOpenEmbedding_coe.measurableEmbedding
    D.logGrowthBounds.isConservative_kernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    (fun t y => procConstr_onePointKernelSemigroup_coe
      D.logGrowthBounds.isConservative_kernelSemigroup t y) x (Q x) hQ'.2 _
    (fun I => (Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I) _).symm.trans
      (congrArg (fun K => K (x : OnePoint (Vec d)))
        ((onePointProcess_spec D.logGrowthBounds.processInput.toOnePointRegular).2 I)))

/-- **The Laplace transform of the exit time, on paths of `ℝ^d`.**  For every continuous-path law
`Q` of the process of the marginal field, the Laplace transform of the exit time from a convex
domain `V` is `1 - lam w`, where `w` is the continuous representative of the part resolvent of
one. -/
theorem ballExit_lintegral_exp_neg_exitTime {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {w : Vec d → ℝ}
    (hw : Continuous w) (hoff : ∀ x, x ∉ V → w x = 0)
    (hrep : w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution D.analyticData.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        D.analyticData.hnu (partEllipticity D.analyticData hV) (ballExit_datumL2 hV)))
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    {x : Vec d} (hx : x ∈ V) :
    ∫⁻ path, ({path | ContinuousPath.exitTime V path < ⊤} : Set _).indicator
        (fun path => ENNReal.ofReal (Real.exp (-(lam : ℝ) *
          (ContinuousPath.exitTime V path).toReal))) path ∂(Q x) =
      ENNReal.ofReal (1 - (lam : ℝ) * w x) := by
  have hmap := ballExit_map_pathPostcomp_eq D hQ x
  have hone := ballExit_lintegral_exp_neg_exitTime_onePoint D hV lam hw hoff hrep hx
  let := D.logGrowthBounds.processInput.toOnePointRegular.metricSpace
  let := D.logGrowthBounds.processInput.toOnePointRegular.completeSpace
  have hemb : MeasurableEmbedding (pathPostcomp (liveEmbedding (Vec d))) :=
    (continuous_pathPostcomp (liveEmbedding (Vec d))).measurableEmbedding
      (procConstr_injective_pathPostcomp OnePoint.isOpenEmbedding_coe.isEmbedding)
  let G : ContinuousPath (OnePoint (Vec d)) → ℝ≥0∞ :=
    ({path | ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V) path < ⊤} :
      Set _).indicator (fun path => ENNReal.ofReal (Real.exp (-(lam : ℝ) *
        (ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V) path).toReal)))
  have hG : ∀ path : ContinuousPath (Vec d), G (pathPostcomp (liveEmbedding (Vec d)) path) =
      ({path | ContinuousPath.exitTime V path < ⊤} : Set _).indicator
        (fun path => ENNReal.ofReal (Real.exp (-(lam : ℝ) *
          (ContinuousPath.exitTime V path).toReal))) path := by
    intro path
    have hexit : ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V)
        (pathPostcomp (liveEmbedding (Vec d)) path) = ContinuousPath.exitTime V path :=
      exitTime_image_pathPostcomp (liveEmbedding (Vec d)) injective_liveCoe V path
    simp only [G, Set.indicator_apply, Set.mem_ofPred_eq, hexit]
  calc _ = ∫⁻ path, G (pathPostcomp (liveEmbedding (Vec d)) path) ∂(Q x) :=
        (lintegral_congr hG).symm
    _ = ∫⁻ path, G path ∂((Q x).map (pathPostcomp (liveEmbedding (Vec d)))) :=
        (hemb.lintegral_map G).symm
    _ = _ := (congrArg (fun m => ∫⁻ path, G path ∂m) hmap).trans hone

/-- **The early-exit probability on paths of `ℝ^d`.**  `Q x {T_V ≤ t} ≤ e^{lam t} (1 - lam w x)`. -/
theorem ballExit_measure_exitTime_le_le {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (lam : PositiveShift) {w : Vec d → ℝ}
    (hw : Continuous w) (hoff : ∀ x, x ∉ V → w x = 0)
    (hrep : w =ᵐ[volumeMeasureOn V] ZeroTraceSobolev.toL2
      (alphaShiftedSolution D.analyticData.a
        (show (0 : ℝ) < ((lam : PositiveShift) : ℝ) from lam.property)
        D.analyticData.hnu (partEllipticity D.analyticData hV) (ballExit_datumL2 hV)))
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    {x : Vec d} (hx : x ∈ V) (t : ℝ≥0) :
    Q x {path | ContinuousPath.exitTime V path ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp ((lam : ℝ) * (t : ℝ))) *
        ENNReal.ofReal (1 - (lam : ℝ) * w x) := by
  have hmap := ballExit_map_pathPostcomp_eq D hQ x
  have hone' := ballExit_lintegral_exp_neg_exitTime_onePoint D hV lam hw hoff hrep hx
  let := D.logGrowthBounds.processInput.toOnePointRegular.metricSpace
  let := D.logGrowthBounds.processInput.toOnePointRegular.completeSpace
  have hpost : Measurable (pathPostcomp (liveEmbedding (Vec d))) :=
    (continuous_pathPostcomp (liveEmbedding (Vec d))).measurable
  have hmeas : MeasurableSet {path : ContinuousPath (OnePoint (Vec d)) |
      ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V) path ≤ (t : ℝ≥0∞)} :=
    measurableSet_le (ContinuousPath.measurable_exitTime _
      (OnePoint.isOpen_image_coe.mpr hV.isOpen)) measurable_const
  have hpre : Q x {path | ContinuousPath.exitTime V path ≤ (t : ℝ≥0∞)} =
      ((Q x).map (pathPostcomp (liveEmbedding (Vec d)))) {path : ContinuousPath (OnePoint (Vec d)) |
        ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V) path ≤ (t : ℝ≥0∞)} := by
    rw [Measure.map_apply hpost hmeas]
    refine congrArg (Q x) ?_
    ext path
    have hexit : ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' V)
        (pathPostcomp (liveEmbedding (Vec d)) path) = ContinuousPath.exitTime V path :=
      exitTime_image_pathPostcomp (liveEmbedding (Vec d)) injective_liveCoe V path
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hexit]
  rw [hpre, hmap, ← hone']
  exact IsConservative.measure_exitTime_le_le
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup _
    (OnePoint.isOpen_image_coe.mpr hV.isOpen) (lam : ℝ) lam.property.le t _

end

end SuperdiffusionCLT.Section8
