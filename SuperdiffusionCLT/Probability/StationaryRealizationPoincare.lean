/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.DifferenceQuotient
public import Homogenization.Sobolev.Foundations.H1Graph
public import Homogenization.Sobolev.Foundations.PoincareMeanZero
public import Homogenization.Sobolev.Foundations.CoerciveH1Translation
public import Homogenization.Sobolev.H1.Definitions
public import Homogenization.Sobolev.L2Ambient
public import SuperdiffusionCLT.Probability.StationaryProjection
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# The cube realization of a stationary potential field: the Poincaré layer

The statement `SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization`
asks, for a probability carrier `Ω` carrying a measure-preserving translation action of
`Vec d`, for a map `ω ↦ uReal ω` into the `H¹` functions on the cube
`openCubeSet (originCube d M)` whose weak gradient is the translate
`x ↦ gradHatW (x +ᵥ ω)` of a stationary square-integrable field, together with the interior
weak equation.  This module collects the part of the argument that is pure
`H¹`-on-an-open-bounded-convex-domain analysis, together with the transfer identity for a
jointly measurable action.

## Mean-zero closed range

The `L²` gradient map on mean-zero `H¹` functions on a bounded open convex domain has closed
range.  Poincaré–Wirtinger controls the mean-zero primitives by their gradients, so a
convergent sequence of gradients of mean-zero `H¹` functions converges to the gradient of a
mean-zero `H¹` function, because the graph of the weak gradient is closed.  This is
`exists_h1MeanZeroFunction_of_tendsto_gradToHilbertVectorL2`; the Poincaré constant makes the
primitives converge, so no test function is needed.

## Transfer identity

Joint measurability of the action makes the pushforward of `μ ⊗ ν` along the action equal to
`μ`, for every probability measure `ν` on `Vec d` (for instance the normalized cube measure or
a smooth bump density), hence `∫ ω, f ω ∂μ = ∫∫ f (x +ᵥ ω) ∂ν ∂μ` for every measurable `f`.
This is `map_vadd_prod_eq_of_measurableVAdd₂`, the abstract-carrier form of
`SuperdiffusionCLT.Section3.Terms.map_vadd_prod_eq`.  It makes the slice
`x ↦ g (x +ᵥ ω)` an `L²(U; ℝ)` element for almost every `ω` (`ae_memLp_slice`).

## Difference-quotient core

The converse of a difference-quotient estimate, passing from `L²(U)` convergence of backward
difference quotients of a sample to the weak partial derivative, rests on the whole-space
summation-by-parts identity
`integral_euclideanForwardDifferenceQuotient_mul_eq_neg_of_integrable`, in which smoothness of
the differentiated factor is replaced by integrability of the three products the expansion
needs, and on `integrable_mul_of_memLp_of_hasCompactSupport_subset`, which supplies one of
those three.
-/

@[expose] public section

open MeasureTheory Homogenization

open scoped ENNReal

namespace SuperdiffusionCLT.Probability.Stationary

noncomputable section

variable {d : ℕ}

/-! ## Mean-zero closed range of the gradient, via Poincaré

Every statement here is about the cube layer only: a bounded open convex domain `U`, the
mean-zero `H¹` functions on it, and their `L²` gradients. -/

section MeanZeroClosedRange

variable {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (Homogenization.volumeMeasureOn U)]

/-- The scalar `L²` realization of a difference of mean-zero `H¹` functions is the
difference of the realizations. -/
theorem toScalarL2_sub (u v : H1MeanZeroFunction U) :
    (u - v).toScalarL2 = u.toScalarL2 - v.toScalarL2 := by
  have hneg : (-v).toScalarL2 = -v.toScalarL2 := by
    have h := H1MeanZeroFunction.toScalarL2_smul (-1 : ℝ) v
    simpa using h
  rw [sub_eq_add_neg, H1MeanZeroFunction.toScalarL2_add, hneg, ← sub_eq_add_neg]

/-- The Hilbert-vector `L²` realization of a difference of mean-zero `H¹` functions is the
difference of the realizations. -/
theorem gradToHilbertVectorL2_sub (u v : H1MeanZeroFunction U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  have hneg : (-v).gradToHilbertVectorL2 = -v.gradToHilbertVectorL2 := by
    have h := H1MeanZeroFunction.gradToHilbertVectorL2_smul (-1 : ℝ) v
    simpa using h
  rw [sub_eq_add_neg, H1MeanZeroFunction.gradToHilbertVectorL2_add, hneg, ← sub_eq_add_neg]

/-- **The mean-zero `L²`-realization and its gradient are comparable.**  The Poincaré
inequality of a bounded open convex domain bounds the `L²` norm of a mean-zero `H¹`
function by a constant times the norm of its gradient realization. -/
theorem valueL2Norm_le_poincare_mul_gradToHilbertVectorL2
    (hU : IsOpenBoundedConvexDomain U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : H1MeanZeroFunction U,
      ‖u.toScalarL2‖ ≤ C * ‖u.gradToHilbertVectorL2‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    Homogenization.exists_poincare_constant_of_isOpenBoundedConvexDomain (U := U) hU
  refine ⟨C, hC0, fun u => ?_⟩
  calc ‖u.toScalarL2‖ = u.valueL2Norm := rfl
    _ ≤ C * u.gradientL2Norm := hC u
    _ = C * ‖u.gradToVectorL2‖ := rfl
    _ ≤ C * ‖u.gradToHilbertVectorL2‖ :=
      mul_le_mul_of_nonneg_left
        (Homogenization.H1Function.norm_gradToVectorL2_le_norm_gradToHilbertVectorL2
          (U := U) u.toH1Function) hC0

/-- **An `L²`-limit of gradients of mean-zero `H¹` functions is again a gradient of a
mean-zero `H¹` function.**  The primitives converge because Poincaré controls the `L²` norm of
a mean-zero function by its gradient, and then the closedness of the mean-zero weak-gradient graph
(`Homogenization.h1MeanZeroGraphClosedSubmodule`) turns the limit pair into an honest
witness.  No test function is ever tested against the limit, so the uncountable test class
of `Homogenization.H1WeakTestFunction` is never enumerated. -/
theorem exists_h1MeanZeroFunction_of_tendsto_gradToHilbertVectorL2
    (hU : IsOpenBoundedConvexDomain U)
    {ι : Type*} {l : Filter ι} [l.NeBot] {u : ι → H1MeanZeroFunction U}
    {g : HilbertVectorL2 U}
    (hgrad : Filter.Tendsto (fun n => (u n).gradToHilbertVectorL2) l (nhds g)) :
    ∃ ulim : H1MeanZeroFunction U, ulim.gradToHilbertVectorL2 = g := by
  obtain ⟨C, hC0, hC⟩ := valueL2Norm_le_poincare_mul_gradToHilbertVectorL2 (U := U) hU
  have hEst : ∀ n m : ι,
      ‖(u n).toScalarL2 - (u m).toScalarL2‖ ≤
        C * ‖(u n).gradToHilbertVectorL2 - (u m).gradToHilbertVectorL2‖ := by
    intro n m
    have h := hC (u n - u m)
    rw [toScalarL2_sub (u n) (u m), gradToHilbertVectorL2_sub (u n) (u m)] at h
    exact h
  have hCauchy : Cauchy (Filter.map (fun n => (u n).toScalarL2) l) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    set δ : ℝ := ε / (4 * (C + 1)) with hδdef
    have hCone : (0 : ℝ) < C + 1 := by linarith only [hC0]
    have hδpos : 0 < δ := by
      rw [hδdef]
      positivity
    have hball : {n : ι | dist ((u n).gradToHilbertVectorL2) g < δ} ∈ l := by
      exact hgrad (Metric.ball_mem_nhds g hδpos)
    refine ⟨(fun n => (u n).toScalarL2) '' {n : ι |
        dist ((u n).gradToHilbertVectorL2) g < δ}, Filter.image_mem_map hball, ?_⟩
    rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
    have hnm : dist ((u n).gradToHilbertVectorL2) ((u m).gradToHilbertVectorL2) < 2 * δ := by
      calc dist ((u n).gradToHilbertVectorL2) ((u m).gradToHilbertVectorL2)
          ≤ dist ((u n).gradToHilbertVectorL2) g + dist g ((u m).gradToHilbertVectorL2) :=
            dist_triangle _ _ _
        _ = dist ((u n).gradToHilbertVectorL2) g +
              dist ((u m).gradToHilbertVectorL2) g := by rw [dist_comm g]
        _ < δ + δ := add_lt_add hn hm
        _ = 2 * δ := by ring
    have hfinal : C * (2 * δ) < ε := by
      have hCratio : C / (2 * (C + 1)) < 1 := by
        rw [div_lt_one (by positivity : (0 : ℝ) < 2 * (C + 1))]
        linarith only [hC0]
      have hkey : C * (2 * δ) = ε * (C / (2 * (C + 1))) := by
        rw [hδdef]
        field_simp
        ring
      rw [hkey]
      calc ε * (C / (2 * (C + 1))) < ε * 1 := mul_lt_mul_of_pos_left hCratio hε
        _ = ε := mul_one ε
    have h1 : dist ((u n).toScalarL2) ((u m).toScalarL2) ≤
        C * dist ((u n).gradToHilbertVectorL2) ((u m).gradToHilbertVectorL2) := by
      simpa only [dist_eq_norm] using hEst n m
    have h2 : C * dist ((u n).gradToHilbertVectorL2) ((u m).gradToHilbertVectorL2) ≤
        C * (2 * δ) := mul_le_mul_of_nonneg_left (le_of_lt hnm) hC0
    linarith only [h1, h2, hfinal]
  obtain ⟨f, hf⟩ :=
    (cauchy_iff_exists_le_nhds (l := Filter.map (fun n => (u n).toScalarL2) l)).mp hCauchy
  have hval : Filter.Tendsto (fun n => (u n).toScalarL2) l (nhds f) := hf
  have hpair : Filter.Tendsto
      (fun n => ((u n).toScalarL2, (u n).gradToHilbertVectorL2)) l (nhds (f, g)) :=
    hval.prodMk_nhds hgrad
  have hmem : (f, g) ∈ Homogenization.h1MeanZeroGraphClosedSubmodule (U := U) :=
    (Homogenization.h1MeanZeroGraphClosedSubmodule (U := U)).isClosed.mem_of_tendsto hpair
      (Filter.Eventually.of_forall fun n =>
        Homogenization.h1MeanZero_pair_mem_h1MeanZeroGraphClosedSubmodule (U := U) (u n))
  obtain ⟨ulim, _, hgradLim⟩ :=
    (Homogenization.mem_h1MeanZeroGraphClosedSubmodule_iff_exists_h1MeanZeroFunction
      (U := U) (f, g)).mp hmem
  exact ⟨ulim, hgradLim⟩

end MeanZeroClosedRange

/-! ## The difference-quotient core

The two lemmas below are pure algebra and pure integrability; neither carries any hypothesis
about `H¹` functions, difference quotients or convergence.  They enter the passage from
`L²(U)` convergence of the backward coordinate difference quotients of a sample to the weak
`i`-th partial derivative as follows: the coordinate-shift change of variables
`Homogenization.integral_comp_euclideanCoordShift_mul_eq_integral_mul_comp_euclideanCoordShift_neg`
transfers the integrability of `u * φ` supplied by `integrable_mul_of_memLp_of_hasCompactSupport_subset`
to that of `(u ∘ shift) * φ` and of `u * (φ ∘ shift)` whenever the support of the test function
is thickened by less than its distance to `Uᶜ`; the identity
`integral_euclideanForwardDifferenceQuotient_mul_eq_neg_of_integrable` then gives
summation by parts on `U`; and the limit passages use Hölder for the quotient side and
dominated convergence for the test side. -/

section DifferenceQuotientCore

/-- **Whole-space finite-difference summation by parts, with smoothness of the first factor
replaced by integrability of exactly the three products the expansion into ordinary Lebesgue
integrals needs.**  This is the algebraic core of the converse difference-quotient step: the
CoarseGraining lemma
`Homogenization.integral_euclideanForwardDifferenceQuotient_mul_eq_neg_integral_mul_euclideanBackwardDifferenceQuotient`
proves the same identity under `ContDiff ℝ ⊤ u`, which is exactly the hypothesis that the
converse passage must not have.  The change of variables
`Homogenization.integral_comp_euclideanCoordShift_mul_eq_integral_mul_comp_euclideanCoordShift_neg`
used in the proof is unconditional, so only the three integrability hypotheses remain. -/
theorem integral_euclideanForwardDifferenceQuotient_mul_eq_neg_of_integrable
    {u v : Vec d → ℝ} (h : ℝ) (i : Fin d)
    (h1 : Integrable (fun x : Vec d => u (Homogenization.euclideanCoordShift h i x) * v x))
    (h2 : Integrable (fun x : Vec d => u x * v x))
    (h3 : Integrable (fun x : Vec d => u x * v (Homogenization.euclideanCoordShift (-h) i x))) :
    ∫ x, Homogenization.euclideanForwardDifferenceQuotient h i u x * v x
        ∂MeasureTheory.volume =
      -∫ x, u x * Homogenization.euclideanBackwardDifferenceQuotient h i v x
        ∂MeasureTheory.volume := by
  have hchange :=
    Homogenization.integral_comp_euclideanCoordShift_mul_eq_integral_mul_comp_euclideanCoordShift_neg
      h i u v
  have hpointLeft :
      (fun x : Vec d => Homogenization.euclideanForwardDifferenceQuotient h i u x * v x) =
        fun x : Vec d =>
          (u (Homogenization.euclideanCoordShift h i x) * v x - u x * v x) * h⁻¹ := by
    funext x
    simp [Homogenization.euclideanForwardDifferenceQuotient, div_eq_mul_inv]
    ring
  have hpointRight :
      (fun x : Vec d => u x * Homogenization.euclideanBackwardDifferenceQuotient h i v x) =
        fun x : Vec d =>
          (u x * v x - u x * v (Homogenization.euclideanCoordShift (-h) i x)) * h⁻¹ := by
    funext x
    simp [Homogenization.euclideanBackwardDifferenceQuotient, div_eq_mul_inv]
    ring
  calc
    ∫ x, Homogenization.euclideanForwardDifferenceQuotient h i u x * v x
          ∂MeasureTheory.volume
        = ∫ x, (u (Homogenization.euclideanCoordShift h i x) * v x - u x * v x) * h⁻¹
            ∂MeasureTheory.volume := by
          rw [hpointLeft]
    _ = (∫ x, u (Homogenization.euclideanCoordShift h i x) * v x - u x * v x
            ∂MeasureTheory.volume) * h⁻¹ := by
          rw [MeasureTheory.integral_mul_const]
    _ = ((∫ x, u (Homogenization.euclideanCoordShift h i x) * v x ∂MeasureTheory.volume) -
            (∫ x, u x * v x ∂MeasureTheory.volume)) * h⁻¹ := by
          rw [MeasureTheory.integral_sub h1 h2]
    _ = ((∫ x, u x * v (Homogenization.euclideanCoordShift (-h) i x) ∂MeasureTheory.volume) -
            (∫ x, u x * v x ∂MeasureTheory.volume)) * h⁻¹ := by
          rw [hchange]
    _ = -(((∫ x, u x * v x ∂MeasureTheory.volume) -
            (∫ x, u x * v (Homogenization.euclideanCoordShift (-h) i x)
              ∂MeasureTheory.volume)) * h⁻¹) := by
          ring
    _ = -((∫ x, u x * v x - u x * v (Homogenization.euclideanCoordShift (-h) i x)
            ∂MeasureTheory.volume) * h⁻¹) := by
          rw [MeasureTheory.integral_sub h2 h3]
    _ = -∫ x, (u x * v x - u x * v (Homogenization.euclideanCoordShift (-h) i x)) * h⁻¹
            ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_mul_const]
    _ = -∫ x, u x * Homogenization.euclideanBackwardDifferenceQuotient h i v x
            ∂MeasureTheory.volume := by
          rw [hpointRight]

/-- **An `L²(U)` field times a compactly supported continuous test function whose support lies
in `U` is integrable on all of `Vec d`.**  This is the first of the three integrability
hypotheses of `integral_euclideanForwardDifferenceQuotient_mul_eq_neg_of_integrable`; the other
two are its images under the coordinate-shift change of variables.  It carries no hypothesis on
difference quotients. -/
theorem integrable_mul_of_memLp_of_hasCompactSupport_subset {U : Set (Vec d)}
    {u : Vec d → ℝ} (hu : MemLp u 2 (MeasureTheory.volume.restrict U))
    {φ : Vec d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    Integrable (fun x : Vec d => u x * φ x) MeasureTheory.volume := by
  have hφ2 : MemLp φ 2 (MeasureTheory.volume.restrict (tsupport φ)) :=
    (hφ.memLp_of_hasCompactSupport hφc).restrict (tsupport φ)
  have hu2 : MemLp u 2 (MeasureTheory.volume.restrict (tsupport φ)) :=
    hu.mono_measure (Measure.restrict_mono hφU le_rfl)
  have hint : Integrable (u * φ) (MeasureTheory.volume.restrict (tsupport φ)) :=
    MemLp.integrable_mul hu2 hφ2
  have hzero : ∀ x ∈ (Set.univ : Set (Vec d)) \ tsupport φ, (u * φ) x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := hx.2
    simp [image_eq_zero_of_notMem_tsupport hx']
  have huniv := IntegrableOn.of_forall_sdiff_eq_zero (s := tsupport φ) (t := Set.univ)
    hint MeasurableSet.univ hzero
  rw [IntegrableOn, Measure.restrict_univ] at huniv
  exact huniv

end DifferenceQuotientCore

/-! ## The transfer identity at an abstract carrier

`map_vadd_prod_eq_of_measurableVAdd₂` is the abstract-carrier form of
`SuperdiffusionCLT.Section3.Terms.map_vadd_prod_eq`: it needs the action to be jointly
measurable, and its second factor may be *any* probability measure on `Vec d`.  The
consequences below are the ones the sample-wise argument consumes: the `ω`-slices of a
square-integrable field are square integrable for almost every `ω`, and the squared
norms of the slices integrate back to the squared norm of the field. -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
variable [AddAction (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Joint measurability of the action makes the action measurable as a map of the product. -/
theorem measurable_vadd_prod :
    Measurable (fun p : Ω × Vec d => p.2 +ᵥ p.1) := by
  have h := (measurable_vadd (M := Vec d) (α := Ω)).comp
    (measurable_swap (α := Ω) (β := Vec d))
  have hfun : (Function.uncurry (fun a : Vec d => fun b : Ω => a +ᵥ b)) ∘ Prod.swap =
      fun p : Ω × Vec d => p.2 +ᵥ p.1 := rfl
  rwa [hfun] at h

/-- The action is measurable in the translating vector alone. -/
theorem measurable_vadd_slice (ω : Ω) : Measurable (fun x : Vec d => x +ᵥ ω) := by
  have h := measurable_vadd_prod.comp
    ((measurable_const : Measurable (fun _ : Vec d => ω)).prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using h

/-- **Pushing the product of an invariant measure with any probability measure on `Vec d`
along the action returns the invariant measure.** -/
theorem map_vadd_prod_eq_of_measurableVAdd₂ (ν : Measure (Vec d)) [IsProbabilityMeasure ν] :
    (μ.prod ν).map (fun p : Ω × Vec d => p.2 +ᵥ p.1) = μ := by
  ext s hs
  rw [Measure.map_apply measurable_vadd_prod hs]
  have hs' : MeasurableSet ((fun p : Ω × Vec d => p.2 +ᵥ p.1) ⁻¹' s) :=
    hs.preimage measurable_vadd_prod
  rw [Measure.prod_apply_symm hs']
  have hinner : ∀ x : Vec d, μ ((fun ω : Ω => (ω, x)) ⁻¹'
      ((fun p : Ω × Vec d => p.2 +ᵥ p.1) ⁻¹' s)) = μ s := by
    intro x
    have hset : (fun ω : Ω => (ω, x)) ⁻¹'
        ((fun p : Ω × Vec d => p.2 +ᵥ p.1) ⁻¹' s) =
        (fun ω : Ω => x +ᵥ ω) ⁻¹' s := rfl
    rw [hset]
    exact VAddInvariantMeasure.measure_preimage_vadd x hs
  simp only [hinner, lintegral_const, measure_univ, mul_one]

/-- **The transfer identity for nonnegative a.e.-measurable functions.**  It is the
pushforward identity above read as an integral identity: the average over `Ω` of an
a.e.-measurable function is the average over `Ω × Vec d` of its translates. -/
theorem lintegral_vadd_prod_eq (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ p : Ω × Vec d, f (p.2 +ᵥ p.1) ∂(μ.prod ν) = ∫⁻ ω, f ω ∂μ := by
  have hmap : (μ.prod ν).map (fun p : Ω × Vec d => p.2 +ᵥ p.1) = μ :=
    map_vadd_prod_eq_of_measurableVAdd₂ (μ := μ) ν
  have hact : AEMeasurable (fun p : Ω × Vec d => p.2 +ᵥ p.1) (μ.prod ν) :=
    measurable_vadd_prod.aemeasurable
  have hf' : AEMeasurable f ((μ.prod ν).map (fun p : Ω × Vec d => p.2 +ᵥ p.1)) := by
    rw [hmap]
    exact hf
  rw [← MeasureTheory.lintegral_map' (μ := μ.prod ν)
    (g := fun p : Ω × Vec d => p.2 +ᵥ p.1) hf' hact, hmap]

/-- **The slices of a square-integrable field are square integrable for almost every
sample.**  This discharges the `L²` typing of the sample field `x ↦ g (x +ᵥ ω)` in the
conclusion: for almost every `ω` the slice of a `MemLp` field is `MemLp`.

Two hypotheses beyond `MemLp g 2 μ` are needed and are *not* removable.  `hgm : Measurable g`
is needed because the slice's a.e.-strong-measurability is not inherited from the mere
`AEStronglyMeasurable` that `MemLp` supplies: two functions that agree `μ`-a.e. can have
slices that differ on a *non-null* set of the translating variable, since `ν` is an arbitrary
probability measure on `Vec d` unrelated to `μ`.  `[SecondCountableTopology E]` is needed
because `Measurable.aestronglyMeasurable` needs it.  The transfer identity is what makes the
squared norms of the slices integrate back to the squared norm of the field, hence are finite
almost everywhere. -/
theorem ae_memLp_slice (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    {g : Ω → E} [SecondCountableTopology E] (hgm : Measurable g) (hg : MemLp g 2 μ) :
    ∀ᵐ ω ∂μ, MemLp (fun x : Vec d => g (x +ᵥ ω)) 2 ν := by
  have hpow : Measurable (fun a : ℝ≥0∞ => a ^ (2 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable
  have hF : AEMeasurable (fun p : Ω × Vec d => ‖g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ)) (μ.prod ν) := by
    have hmapact : (μ.prod ν).map (fun p : Ω × Vec d => p.2 +ᵥ p.1) = μ :=
      map_vadd_prod_eq_of_measurableVAdd₂ (μ := μ) ν
    have hga : AEMeasurable g ((μ.prod ν).map (fun p : Ω × Vec d => p.2 +ᵥ p.1)) := by
      rw [hmapact]
      exact hgm.aemeasurable
    exact hpow.comp_aemeasurable ((hga.comp_measurable measurable_vadd_prod).enorm)
  have hfin : ∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℝ) ∂μ ≠ ⊤ :=
    ne_of_lt (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
      (by norm_num) (by norm_num) hg.eLpNorm_lt_top)
  have hf_ae : AEMeasurable (fun ω : Ω => ‖g ω‖ₑ ^ (2 : ℝ)) μ :=
    hpow.comp_aemeasurable hgm.aemeasurable.enorm
  have hne : ∫⁻ ω, ∫⁻ x : Vec d, ‖g (x +ᵥ ω)‖ₑ ^ (2 : ℝ) ∂ν ∂μ ≠ ⊤ := by
    have h1 : ∫⁻ ω, ∫⁻ x : Vec d, ‖g (x +ᵥ ω)‖ₑ ^ (2 : ℝ) ∂ν ∂μ =
        ∫⁻ p : Ω × Vec d, ‖g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) :=
      (MeasureTheory.lintegral_prod
        (fun p : Ω × Vec d => ‖g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ)) hF).symm
    have h2 : ∫⁻ p : Ω × Vec d, ‖g (p.2 +ᵥ p.1)‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) =
        ∫⁻ ω, ‖g ω‖ₑ ^ (2 : ℝ) ∂μ :=
      lintegral_vadd_prod_eq (μ := μ) ν hf_ae
    rw [h1, h2]
    exact hfin
  have hae : ∀ᵐ ω ∂μ, ∫⁻ x : Vec d, ‖g (x +ᵥ ω)‖ₑ ^ (2 : ℝ) ∂ν < ⊤ :=
    MeasureTheory.ae_lt_top' hF.lintegral_prod_right' hne
  filter_upwards [hae] with ω hω
  have hmeas : AEStronglyMeasurable (fun x : Vec d => g (x +ᵥ ω)) ν :=
    (hgm.comp (measurable_vadd_slice ω)).aestronglyMeasurable
  rw [MeasureTheory.memLp_iff, MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2)
    (by norm_num) (by norm_num) hmeas]
  simpa only [ENNReal.toReal_ofNat] using hω

end Transfer

end

end SuperdiffusionCLT.Probability.Stationary
