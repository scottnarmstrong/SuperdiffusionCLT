/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Independence.Integration
public import SuperdiffusionCLT.Probability.StationaryProjectionConditional

/-!
# Independent blocks and the stationary potential projection

Stationary potential fields have mean zero, and the stationary potential
projection of a field measurable with respect to a translation-invariant
sub-sigma-field is measurable with respect to the same sub-sigma-field. Together
these two facts make the responses of independent blocks orthogonal, so that the
response energy of a sum of independent blocks is the sum of the block energies.

## Main results

* `scalarMeanL2`: the mean of a scalar square-integrable variable, as a
  continuous linear functional on `ScalarL2 μ` for a finite measure.
* `integral_eq_zero_of_mem_stationaryPotentialSubspace`: every stationary
  potential field is centred.
* `inner_eq_zero_of_indep_of_integral_eq_zero`: two square-integrable vector
  fields measurable with respect to independent sub-sigma-fields, one of them
  centred, are orthogonal in `L²`.
* `inner_stationaryPotentialProjection_eq_zero_of_indep`: the stationary
  potential responses of two independent blocks are orthogonal.
* `norm_stationaryPotentialProjection_sum_sq`: the response energy of a sum of
  independent blocks is the sum of the block response energies.
-/

@[expose] public section

open MeasureTheory
open Homogenization

namespace SuperdiffusionCLT.Probability.Stationary

noncomputable section

/-! ## A finite orthogonal family -/

section OrthogonalFamily

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem norm_sum_sq_of_pairwise_inner_eq_zero {ι : Type*} (s : Finset ι) (v : ι → H)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · exact fun j hj hji ↦ h i hi j hj (Ne.symm hji)
  · exact fun hni ↦ absurd hi hni

end OrthogonalFamily

variable {d : ℕ} {Ω : Type*} {m₁ m₂ : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}

/-! ## The mean as a continuous linear functional -/

section Mean

variable [IsFiniteMeasure μ]

/-- The mean of a scalar square-integrable variable, presented as a continuous
linear functional: the `L²` inner product against the constant function `1`. -/
def scalarMeanL2 : ScalarL2 μ →L[ℝ] ℝ := innerSL ℝ (Lp.const 2 μ (1 : ℝ))

theorem scalarMeanL2_apply (g : ScalarL2 μ) : scalarMeanL2 g = ∫ ω, g ω ∂μ := by
  have h := L2.inner_indicatorConstLp_one (𝕜 := ℝ) (μ := μ) (s := Set.univ)
    MeasurableSet.univ (measure_ne_top μ Set.univ) g
  rw [indicatorConstLp_univ, Measure.restrict_univ] at h
  exact h

end Mean

/-! ## Independent centred fields are orthogonal -/

section GenericIndependence

variable [IsProbabilityMeasure μ]

/-- Two square-integrable vector fields measurable with respect to independent
sub-sigma-fields are orthogonal in `L²` as soon as one of them is centred. -/
theorem inner_eq_zero_of_indep_of_integral_eq_zero
    (hindep : ProbabilityTheory.Indep m₁ m₂ μ) {G₁ G₂ : VectorL2 d μ}
    (hG₁ : AEStronglyMeasurable[m₁] (G₁ : Ω → HilbertVec d) μ)
    (hG₂ : AEStronglyMeasurable[m₂] (G₂ : Ω → HilbertVec d) μ)
    (hz₁ : ∫ ω, (G₁ : Ω → HilbertVec d) ω ∂μ = 0) :
    inner ℝ G₁ G₂ = 0 := by
  classical
  obtain ⟨g₁, hg₁m, hg₁ae⟩ := hG₁
  obtain ⟨g₂, hg₂m, hg₂ae⟩ := hG₂
  have hcoord₁ : ∀ i : Fin d, Measurable[m₁] fun ω ↦ g₁ ω i := fun i ↦
    ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d ↦ ℝ) i).continuous.comp_stronglyMeasurable
      hg₁m).measurable
  have hcoord₂ : ∀ i : Fin d, Measurable[m₂] fun ω ↦ g₂ ω i := fun i ↦
    ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d ↦ ℝ) i).continuous.comp_stronglyMeasurable
      hg₂m).measurable
  have hindepFun : ∀ i : Fin d,
      ProbabilityTheory.IndepFun (fun ω ↦ g₁ ω i) (fun ω ↦ g₂ ω i) μ := by
    intro i
    refine (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mpr ?_
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hindep (hcoord₁ i).comap_le)
      (hcoord₂ i).comap_le
  have hint₁ : ∀ i : Fin d, Integrable (fun ω ↦ (G₁ : Ω → HilbertVec d) ω i) μ := fun i ↦
    memLp_one_iff_integrable.1 (((Lp.memLp G₁).eval_piLp i).mono_exponent one_le_two)
  have hcae₁ : ∀ i : Fin d,
      (fun ω ↦ (G₁ : Ω → HilbertVec d) ω i) =ᵐ[μ] fun ω ↦ g₁ ω i := by
    intro i
    filter_upwards [hg₁ae] with ω hω
    rw [hω]
  have hcae₂ : ∀ i : Fin d,
      (fun ω ↦ (G₂ : Ω → HilbertVec d) ω i) =ᵐ[μ] fun ω ↦ g₂ ω i := by
    intro i
    filter_upwards [hg₂ae] with ω hω
    rw [hω]
  have hLp₁ : ∀ i : Fin d, MemLp (fun ω ↦ g₁ ω i) 2 μ := fun i ↦
    ((Lp.memLp G₁).eval_piLp i).ae_eq (hcae₁ i)
  have hLp₂ : ∀ i : Fin d, MemLp (fun ω ↦ g₂ ω i) 2 μ := fun i ↦
    ((Lp.memLp G₂).eval_piLp i).ae_eq (hcae₂ i)
  have hmean₁ : ∀ i : Fin d, ∫ ω, g₁ ω i ∂μ = 0 := by
    intro i
    rw [← integral_congr_ae (hcae₁ i), ← eval_integral_piLp hint₁ i, hz₁]
    rfl
  rw [L2.inner_def]
  have hstep : ∫ ω, (inner ℝ ((G₁ : Ω → HilbertVec d) ω)
        ((G₂ : Ω → HilbertVec d) ω)) ∂μ
      = ∫ ω, ∑ i : Fin d, g₁ ω i * g₂ ω i ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg₁ae, hg₂ae] with ω h1 h2
    rw [h1, h2, PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [RCLike.inner_apply, mul_comm]
  have hprod : ∀ i : Fin d, Integrable (fun ω ↦ g₁ ω i * g₂ ω i) μ := fun i ↦
    (hLp₁ i).integrable_mul (hLp₂ i)
  rw [hstep, integral_finsetSum _ fun i _ ↦ hprod i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [(hindepFun i).integral_fun_mul_eq_mul_integral (hLp₁ i).aestronglyMeasurable
    (hLp₂ i).aestronglyMeasurable]
  rw [hmean₁ i, zero_mul]

end GenericIndependence

variable [AddAction (Vec d) Ω]
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-! ## Stationary potential fields are centred -/

section MeanZero

variable [IsFiniteMeasure μ]

/-- The mean is translation invariant. -/
theorem scalarMeanL2_koopman (x : Vec d) (g : ScalarL2 μ) :
    scalarMeanL2 (koopman (μ := μ) x g) = scalarMeanL2 g := by
  have hmp := measurePreserving_const_vadd (μ := μ) (Ω := Ω) x
  rw [scalarMeanL2_apply, scalarMeanL2_apply]
  have h1 : ∫ ω, (koopman (μ := μ) x g) ω ∂μ = ∫ ω, (g : Ω → ℝ) (x +ᵥ ω) ∂μ :=
    integral_congr_ae (Lp.coeFn_compMeasurePreserving g hmp)
  have h2 : ∫ ω, (g : Ω → ℝ) (x +ᵥ ω) ∂μ =
      ∫ y, (g : Ω → ℝ) y ∂(Measure.map (fun ω : Ω ↦ x +ᵥ ω) μ) := by
    refine (integral_map hmp.measurable.aemeasurable ?_).symm
    rw [hmp.map_eq]
    exact Lp.aestronglyMeasurable g
  rw [h1, h2, hmp.map_eq]

/-- Every coordinate of a horizontal gradient is centred: the mean of a Koopman
orbit is constant, so its derivative vanishes. -/
theorem scalarMeanL2_vectorL2Coord_of_hasHorizontalGradient {φ : ScalarL2 μ}
    {F : VectorL2 d μ} (h : HasHorizontalGradient (μ := μ) φ F) (i : Fin d) :
    scalarMeanL2 (vectorL2Coord (μ := μ) i F) = 0 := by
  have hd : HasDerivAt ((scalarMeanL2 (μ := μ)) ∘
      fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ)
      (scalarMeanL2 (vectorL2Coord (μ := μ) i F)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (ContinuousLinearMap.hasFDerivAt (scalarMeanL2 (μ := μ))) (h i)
  have hconst : ((scalarMeanL2 (μ := μ)) ∘
      fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ) =
      fun _ : ℝ ↦ scalarMeanL2 (μ := μ) φ := by
    funext t
    exact scalarMeanL2_koopman _ φ
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (scalarMeanL2 (μ := μ) φ))

/-- Every coordinate of a stationary potential field is centred. The set where a
fixed coordinate mean vanishes is the kernel of a continuous linear functional,
hence closed, so the statement passes from the horizontal gradients to their
closure. -/
theorem scalarMeanL2_vectorL2Coord_of_mem_stationaryPotentialSubspace
    {F : VectorL2 d μ} (hF : F ∈ stationaryPotentialSubspace (μ := μ) (d := d))
    (i : Fin d) : scalarMeanL2 (vectorL2Coord (μ := μ) i F) = 0 := by
  have hle : stationaryPotentialSubspace (μ := μ) (d := d) ≤
      LinearMap.ker ((scalarMeanL2 (μ := μ)).comp (vectorL2Coord (μ := μ) i)).toLinearMap := by
    refine (horizontalGradientRange (μ := μ) (d := d)).topologicalClosure_minimal ?_
      (ContinuousLinearMap.isClosed_ker _)
    rintro G ⟨φ, hφ⟩
    exact scalarMeanL2_vectorL2Coord_of_hasHorizontalGradient hφ i
  exact hle hF

/-- **Stationary potential fields have mean zero.** -/
theorem integral_eq_zero_of_mem_stationaryPotentialSubspace {F : VectorL2 d μ}
    (hF : F ∈ stationaryPotentialSubspace (μ := μ) (d := d)) :
    ∫ ω, (F : Ω → HilbertVec d) ω ∂μ = 0 := by
  have hcoordLp : ∀ i : Fin d, MemLp (fun ω ↦ (F : Ω → HilbertVec d) ω i) 2 μ :=
    fun i ↦ (Lp.memLp F).eval_piLp i
  have hint : ∀ i : Fin d, Integrable (fun ω ↦ (F : Ω → HilbertVec d) ω i) μ :=
    fun i ↦ memLp_one_iff_integrable.1 ((hcoordLp i).mono_exponent one_le_two)
  refine HilbertVec.ext fun i ↦ ?_
  rw [eval_integral_piLp hint i]
  have hcoord : ∫ ω, (F : Ω → HilbertVec d) ω i ∂μ =
      scalarMeanL2 (vectorL2Coord (μ := μ) i F) := by
    rw [scalarMeanL2_apply]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d ↦ ℝ) i) F] with ω hω
    exact hω.symm
  rw [hcoord, scalarMeanL2_vectorL2Coord_of_mem_stationaryPotentialSubspace hF i]
  rfl

end MeanZero

/-! ## Response energies of independent blocks -/

section BlockEnergy

variable [IsProbabilityMeasure μ]

/-- **The stationary potential responses of independent blocks are
orthogonal.** -/
theorem inner_stationaryPotentialProjection_eq_zero_of_indep
    (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    (hinv₁ : IsVAddInvariantSubalgebra d m₁) (hinv₂ : IsVAddInvariantSubalgebra d m₂)
    (hindep : ProbabilityTheory.Indep m₁ m₂ μ) {F₁ F₂ : VectorL2 d μ}
    (hF₁ : AEStronglyMeasurable[m₁] (F₁ : Ω → HilbertVec d) μ)
    (hF₂ : AEStronglyMeasurable[m₂] (F₂ : Ω → HilbertVec d) μ) :
    inner ℝ (stationaryPotentialProjection (μ := μ) F₁)
      (stationaryPotentialProjection (μ := μ) F₂) = 0 :=
  inner_eq_zero_of_indep_of_integral_eq_zero hindep
    (aestronglyMeasurable_stationaryPotentialProjection hm₁ hinv₁ hF₁)
    (aestronglyMeasurable_stationaryPotentialProjection hm₂ hinv₂ hF₂)
    (integral_eq_zero_of_mem_stationaryPotentialSubspace
      (stationaryPotentialProjection_mem F₁))

/-- **The response energy of a finite family of mutually independent blocks is
the sum of the block response energies.** -/
theorem norm_stationaryPotentialProjection_sum_sq {ι : Type*} (s : Finset ι)
    (mfam : ι → MeasurableSpace Ω) (hle : ∀ i, mfam i ≤ mΩ)
    (hinvfam : ∀ i, IsVAddInvariantSubalgebra d (mfam i))
    (hindep : ProbabilityTheory.iIndep mfam μ) (F : ι → VectorL2 d μ)
    (hF : ∀ i, AEStronglyMeasurable[mfam i] (F i : Ω → HilbertVec d) μ) :
    ‖stationaryPotentialProjection (μ := μ) (∑ i ∈ s, F i)‖ ^ 2 =
      ∑ i ∈ s, ‖stationaryPotentialProjection (μ := μ) (F i)‖ ^ 2 := by
  rw [map_sum]
  refine norm_sum_sq_of_pairwise_inner_eq_zero s _ fun i _ j _ hij ↦ ?_
  exact inner_stationaryPotentialProjection_eq_zero_of_indep (hle i) (hle j)
    (hinvfam i) (hinvfam j) (hindep.indep hij) (hF i) (hF j)

end BlockEnergy

end

end SuperdiffusionCLT.Probability.Stationary
