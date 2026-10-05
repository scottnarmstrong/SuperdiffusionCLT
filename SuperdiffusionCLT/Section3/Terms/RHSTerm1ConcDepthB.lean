/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1MeasurableInputsB
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC

/-!
# The two sample-measurability residuals of the per-cube concentration clause

`RHSTerm1ConcDepth.depthClause_of_perCubeConcentration` reduces the depth moment
of the term-1 flux pairing field to a per-cube concentration hypothesis plus two
sample-measurability hypotheses:

* `hmeasA`: for every depth `j` and every depth-`j` descendant `R` of `cu_m`,
  the observable `omega ↦ ENNReal.ofReal (‖⟨a_ℓ(ω) ∇ũ_n(ω) − q̃⟩_{R}‖²)`;
* `hmeasB`: the same for the descendant square average
  `omega ↦ ENNReal.ofReal (‖a_ℓ(ω) ∇ũ_n(ω) − q̃‖²_{L̲²(R)})`.

This module discharges both, at the general pairing field
`pairingField hnu L k m F qTilde`, so the base module can instantiate them at
`concDepthField`.

## Main results

* `measurable_vecNormSq_volumeAverageVec_pairingField_sub` — `hmeasA` as a
  statement about the pairing field at an *arbitrary* descendant cube.  The
  ancestor mean is the inner product of the cut-off coefficient row class with
  the glued `L²(cu_m)` class minus the drift
  (`volumeAverageVec_cubeSet_pairingField_sub_eq_inner`), both of which are
  measurable functions of the sample.
* `aemeasurable_ofReal_vecNormSq_volumeAverageVec_pairingField` — the
  `ℝ≥0∞`-valued form of `hmeasA`.
* `vecSqAvg_eq_inv_volume_mul_integral` — the square average is the inverse
  volume times the set integral of the Euclidean square of the field.
* `aemeasurable_ofReal_vecSqAvg_pairingField` — `hmeasB`: the descendant square
  average of the pairing field is the inverse cube volume times the squared
  `L²(cu_m)` norm of the zero-extension of the pairing class, a continuous
  function of the measurable pairing class.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The descendant cube mean of the pairing field is measurable

The mean of the pairing field over a descendant cube is the vector of inner
products of the cut-off coefficient rows of that cube with the glued
`L²(cu_m)` class, minus the drift.  Both factors are measurable functions of the
sample, so the squared Euclidean length of the mean is. -/

/-- The squared Euclidean length of a vector-valued map with measurable
components is measurable. -/
private theorem measurable_vecNormSq_of_components {Omega : Type*}
    [MeasurableSpace Omega] {v : Omega → Vec d}
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecNormSq (v omega) := by
  show Measurable fun omega => vecDot (v omega) (v omega)
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hv i)

/-- **`hmeasA` at an arbitrary descendant.**  For every depth `j` and every
depth-`j` descendant `R` of `cu_m`, the squared length of the cube mean over
`R` of the pairing field `a_L(ω) ∇ũ_k(ω) − q̃` is a measurable function of the
sample.  The mean over the descendant is the mean over its open cube
(`volumeAverageVec_cubeSet_eq_openCubeSet`), which is the inner product of the
cut-off coefficient row class of `R` with the glued class of `cu_m`, minus the
drift; the row class is the class of an indicator of a continuous row
(`measurable_cutOffRowClass`) and the glued class is measurable
(`measurable_gluedGradientClass`). -/
theorem measurable_vecNormSq_volumeAverageVec_pairingField_sub [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L k m j : ℕ) (F qTilde : Vec d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) j) :
    Measurable (fun omega : ShellSeq d => vecNormSq (volumeAverageVec (cubeSet R)
      (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
        (gluedGradientField hnu L k m F omega x) - qTilde))) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hglued := measurable_gluedGradientClass (d := d) hnu L k m F
  set Q : TriadicCube d := originCube d (m : ℤ)
  have hVU : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hvec : ∀ omega : ShellSeq d, volumeAverageVec (cubeSet R)
      (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
        (gluedGradientField hnu L k m F omega x) - qTilde) =
    fun i : Fin d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
      inner ℝ (toHilbertVectorL2OfVecField
        ((memVectorL2_of_continuous (m : ℤ)
            (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega L i j)).indicator
          (isOpen_openCubeSet R).measurableSet))
        (toHilbertVectorL2OfVecField
          (memVectorL2_gluedGradientField hnu L k m F omega Q)) - qTilde i :=
    fun omega => by
      rw [volumeAverageVec_cubeSet_eq_openCubeSet R
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x) - qTilde)]
      exact volumeAverageVec_cubeSet_pairingField_sub_eq_inner hnu omega L
        k m F qTilde hVU (isOpen_openCubeSet R).measurableSet
        (memVectorL2_gluedGradientField hnu L k m F omega Q)
        (fun i => (memVectorL2_of_continuous (m : ℤ)
            (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega L i j)).indicator
          (isOpen_openCubeSet R).measurableSet)
        (Section2.Annealed.volume_openCubeSet_ne_zero R)
        (Homogenization.volume_openCubeSet_lt_top R).ne
        (fun i => MeasureTheory.MemLp.integrable (by norm_num)
          (MeasureTheory.MemLp.eval
            (memVectorL2_matVecMul_coefficientCutoff hnu omega L R
              (memVectorL2_openCubeSet_gluedGradientField hnu L k m F omega R)) i))
  have hrw : (fun omega : ShellSeq d => vecNormSq (volumeAverageVec (cubeSet R)
        (fun x => matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
          (gluedGradientField hnu L k m F omega x) - qTilde))) =
      fun omega : ShellSeq d =>
        vecNormSq (fun i : Fin d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
          inner ℝ (toHilbertVectorL2OfVecField
            ((memVectorL2_of_continuous (m : ℤ)
                (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega L i j)).indicator
              (isOpen_openCubeSet R).measurableSet))
            (toHilbertVectorL2OfVecField
              (memVectorL2_gluedGradientField hnu L k m F omega Q)) - qTilde i) := by
    funext omega
    exact congrArg vecNormSq (hvec omega)
  rw [hrw]
  have hcomp : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
      inner ℝ (toHilbertVectorL2OfVecField
        ((memVectorL2_of_continuous (m : ℤ)
            (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega L i j)).indicator
          (isOpen_openCubeSet R).measurableSet))
        (toHilbertVectorL2OfVecField
          (memVectorL2_gluedGradientField hnu L k m F omega Q))) := by
    intro i
    exact continuous_inner.measurable.comp
      ((measurable_cutOffRowClass L m R (isOpen_openCubeSet R).measurableSet i
        (fun omega => (memVectorL2_of_continuous (m : ℤ)
            (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega L i j)).indicator
          (isOpen_openCubeSet R).measurableSet)).prodMk hglued)
  exact measurable_vecNormSq_of_components (fun i =>
    (((measurable_const : Measurable
      (fun _ : ShellSeq d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹)).mul
      (hcomp i)).sub measurable_const))

/-- **`hmeasA` for the pairing field.**  The same statement read through the
definition of the pairing field. -/
theorem measurable_vecNormSq_volumeAverageVec_pairingField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L k m j : ℕ) (F qTilde : Vec d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) j) :
    Measurable (fun omega : ShellSeq d => vecNormSq
      (volumeAverageVec (cubeSet R) (pairingField hnu L k m F qTilde omega))) :=
  measurable_vecNormSq_volumeAverageVec_pairingField_sub hnu L k m j F qTilde hR

/-- **`hmeasA` in the `ℝ≥0∞` form carried by the clause.** -/
theorem aemeasurable_ofReal_vecNormSq_volumeAverageVec_pairingField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (L k m j : ℕ) (F qTilde : Vec d)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) j) :
    AEMeasurable (fun omega : ShellSeq d => ENNReal.ofReal (vecNormSq
      (volumeAverageVec (cubeSet R) (pairingField hnu L k m F qTilde omega))))
      P.toMeasure :=
  (measurable_vecNormSq_volumeAverageVec_pairingField hnu L k m j F qTilde hR).ennreal_ofReal
    |>.aemeasurable

/-! ## Scalar identities for the diagonal indicator matrix field

The multiplier that zeroes a field outside a descendant cube is the diagonal
matrix field `x ↦ 1_{cubeSet R}(x) • I`.  On the point `x` it is the identity
inside `cubeSet R` and the zero matrix outside, so it acts on a vector as the
scalar indicator. -/

private theorem matVecMul_one_vec (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  have h := matVecMul_scalarMatrix (d := d) (1 : ℝ) v
  rw [scalarMatrix] at h
  simpa using h

private theorem zero_matVecMul_vec (v : Vec d) : matVecMul (0 : Mat d) v = 0 := by
  funext i
  simp [matVecMul]

private theorem matVecMul_indicatorMul (R : TriadicCube d) (x v : Vec d) :
    matVecMul (Set.indicator (cubeSet R) (fun _ => (1 : Mat d)) x) v =
      Set.indicator (cubeSet R) (fun _ : Vec d => v) x := by
  by_cases hx : x ∈ cubeSet R
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, matVecMul_one_vec]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_matVecMul_vec]

/-! ## The descendant square average as an inverse volume times an integral -/

/-- The square average of a field over a cube is the inverse volume of the
half-open cube times the set integral of its squared Euclidean length. -/
theorem vecSqAvg_eq_inv_volume_mul_integral (R : TriadicCube d) (F : Vec d → Vec d) :
    vecSqAvg R F = (MeasureTheory.volume (cubeSet R)).toReal⁻¹ *
      ∫ x in cubeSet R, vecDot (F x) (F x) := by
  rw [vecSqAvg, cubeSquareAverage, volumeAverage]
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_cubeSet R) fun x _ => ?_
  exact HilbertVec.norm_sq_ofVec (F x)

/-! ## The integral of the zero-extension over the ambient cube -/

/-- The restricted volume of the ambient open cube intersected with a
descendant equals the restricted volume of that descendant. -/
theorem volume_restrict_inter_cubeSet_eq_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.volume.restrict (openCubeSet Q ∩ cubeSet R) =
      MeasureTheory.volume.restrict (cubeSet R) := by
  have hsubopen : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hnull : MeasureTheory.volume
      ((openCubeSet Q ∩ cubeSet R) \ openCubeSet R) = 0 := by
    refine MeasureTheory.measure_mono_null ?_ (volume_cubeSet_sdiff_openCubeSet R)
    intro x hx
    exact ⟨hx.1.2, hx.2⟩
  have hempty : openCubeSet R \ (openCubeSet Q ∩ cubeSet R) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    exact hx.2 ⟨hsubopen hx.1, fun i => ⟨le_of_lt (hx.1 i).1, (hx.1 i).2⟩⟩
  have hae : (openCubeSet Q ∩ cubeSet R : Set (Vec d)) =ᵐ[MeasureTheory.volume]
      (openCubeSet R : Set (Vec d)) := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hnull, by rw [hempty, MeasureTheory.measure_empty]⟩
  rw [MeasureTheory.Measure.restrict_congr_set hae,
    ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]

/-- The integral over the ambient open cube of the squared length of the
zero-extension of a field to a descendant is the integral over the descendant
of the squared length of the field. -/
theorem integral_indicator_cubeSet_vecDot_eq_of_mem_descendantsAtDepth {Q R : TriadicCube d}
    {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (F : Vec d → Vec d) :
    ∫ x in openCubeSet Q,
        vecDot (Set.indicator (cubeSet R) F x) (Set.indicator (cubeSet R) F x) =
      ∫ x in cubeSet R, vecDot (F x) (F x) := by
  have hpoint : (fun x => vecDot (Set.indicator (cubeSet R) F x)
        (Set.indicator (cubeSet R) F x)) =
      Set.indicator (cubeSet R) (fun y => vecDot (F y) (F y)) := by
    funext x
    by_cases hx : x ∈ cubeSet R
    · simp only [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, vecDot]
  rw [hpoint, MeasureTheory.setIntegral_indicator (measurableSet_cubeSet R),
    volume_restrict_inter_cubeSet_eq_of_mem_descendantsAtDepth hR]

/-! ## `hmeasB`

The square average of the pairing field over a descendant cube is written as
the inverse cube volume times the squared `L²(cu_m)` norm of the zero-extension
of the pairing class.  That zero-extension is the diagonal indicator multiplier
applied to the pairing class; the multiplier is a fixed (sample-independent)
bounded matrix field, so its class map is continuous, and the pairing class is
already known to be a measurable function of the sample. -/

/-- **`hmeasB`.**  For every depth `j` and every depth-`j` descendant `R` of
`cu_m`, the square average over `R` of the pairing field `a_L(ω) ∇ũ_k(ω) − q̃`
is `P`-a.e. measurable, hence so is its `ℝ≥0∞`-valued image. -/
theorem aemeasurable_ofReal_vecSqAvg_pairingField [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (L k m j : ℕ) (F qTilde : Vec d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (m : ℤ)) j) :
    AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (vecSqAvg R (pairingField hnu L k m F qTilde omega))) P.toMeasure := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let Q : TriadicCube d := originCube d (m : ℤ)
  set A : Vec d → Mat d := fun x => Set.indicator (cubeSet R) (fun _ => (1 : Mat d)) x with hAdef
  have hsubopen : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hmemR : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet R)
      (pairingField hnu L k m F qTilde omega) :=
    fun omega => memVectorL2_mono hsubopen
      (memVectorL2_pairingField hnu L k m F qTilde omega Q)
  have hmulB : ∀ f : Vec d → Vec d, MemVectorL2 (openCubeSet Q) f →
      MemVectorL2 (openCubeSet Q) (fun x => matVecMul (A x) (f x)) := by
    intro f hf
    have hpt : (fun x => matVecMul (A x) (f x)) = Set.indicator (cubeSet R) f := by
      funext x
      rw [hAdef]
      exact matVecMul_indicatorMul R x (f x)
    rw [hpt]
    exact memVectorL2_indicator_cubeSet (Q := Q) (memVectorL2_mono hsubopen hf)
  have hbdB : ∀ x ∈ openCubeSet Q, ∀ v : Vec d,
      vecNormSq (matVecMul (A x) v) ≤ (1 : ℝ) ^ 2 * vecNormSq v := by
    intro x _ v
    rw [hAdef, matVecMul_indicatorMul R x v]
    have h1 : (1 : ℝ) ^ 2 * vecNormSq v = vecNormSq v := by
      rw [one_pow, one_mul]
    by_cases hx : x ∈ cubeSet R
    · rw [Set.indicator_of_mem hx, h1]
    · rw [Set.indicator_of_notMem hx, h1]
      have h0 : vecNormSq (0 : Vec d) = 0 := by simp [vecNormSq, vecDot]
      rw [h0]
      exact vecNormSq_nonneg v
  have hcontMul : Continuous (matFieldMulClass A hmulB) :=
    continuous_matFieldMulClass (measurableSet_openCubeSet Q) A hmulB (by norm_num) hbdB
  have hclass : AEMeasurable (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_pairingField hnu L k m F qTilde omega Q)) P.toMeasure :=
    aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass hnu L k m F qTilde
      (measurable_gluedGradientClass (d := d) hnu L k m F).aemeasurable
  have hkey : ∀ omega : ShellSeq d, toHilbertVectorL2OfVecField
        (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega)) =
      matFieldMulClass A hmulB (toHilbertVectorL2OfVecField
        (memVectorL2_pairingField hnu L k m F qTilde omega Q)) := by
    intro omega
    rw [matFieldMulClass_toHilbertVectorL2OfVecField A hmulB
      (memVectorL2_pairingField hnu L k m F qTilde omega Q)]
    refine toHilbertVectorL2OfVecField_congr _ _
      (Filter.Eventually.of_forall fun x => ?_)
    show Set.indicator (cubeSet R) (pairingField hnu L k m F qTilde omega) x =
      matVecMul (A x) (pairingField hnu L k m F qTilde omega x)
    rw [hAdef, matVecMul_indicatorMul R x (pairingField hnu L k m F qTilde omega x)]
    by_cases hx : x ∈ cubeSet R
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx]
  have hMeasClass : AEMeasurable (fun omega : ShellSeq d => matFieldMulClass A hmulB
      (toHilbertVectorL2OfVecField (memVectorL2_pairingField hnu L k m F qTilde omega Q)))
      P.toMeasure :=
    hcontMul.measurable.comp_aemeasurable hclass
  have hMeasInd : AEMeasurable (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))) P.toMeasure :=
    (aemeasurable_congr (Filter.Eventually.of_forall fun omega => (hkey omega).symm)).mp hMeasClass
  have hMeasNorm : AEMeasurable (fun omega : ShellSeq d => ‖toHilbertVectorL2OfVecField
      (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))‖) P.toMeasure :=
    continuous_norm.measurable.comp_aemeasurable hMeasInd
  have hMeasProd : AEMeasurable (fun omega : ShellSeq d =>
      (MeasureTheory.volume (cubeSet R)).toReal⁻¹ * ‖toHilbertVectorL2OfVecField
        (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))‖ ^ (2 : ℕ)) P.toMeasure :=
    (hMeasNorm.pow_const (2 : ℕ)).const_mul _
  have hnorm : ∀ omega : ShellSeq d, vecSqAvg R (pairingField hnu L k m F qTilde omega) =
      (MeasureTheory.volume (cubeSet R)).toReal⁻¹ * ‖toHilbertVectorL2OfVecField
        (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))‖ ^ (2 : ℕ) := by
    intro omega
    have h1 : vecSqAvg R (pairingField hnu L k m F qTilde omega) =
        (MeasureTheory.volume (cubeSet R)).toReal⁻¹ *
          ∫ x in cubeSet R, vecDot (pairingField hnu L k m F qTilde omega x)
            (pairingField hnu L k m F qTilde omega x) :=
      vecSqAvg_eq_inv_volume_mul_integral R _
    have hnonneg : (0 : ℝ) ≤ ∫ x in openCubeSet Q,
        vecDot (Set.indicator (cubeSet R) (pairingField hnu L k m F qTilde omega) x)
          (Set.indicator (cubeSet R) (pairingField hnu L k m F qTilde omega) x) := by
      refine setIntegral_nonneg (measurableSet_openCubeSet Q) fun x _ => ?_
      exact vecNormSq_nonneg _
    have h2 : ‖toHilbertVectorL2OfVecField
          (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))‖ ^ (2 : ℕ) =
        ∫ x in cubeSet R, vecDot (pairingField hnu L k m F qTilde omega x)
          (pairingField hnu L k m F qTilde omega x) := by
      rw [norm_toHilbertVectorL2OfVecField_eq_sqrt, Real.sq_sqrt hnonneg]
      exact integral_indicator_cubeSet_vecDot_eq_of_mem_descendantsAtDepth hR _
    rw [h1, ← h2]
  exact ((aemeasurable_congr (Filter.Eventually.of_forall fun omega =>
    (hnorm omega).symm)).mp hMeasProd).ennreal_ofReal

end

end SuperdiffusionCLT.Section3.Terms
