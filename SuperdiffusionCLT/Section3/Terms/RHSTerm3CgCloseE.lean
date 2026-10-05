/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgCloseD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3FluxEnergy
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3MemFluxB
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC

/-!
# `term3_cgBound_closeE`: the residuals of the display `e.RHS.term3.A`, continued

`term3_cgBound_closeD` (in `Section3/Terms/RHSTerm3CgCloseD.lean`) states the
coarse-graining display `e.RHS.term3.A` (Step 2 of the proof of `e.RHS.term3`)
with eight residual binders beyond the data of the statement.  This module removes two of them.

## The two removals

* `hJsubInt` — **deleted outright.**  `energySubQCarrier` is, by its definition,
  the sum of the `u_m`-energy cube average and half the cube average of
  `nu |∇u_m - ∇u_{n,z}|²`; the two summands are exactly the integrands of
  `hEnergyInt` and `hEnergyIntDiff`, so the integrability is a sum of two
  integrability hypotheses.

* `hEnergyIntDiff` — **deleted outright.**  The sub-cube energy of the glued
  difference is bounded *uniformly in the sample* by
  `vecCubeLpENorm_gluedGradientField_diff_subcube_B`
  (in `Section3/Terms/RHSTerm3MemFluxB.lean`) and is measurable in the sample
  by `measurable_vecSqAvg_gluedGradientField_diff_subcube` below, so it is integrable over the
  probability measure by `Integrable.of_bound`.

The residual `hEnergyInt` is kept: the bound
`vecCubeLpENorm_gluedGradientField_self_subcube_B`
(in `Section3/Terms/RHSTerm3MemFluxB.lean`) and the sample measurability
`measurable_vecSqAvg_gluedGradientField_self_subcube` below are the ingredients of its
integrability.

The sample measurability of a sub-cube energy of a glued field is the only new
analytic content.  On a scale-`n` sub-cube `R` of `cu_m` the scale-`m` glued
field is *not* one of the tiling maximizers of `R`, so the cube-wise identity
`gluedGradientField_apply_of_mem_openCubeSet` does not apply; instead the
`L²(cu_m)` class of the glued field is measurable in the sample
(`measurable_gluedGradientClass`, in `Section3/Terms/MaximizerCoefficientStabilityB.lean`),
and the sub-cube energy is the squared norm of that class after the diagonal
indicator multiplier `1_{cu_n}` — a fixed, sample-independent bounded matrix
field, whose class map is continuous
(`continuous_matFieldMulClass`, in `Section3/Setup/ResponseMeasurabilityC.lean`).
This is the route of the measurability lemmas of
`Section3/Terms/CenteredGradientMeasurable.lean`, transplanted from the
response `w` to the glued fields.

## Main results

* `measurable_vecSqAvg_gluedGradientField_self_subcube`
* `measurable_vecSqAvg_gluedGradientField_diff_subcube`
* `integrable_hEnergyIntDiff_discharged`, `integrable_hJsubInt_discharged`
* `term3_cgBound_closeE`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

/-! ## 1. The sub-cube energy as a class norm

The squared `L̲²(R)` norm `vecSqAvg R V` of a vector field, read on the half-open
cube `cubeSet R`, is the normalized volume average of `vecNormSq V` over the
open cube `openCubeSet R`: the two sets differ by a Lebesgue null set and have
equal volume, and `vecSqAvg` is `cubeSquareAverage`, i.e. the volume average of
the squared Euclidean norm. -/

/-- `vecSqAvg` is the normalized volume average of `vecNormSq` over the open
cube. -/
theorem vecSqAvg_eq_volumeAverage_vecNormSq_openCubeSet {d : ℕ} (R : TriadicCube d)
    (V : Vec d → Vec d) :
    vecSqAvg R V = volumeAverage (openCubeSet R) (fun x => vecNormSq (V x)) := by
  rw [vecSqAvg_eq_volumeAverage_vecNormSq R V, volumeAverage_cubeSet_eq_openCubeSet]

/-- The identity matrix acts trivially on a vector. -/
private theorem matVecMul_one_vec_cgE {d : ℕ} (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  have h := matVecMul_scalarMatrix (d := d) (1 : ℝ) v
  rw [scalarMatrix] at h
  simpa using h

/-- The zero matrix acts on a vector as the zero vector. -/
private theorem matVecMul_zero_vec_cgE {d : ℕ} (v : Vec d) :
    matVecMul (0 : Mat d) v = 0 := by
  funext i
  simp [matVecMul]

/-- The diagonal indicator matrix field acts on a vector as the scalar
indicator of the half-open cube. -/
private theorem matVecMul_indicatorMul_cgE {d : ℕ} (R : TriadicCube d) (x v : Vec d) :
    matVecMul (Set.indicator (cubeSet R) (fun _ => (1 : Mat d)) x) v =
      Set.indicator (cubeSet R) (fun _ : Vec d => v) x := by
  by_cases hx : x ∈ cubeSet R
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, matVecMul_one_vec_cgE]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, matVecMul_zero_vec_cgE]

/-- The sub-cube energy of a vector field is measurable in the sample as soon as
its `L²(cu_m)` class is, for every scale-`n` sub-cube `R` of `cu_m`.  The
zero-extension of the field to `R` is the diagonal indicator multiplier applied
to the class, a continuous map of classes, so the squared class norm — the cube
average up to the inverse cube volume — is measurable. -/
private theorem measurable_vecSqAvg_of_cu_m_class {d : ℕ} [NeZero d] {m n : ℕ}
    {V : ShellSeq d → Vec d → Vec d} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n m)
    (hVmem : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (V omega))
    (hVmeas : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hVmem omega)) :
    Measurable fun omega : ShellSeq d => vecSqAvg R (V omega) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set Q : TriadicCube d := originCube d (m : ℤ) with hQdef
  set A : Vec d → Mat d := fun x => Set.indicator (cubeSet R) (fun _ => (1 : Mat d)) x
    with hAdef
  have hsubopen : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hmulB : ∀ f : Vec d → Vec d, MemVectorL2 (openCubeSet Q) f →
      MemVectorL2 (openCubeSet Q) (fun x => matVecMul (A x) (f x)) := by
    intro f hf
    have hpt : (fun x => matVecMul (A x) (f x)) = Set.indicator (cubeSet R) f := by
      funext x
      rw [hAdef]
      exact matVecMul_indicatorMul_cgE R x (f x)
    rw [hpt]
    exact memVectorL2_indicator_cubeSet (Q := Q) (memVectorL2_mono hsubopen hf)
  have hbdB : ∀ x ∈ openCubeSet Q, ∀ v : Vec d,
      vecNormSq (matVecMul (A x) v) ≤ (1 : ℝ) ^ 2 * vecNormSq v := by
    intro x _ v
    rw [hAdef, matVecMul_indicatorMul_cgE R x v]
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
  have hmemR : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet R) (V omega) :=
    fun omega => memVectorL2_mono hsubopen (hVmem omega)
  have hZ : Measurable fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega)) := by
    have hkey : ∀ omega : ShellSeq d, toHilbertVectorL2OfVecField
          (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega)) =
        matFieldMulClass A hmulB (toHilbertVectorL2OfVecField (hVmem omega)) := by
      intro omega
      rw [matFieldMulClass_toHilbertVectorL2OfVecField A hmulB (hVmem omega)]
      refine toHilbertVectorL2OfVecField_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
      show Set.indicator (cubeSet R) (V omega) x = matVecMul (A x) (V omega x)
      rw [hAdef, matVecMul_indicatorMul_cgE R x (V omega x)]
      by_cases hx : x ∈ cubeSet R
      · simp only [Set.indicator_of_mem hx]
      · simp only [Set.indicator_of_notMem hx]
    have hfun : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
          (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))) =
        fun omega : ShellSeq d => matFieldMulClass A hmulB
          (toHilbertVectorL2OfVecField (hVmem omega)) := funext hkey
    rw [hfun]
    exact hcontMul.measurable.comp hVmeas
  have hnorm : ∀ omega : ShellSeq d, vecSqAvg R (V omega) =
      (MeasureTheory.volume (cubeSet R)).toReal⁻¹ * ‖toHilbertVectorL2OfVecField
        (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))‖ ^ (2 : ℕ) := by
    intro omega
    have h1 : vecSqAvg R (V omega) =
        (MeasureTheory.volume (cubeSet R)).toReal⁻¹ *
          ∫ x in cubeSet R, vecDot (V omega x) (V omega x) :=
      vecSqAvg_eq_inv_volume_mul_integral R _
    have hnonneg : (0 : ℝ) ≤ ∫ x in openCubeSet Q,
        vecDot (Set.indicator (cubeSet R) (V omega) x)
          (Set.indicator (cubeSet R) (V omega) x) := by
      refine setIntegral_nonneg (measurableSet_openCubeSet Q) fun x _ => ?_
      exact vecNormSq_nonneg _
    have h2 : ‖toHilbertVectorL2OfVecField
          (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))‖ ^ (2 : ℕ) =
        ∫ x in cubeSet R, vecDot (V omega x) (V omega x) := by
      rw [norm_toHilbertVectorL2OfVecField_eq_sqrt, Real.sq_sqrt hnonneg]
      exact integral_indicator_cubeSet_vecDot_eq_of_mem_descendantsAtDepth hR _
    rw [h1, ← h2]
  have hfun : (fun omega : ShellSeq d => vecSqAvg R (V omega)) =
      fun omega : ShellSeq d => (MeasureTheory.volume (cubeSet R)).toReal⁻¹ *
        ‖toHilbertVectorL2OfVecField
          (memVectorL2_indicator_cubeSet (Q := Q) (hmemR omega))‖ ^ (2 : ℕ) :=
    funext hnorm
  rw [hfun]
  exact ((continuous_norm.measurable.comp hZ).pow_const 2).const_mul _

/-- The `L²(U)` class of a difference of two vector fields is measurable in the
sample as soon as the classes of the fields are: the class of the difference is
the difference of the classes, and subtraction is continuous on the class
space. -/
private theorem measurable_toHilbertVectorL2OfVecField_sub {d : ℕ} {U : Set (Vec d)}
    {ι : Type*} [MeasurableSpace ι] {V₁ V₂ : ι → Vec d → Vec d}
    (h₁ : ∀ i, MemVectorL2 U (V₁ i)) (h₂ : ∀ i, MemVectorL2 U (V₂ i))
    (hm₁ : Measurable fun i => toHilbertVectorL2OfVecField (h₁ i))
    (hm₂ : Measurable fun i => toHilbertVectorL2OfVecField (h₂ i)) :
    Measurable fun i => toHilbertVectorL2OfVecField ((h₁ i).sub (h₂ i)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hfun : (fun i => toHilbertVectorL2OfVecField ((h₁ i).sub (h₂ i))) =
      fun i => toHilbertVectorL2OfVecField (h₁ i) -
        toHilbertVectorL2OfVecField (h₂ i) := by
    funext i
    exact toHilbertVectorL2OfVecField_sub (h₁ i) (h₂ i)
  rw [hfun]
  exact hm₁.sub hm₂

/-! ## 2. The sub-cube energy of the glued fields is measurable

The class `L²(cu_m)` of the scale-`m` glued field is measurable in the sample
(`measurable_gluedGradientClass`), and so is the class of its difference with the
scale-`n` glued field (`toHilbertVectorL2OfVecField_sub`); section 1 converts
those into the sample measurability of the sub-cube energy `vecSqAvg R`. -/

/-- **The sub-cube energy of the scale-`m` glued field is measurable in the
sample.**  The field is read as its `L²(cu_m)` class, whose sample measurability
is `measurable_gluedGradientClass`. -/
theorem measurable_vecSqAvg_gluedGradientField_self_subcube {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L m : ℕ) (F : Vec d) {n : ℕ} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n m) :
    Measurable (fun omega : ShellSeq d =>
      vecSqAvg R (fun x => gluedGradientField hnu L m m F omega x)) :=
  measurable_vecSqAvg_of_cu_m_class (m := m) (n := n) (R := R) hR
    (fun omega => memVectorL2_gluedGradientField hnu L m m F omega (originCube d (m : ℤ)))
    (measurable_gluedGradientClass hnu L m m F)

/-- **The sub-cube energy of the glued-field difference is measurable in the
sample.**  The class of the difference of the two glued fields is the difference
of their classes, each of which is measurable in the sample. -/
theorem measurable_vecSqAvg_gluedGradientField_diff_subcube {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L m k : ℕ) (F : Vec d) {n : ℕ} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n m) :
    Measurable (fun omega : ShellSeq d => vecSqAvg R (fun x =>
      gluedGradientField hnu L m m F omega x - gluedGradientField hnu L k m F omega x)) := by
  have h₁ : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (fun x => gluedGradientField hnu L m m F omega x) :=
    fun omega => memVectorL2_gluedGradientField hnu L m m F omega (originCube d (m : ℤ))
  have h₂ : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (fun x => gluedGradientField hnu L k m F omega x) :=
    fun omega => memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ))
  have hVmem : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (fun x => gluedGradientField hnu L m m F omega x -
        gluedGradientField hnu L k m F omega x) :=
    fun omega => (h₁ omega).sub (h₂ omega)
  refine measurable_vecSqAvg_of_cu_m_class (m := m) (n := n) (R := R) hR hVmem ?_
  exact measurable_toHilbertVectorL2OfVecField_sub h₁ h₂
    (measurable_gluedGradientClass hnu L m m F)
    (measurable_gluedGradientClass hnu L k m F)

/-! ## 3. The sub-cube energy of the glued difference is bounded uniformly

Both bounds are the `L̲²` bounds of `Section3/Terms/RHSTerm3MemFluxB.lean`
read through the carrier identity
`(vecCubeLpENorm Q 2 F).toReal ^ 2 = vecSqAvg Q F`.  They hold pointwise in the
sample, with no measurability input. -/

/-- **The sub-cube energy of the scale-`m` glued field is at most the number of
sub-cubes times `nu⁻² |F|²`**, from
`vecCubeLpENorm_gluedGradientField_self_subcube_B`. -/
theorem vecSqAvg_gluedGradientField_self_subcube_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {L n m : ℕ} (hnm : n ≤ m) (F : Vec d) (omega : ShellSeq d) {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n m) :
    vecSqAvg R (fun x => gluedGradientField hnu L m m F omega x) ≤
      (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
        (nu⁻¹ * Real.sqrt (vecNormSq F))) ^ 2 := by
  have hmem : MemLp (hilbertifyVecField (gluedGradientField hnu L m m F omega)) 2
      (normalizedCubeMeasure R) :=
    memLp_hilbertifyVecField_of_memVectorL2
      (memVectorL2_openCubeSet_gluedGradientField hnu L m m F omega R)
  have h1 : (vecCubeLpENorm R 2 (gluedGradientField hnu L m m F omega)).toReal ≤
      Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
        (nu⁻¹ * Real.sqrt (vecNormSq F)) :=
    vecCubeLpENorm_gluedGradientField_self_subcube_B (d := d) hnu omega
      (L := L) (n := n) (m := m) hnm (F := F) hR
  have hK : 0 ≤ Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
      (nu⁻¹ * Real.sqrt (vecNormSq F)) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (inv_nonneg.mpr hnu.le) (Real.sqrt_nonneg _))
  have hsq : (vecCubeLpENorm R 2 (gluedGradientField hnu L m m F omega)).toReal ^ 2 ≤
      (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) *
        (nu⁻¹ * Real.sqrt (vecNormSq F))) ^ 2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg h1 2
  rwa [toReal_vecCubeLpENorm_two_sq_memLp R hmem] at hsq

/-- **The sub-cube energy of the glued-field difference is at most
`(√card + 1)² nu⁻² |F|²`**, from
`vecCubeLpENorm_gluedGradientField_diff_subcube_B`. -/
theorem vecSqAvg_gluedGradientField_diff_subcube_le {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    {L n m : ℕ} (hnm : n ≤ m) (F : Vec d) (omega : ShellSeq d) {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n m) :
    vecSqAvg R (fun x => gluedGradientField hnu L m m F omega x -
        gluedGradientField hnu L n m F omega x) ≤
      ((Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) + 1) *
        (nu⁻¹ * Real.sqrt (vecNormSq F))) ^ 2 := by
  have hmem : MemLp (hilbertifyVecField (fun x => gluedGradientField hnu L m m F omega x -
      gluedGradientField hnu L n m F omega x)) 2 (normalizedCubeMeasure R) :=
    memLp_hilbertifyVecField_of_memVectorL2
      ((memVectorL2_openCubeSet_gluedGradientField hnu L m m F omega R).sub
        (memVectorL2_openCubeSet_gluedGradientField hnu L n m F omega R))
  have h1 : (vecCubeLpENorm R 2 (fun x => gluedGradientField hnu L m m F omega x -
      gluedGradientField hnu L n m F omega x)).toReal ≤
      (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) + 1) *
        (nu⁻¹ * Real.sqrt (vecNormSq F)) :=
    vecCubeLpENorm_gluedGradientField_diff_subcube_B (d := d) hnu omega
      (L := L) hnm (F := F) hR
  have hK : 0 ≤ (Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) + 1) *
      (nu⁻¹ * Real.sqrt (vecNormSq F)) :=
    mul_nonneg (add_nonneg (Real.sqrt_nonneg _) zero_le_one)
      (mul_nonneg (inv_nonneg.mpr hnu.le) (Real.sqrt_nonneg _))
  have hsq : (vecCubeLpENorm R 2 (fun x => gluedGradientField hnu L m m F omega x -
      gluedGradientField hnu L n m F omega x)).toReal ^ 2 ≤
      ((Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) + 1) *
        (nu⁻¹ * Real.sqrt (vecNormSq F))) ^ 2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg h1 2
  rwa [toReal_vecCubeLpENorm_two_sq_memLp R hmem] at hsq

/-! ## 4. The `nu`-weighted averages, in the shape of the residual -/

/-- A constant pulls out of the normalized volume average. -/
private theorem volumeAverage_const_mul_cgE {d : ℕ} (U : Set (Vec d)) (c : ℝ)
    (g : Vec d → ℝ) :
    volumeAverage U (fun x => c * g x) = c * volumeAverage U g := by
  rw [volumeAverage, volumeAverage, MeasureTheory.integral_const_mul]
  ring

/-- The normalized volume average of a nonnegative function is nonnegative. -/
private theorem volumeAverage_nonneg_cgE {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ volumeAverage U f := by
  rw [volumeAverage]
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (MeasureTheory.integral_nonneg hf)

/-- **Sample measurability of the `nu`-weighted sub-cube energy of the glued
difference.** -/
theorem measurable_volumeAverage_nu_vecNormSq_gluedDiff_subcube {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (L m : ℕ) (F : Vec d) {n : ℕ} {R : TriadicCube d}
    (hR : R ∈ largeCubeSubcubes d n m) :
    Measurable (fun omega : ShellSeq d => volumeAverage (openCubeSet R)
      (fun x => nu * vecNormSq (gluedGradientField hnu L m m F omega x -
        gluedGradientField hnu L n m F omega x))) := by
  have hbase : Measurable (fun omega : ShellSeq d => vecSqAvg R (fun x =>
      gluedGradientField hnu L m m F omega x - gluedGradientField hnu L n m F omega x)) :=
    measurable_vecSqAvg_gluedGradientField_diff_subcube (d := d) hnu L m n F hR
  have hfun : (fun omega : ShellSeq d => volumeAverage (openCubeSet R)
      (fun x => nu * vecNormSq (gluedGradientField hnu L m m F omega x -
        gluedGradientField hnu L n m F omega x))) =
      fun omega : ShellSeq d => nu * vecSqAvg R (fun x =>
        gluedGradientField hnu L m m F omega x - gluedGradientField hnu L n m F omega x) := by
    funext omega
    rw [volumeAverage_const_mul_cgE, vecSqAvg_eq_volumeAverage_vecNormSq_openCubeSet]
  rw [hfun]
  exact measurable_const.mul hbase

/-- **The `nu`-weighted sub-cube energy of the glued difference is bounded
uniformly in the sample.** -/
theorem volumeAverage_nu_vecNormSq_gluedDiff_subcube_le {d : ℕ} [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) {L n m : ℕ} (hnm : n ≤ m) (F : Vec d) (omega : ShellSeq d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d n m) :
    volumeAverage (openCubeSet R) (fun x => nu * vecNormSq
        (gluedGradientField hnu L m m F omega x - gluedGradientField hnu L n m F omega x)) ≤
      nu * ((Real.sqrt ((largeCubeSubcubes d n m).card : ℝ) + 1) *
        (nu⁻¹ * Real.sqrt (vecNormSq F))) ^ 2 := by
  rw [volumeAverage_const_mul_cgE, ← vecSqAvg_eq_volumeAverage_vecNormSq_openCubeSet]
  exact mul_le_mul_of_nonneg_left
    (vecSqAvg_gluedGradientField_diff_subcube_le (d := d) hnu hnm F omega hR) hnu.le

/-! ## 5. The residual `hEnergyIntDiff` of the display, discharged -/

/-- **`hEnergyIntDiff` is not a residual.**  The sub-cube energy of the glued
difference is bounded uniformly in the sample by section 3 and measurable in the
sample by section 4, so it is integrable over a probability measure.  Nothing is
carried beyond `0 < nu` and the scale ordering `S.n ≤ S.m`. -/
theorem integrable_hEnergyIntDiff_discharged (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (hnm : S.n ≤ S.m)
    (e : Vec d) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d => volumeAverage (openCubeSet R)
        (fun y => nu * vecNormSq
          (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure := by
  intro R hR
  have hmeas : Measurable (fun omega : ShellSeq d => volumeAverage (openCubeSet R)
      (fun y => nu * vecNormSq
        (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))) := by
    simpa only [gluedMaximizerGrad, gluedSubcubeGrad] using
      measurable_volumeAverage_nu_vecNormSq_gluedDiff_subcube (d := d) hnu S.LPrime S.m
        (fluxSlot nu S.LPrime P S.n e) (n := S.n) (R := R) hR
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (nu * ((Real.sqrt ((largeCubeSubcubes d S.n S.m).card : ℝ) + 1) *
      (nu⁻¹ * Real.sqrt (vecNormSq (fluxSlot nu S.LPrime P S.n e)))) ^ 2)
    (Filter.Eventually.of_forall fun omega => ?_)
  have hnn : 0 ≤ volumeAverage (openCubeSet R) (fun y => nu * vecNormSq
      (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
        gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)) :=
    volumeAverage_nonneg_cgE fun y => mul_nonneg hnu.le (vecNormSq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  simpa only [gluedMaximizerGrad, gluedSubcubeGrad] using
    volumeAverage_nu_vecNormSq_gluedDiff_subcube_le (d := d) hnu hnm
      (fluxSlot nu S.LPrime P S.n e) omega hR

/-! ## 6. The residual `hJsubInt` of the display, discharged -/

/-- **`hJsubInt` is not a residual.**  `energySubQCarrier` is, by its
definition, the cube average of the `u_m`-energy — the integrand of
`hEnergyInt` — plus half the cube average of `nu |∇u_m - ∇u_{n,z}|²`, the
integrand of `hEnergyIntDiff`.  Integrability is therefore a sum of the two
integrability hypotheses, and nothing else is consumed. -/
theorem integrable_hJsubInt_discharged (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (hEnergyIntDiff : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => nu * vecNormSq
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
              gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e)
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure) :
    ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
          (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R) P.toMeasure := by
  intro R hR
  have h2 : Integrable (fun omega : ShellSeq d => (1 / 2 : ℝ) *
      volumeAverage (openCubeSet R) (fun y => nu * vecNormSq
        (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y))) P.toMeasure :=
    (hEnergyIntDiff R hR).const_mul (1 / 2 : ℝ)
  refine ((hEnergyInt R hR).add h2).congr (Filter.Eventually.of_forall fun omega => ?_)
  simp only [energySubQCarrier, Pi.add_apply]

/-! ## 7. The display at the two discharged residuals

`term3_cgBound_closeE` is `term3_cgBound_closeD` with `hEnergyIntDiff` and
`hJsubInt` deleted: both are supplied in the proof by sections 5 and 6.  Every
other binder is copied verbatim from `term3_cgBound_closeD`, and the
conclusion is the `_hCgBound` display of the term-3 final assembly
verbatim. -/

/-- **`term3_cgBound_closeE`.**  The printed display `e.RHS.term3.A`
(`_hCgBound` of the term-3 final assembly) — verbatim — from the binders together
with six residuals: `hAnnealedSub`, `hAnnealedBig`, `hEnergyInt`, `hPigeon`,
`hde1` and the numeric comparison `hCerr`.

Two of the eight residuals of `term3_cgBound_closeD` are *not* hypotheses here:
`hEnergyIntDiff` (section 5) and `hJsubInt` (section 6) are constructed in the
proof from the uniform-in-sample sub-cube bounds of
`Section3/Terms/RHSTerm3MemFluxB.lean` and the sample measurability of the
sub-cube energy of a glued field established in sections 1-4.  Nothing new is
charged for them beyond `0 < nu` and the scale ordering already carried. -/
theorem term3_cgBound_closeE
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (hTwoHLeM : 2 * S.h ≤ S.m) (hHundredALeH : 100 * S.a ≤ S.h)
    (hWindowVsOffset : S.h + 1 ≤ 3 ^ S.a)
    (e : Vec d) (he : vecNormSq e = 1)
    (delta etaL : ℝ) (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse
        omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (Cerr : ℝ)
    (hde1 : delta + etaL ≤ 1)
    (hCerr : cgBoundConst (cgBoundAmpP d P S w) (cgBoundAmpW nu S) (bEllipConst d) ≤ Cerr)
    (hAnnealedSub : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      ∫ omega : ShellSeq d,
          energySubQCarrier nu P S e (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e))
            (gluedSubcubeGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega R
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hAnnealedBig : ∫ omega : ShellSeq d,
          energyBigQCarrier nu P S e
            (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e)) omega
        ∂P.toMeasure =
        (1 / 2 : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.m *
          vecNormSq (fluxSlot nu S.LPrime P S.n e))
    (hEnergyInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      Integrable (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet R)
          (fun y => -(nu / 2) * vecNormSq
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y) +
            vecDot (fluxSlot nu S.LPrime P S.n e)
              (gluedMaximizerGrad hnu S (fluxSlot nu S.LPrime P S.n e) omega y)))
        P.toMeasure)
    (hPigeon : |1 - (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ *
      sigmaBarStarInvSeq nu S.LPrime P S.m| ≤ delta + etaL) :
    ∫ omega : ShellSeq d,
        ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecDot (volumeAverageVec (openCubeSet R) ((w omega).toH1Function.grad))
              (volumeAverageVec (openCubeSet R)
                (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                  (gluedGradientField hnu S.LPrime S.m S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y -
                    gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega y))) ∂P.toMeasure ≤
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
              ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n),
                ∫ omega : ShellSeq d,
                  translatedBlockHalfWeight nu S.LPrime w omega z' z
                  ∂P.toMeasure) ^ ((1 : ℝ) / 2) *
          (delta + etaL) ^ ((1 : ℝ) / 2) +
        Cerr * (3 : ℝ) ^ (-(((S.ellPrime - S.ell : ℕ) : ℝ) / 4)) *
          ((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ) * nu ^ (-(5 : ℝ) / 2) := by
  have hnm : S.n ≤ S.m :=
    le_of_lt ((hSorder.n_lt_ell.trans hSorder.ell_lt_ellPrime).trans hSorder.ellPrime_lt_m)
  exact term3_cgBound_closeD d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder
    hTwoHLeM hHundredALeH hWindowVsOffset e he delta etaL hdelta hetaL w hw Cerr
    hde1 hCerr (integrable_hEnergyIntDiff_discharged d hnu P S hnm e) hAnnealedSub
    hAnnealedBig
    (integrable_hJsubInt_discharged d hnu P S e
      (integrable_hEnergyIntDiff_discharged d hnu P S hnm e) hEnergyInt)
    hEnergyInt hPigeon

end

end SuperdiffusionCLT.Section3.Terms
