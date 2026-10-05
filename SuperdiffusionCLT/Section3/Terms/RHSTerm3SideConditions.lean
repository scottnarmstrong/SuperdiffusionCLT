/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SourceGapsB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3SignedBlockDev
public import SuperdiffusionCLT.Section3.Terms.WindowFactorAbsorption
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3AnchorsConstFirst

/-!
# The `L^2(P)` and integrability side conditions on the response

The last obligation cluster of the final Term 3 statement: the binders `hsq`, `hF`,
`hgF`, `hosc`, `hcg`, `hbHalfInt`, `hIntB`, `hInt1`-`hInt3`, `hIntSwap`, the
`L^2(P)` and integrability side conditions on the response `w`.

The key input is the measurability of the
gradient class of the canonical Dirichlet response in the sample
(`measurable_gradToHilbertVectorL2_dirichletResponse`,
`Section3/Setup/ResponseMeasurabilityB.lean`), which makes every cube mean of
an observable of `∇w` a measurable function of the sample: the cube mean does
not depend on the selection (`volumeAverageVec_comp_grad_response_funext`) and
the canonical one is an inner product of measurable `L^2` classes
(`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`).

## What is proved here

* `sideCondition_hsq` -- the `L^2(P)` membership of the squared-norm cube-mean
  observable of `∇w` on every coarse sub-cube.  Measurability comes from the
  canonical-response route above; finiteness of the second moment comes from a
  single-summand comparison against the fourth-power Jensen inequality
  (`ofReal_subcube_fourth_average_le`,
  `Section3/Terms/RHSTerm3SourceGaps.lean`) at the fourth moment `hfin`
  supplied by `lintegral_gradFour_pow_ne_top`
  (`Section3/Terms/RHSTerm3SourceGapsB.lean`).
* `sideCondition_hF` -- the integrability of the cutoff flux of the glued-field
  difference on every maximizer sub-cube, pointwise in the sample, from the
  `L^2` membership of the glued field (`memVectorL2_gluedGradientField`) and
  its multiplication by the bounded cutoff matrix
  (`memVectorL2_matVecMul_coefficientCutoff`).
* `sideCondition_hgF` -- the pairing integrability, each coordinate a product
  of two `L^2` functions (`MemLp.integrable_mul` at the conjugate pair `2 2`).
* `sideCondition_hInt1` -- the integrability of the `∇w`-weighted double
  lattice average with the constant weight `1`, from `sideCondition_hsq`.

The remaining binders of the cluster (`hosc`, `hcg`, `hbHalfInt`, `hIntB`,
`hInt2`, `hInt3`, `hIntSwap`) are not discharged here.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Helpers -/

/-- The identity matrix acts trivially on a vector. -/
private theorem matVecMul_one_mat (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The squared norm of a vector-valued map with measurable components is
measurable. -/
private theorem measurable_vecNormSq_of_components {Omega : Type*}
    [MeasurableSpace Omega] {v : Omega → Vec d}
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecNormSq (v omega) := by
  show Measurable fun omega => vecDot (v omega) (v omega)
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hv i)

/-! ## Measurability of the squared cube mean of the response gradient -/

/-- **Measurability of the squared cube mean of the response gradient** on a
coarse sub-cube.  The cube mean of an observable of `∇w` does not depend on the
selection (`volumeAverageVec_comp_grad_response_funext`), and at the canonical
response it is the identity-matrix pairing against the canonical response's
gradient class, a measurable `L^2` class of the sample
(`measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp`).  No
selection of a solution enters. -/
private theorem measurable_vecNormSq_volumeAverageVec_grad [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (z' : TriadicCube d)
    (hz' : z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m) :
    Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad))) := by
  have hsub : openCubeSet z' ⊆ openCubeSet (originCube d (S.m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hz'
    exact openCubeSet_subset_of_mem_descendantsAtDepth hz'
  have hcan : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d))
          ((dirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e)).toH1Function.grad y))) := by
    refine measurable_volumeAverageVec_matVecMul_grad_dirichletResponse_comp
      (fun omega => omega) (fun _ _ => (1 : Mat d)) ?_ ?_ S.LPrime S.ellPrime S.m
      (testVector nu S.LPrime P S.n e) hsub (measurableSet_openCubeSet z') ?_
    · intro a i j
      exact continuous_const
    · intro y i j
      exact measurable_const
    · exact fun x => measurable_dirichletRhsField_apply S.LPrime S.ellPrime
        (testVector nu S.LPrime P S.n e) x
  have hmat : Measurable (fun omega : ShellSeq d =>
      volumeAverageVec (openCubeSet z')
        (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y))) :=
    measurable_volumeAverageVec_matVecMul_grad_of_canonical hsub
      (fun _ _ => (1 : Mat d)) hw hcan
  have hEq : (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad))) =
    fun omega : ShellSeq d => vecNormSq (volumeAverageVec (openCubeSet z')
      (fun y => matVecMul ((1 : Mat d)) ((w omega).toH1Function.grad y))) := by
    funext omega
    exact congrArg vecNormSq (congrArg (volumeAverageVec (openCubeSet z'))
      (funext fun y => (matVecMul_one_mat _).symm))
  rw [hEq]
  exact measurable_vecNormSq_of_components
    (fun i => (measurable_pi_apply i).comp hmat)

/-! ## The second-moment bound at the fourth moment -/

/-- **The second moment of the squared cube mean** of the response gradient on
a coarse sub-cube is dominated by the fourth moment
`∫⁻ ||∇w||^4_{L4bar(cu_m)}` times the number of coarse sub-cubes: a
single-summand comparison in the lattice average, each summand being the
fourth-power Jensen inequality `ofReal_subcube_fourth_average_le`. -/
private theorem lintegral_sq_cubeMean_le
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (z' : TriadicCube d)
    (hz' : z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m) :
    (∫⁻ omega : ShellSeq d, ENNReal.ofReal
        (vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) ^ (2 : ℕ))
      ∂P.toMeasure) ≤
    ENNReal.ofReal (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℕ) : ℝ) *
      (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
      ∂P.toMeasure) := by
  classical
  have hcard : (0 : ℝ) < ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (largeCubeSubcubes_nonempty d
      (coarseBlockScale d S) S.m)
  have hsingle : ∀ omega : ShellSeq d,
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ) ≤
        ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ) *
          ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ))) := by
    intro omega
    have h1 : ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ) *
        ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            vecNormSq (volumeAverageVec (openCubeSet R)
              ((w omega).toH1Function.grad)) ^ (2 : ℕ))) =
        ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet R)
            ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
      mul_inv_cancel_left₀ (ne_of_gt hcard) _
    calc vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) ^ (2 : ℕ)
        ≤ ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            vecNormSq (volumeAverageVec (openCubeSet R)
              ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
          Finset.single_le_sum (f := fun R : TriadicCube d =>
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ))
            (fun _ _ => pow_nonneg (vecNormSq_nonneg _) 2) hz'
      _ = ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ) *
            ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ))) := h1.symm
  have hstep1 : (∫⁻ omega : ShellSeq d, ENNReal.ofReal
      (vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ))
      ∂P.toMeasure) ≤
      (∫⁻ omega : ShellSeq d, ENNReal.ofReal
          (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ) *
            ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ))))
        ∂P.toMeasure) :=
    lintegral_mono fun omega => ENNReal.ofReal_le_ofReal (hsingle omega)
  have hmul : ∀ omega : ShellSeq d,
      ENNReal.ofReal (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ) *
          ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ)))) =
      ENNReal.ofReal (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)) *
        ENNReal.ofReal ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            vecNormSq (volumeAverageVec (openCubeSet R)
              ((w omega).toH1Function.grad)) ^ (2 : ℕ))) :=
    fun omega => ENNReal.ofReal_mul (le_of_lt hcard)
  have hpull : (∫⁻ omega : ShellSeq d, ENNReal.ofReal
        (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ) *
          ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ))))
      ∂P.toMeasure) =
      ENNReal.ofReal (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)) *
        (∫⁻ omega : ShellSeq d, ENNReal.ofReal
            ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
              ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
                vecNormSq (volumeAverageVec (openCubeSet R)
                  ((w omega).toH1Function.grad)) ^ (2 : ℕ)))
          ∂P.toMeasure) := by
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hmul),
      MeasureTheory.lintegral_const_mul'
        (r := ENNReal.ofReal (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)))
        (f := fun omega : ShellSeq d => ENNReal.ofReal
          ((((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
            ∑ R ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
              vecNormSq (volumeAverageVec (openCubeSet R)
                ((w omega).toH1Function.grad)) ^ (2 : ℕ))))
        (by exact ENNReal.ofReal_ne_top)]
  refine le_trans hstep1 ?_
  refine le_trans (le_of_eq hpull) ?_
  exact mul_le_mul_right (lintegral_mono fun omega => ofReal_subcube_fourth_average_le
    (w omega).toH1Function.grad_memVectorL2)
    (ENNReal.ofReal (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)))

/-! ## The `hsq` obligation -/

/-- **The `hsq` side condition**: the squared cube mean of the response
gradient on a coarse sub-cube is square-integrable in the sample.  Measurable
by the canonical-response route; the fourth moment `hfin` supplied by
`lintegral_gradFour_pow_ne_top` bounds the second moment through the
single-summand comparison `lintegral_sq_cubeMean_le`. -/
theorem sideCondition_hsq [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) {nu : ℝ} {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hfin : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤)
    (z' : TriadicCube d)
    (hz' : z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m) :
    MemLp (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad))) 2 P.toMeasure := by
  have hmeas := measurable_vecNormSq_volumeAverageVec_grad P S w hw z' hz'
  have hnn : ∀ omega : ShellSeq d, (0 : ℝ) ≤
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ) :=
    fun _ => pow_nonneg (vecNormSq_nonneg _) 2
  have hsqmeas : Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ)) := hmeas.pow_const 2
  have hint : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z')
        ((w omega).toH1Function.grad)) ^ (2 : ℕ)) P.toMeasure := by
    refine ⟨hsqmeas.aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hnn)]
    have hle := lintegral_sq_cubeMean_le P S w z' hz'
    exact hle.trans_lt
      (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin))
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hint

/-! ## The `hF` obligation -/

/-- **The `hF` side condition**: on every maximizer sub-cube the cutoff flux of
the glued-field difference is integrable, pointwise in the sample: the
difference of the two glued fields is `L^2` on the large cube, hence on the
sub-cube, and multiplication by the bounded cutoff matrix preserves `L^2`. -/
theorem sideCondition_hF [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (omega : ShellSeq d) (R : TriadicCube d)
    (hR : R ∈ largeCubeSubcubes d S.n S.m) (i : Fin d) :
    IntegrableOn (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
      (gluedGradientField hnu S.LPrime S.m S.m
          (fluxSlot nu S.LPrime P S.n e) omega y -
        gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega y) i) (cubeSet R) volume := by
  show MeasureTheory.Integrable (fun y : Vec d =>
      matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m
            (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega y) i)
    (MeasureTheory.volume.restrict (cubeSet R))
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
  have : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (openCubeSet R)) :=
    SuperdiffusionCLT.Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet
      R
  have hRsub : openCubeSet R ⊆ openCubeSet (originCube d (S.m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hd : MemVectorL2 (openCubeSet R)
      (fun y => gluedGradientField hnu S.LPrime S.m S.m
          (fluxSlot nu S.LPrime P S.n e) omega y -
        gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega y) :=
    (memVectorL2_mono hRsub
      (memVectorL2_gluedGradientField hnu S.LPrime S.m S.m
        (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))).sub
      (memVectorL2_mono hRsub
        (memVectorL2_gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))))
  exact MeasureTheory.MemLp.integrable (by norm_num)
    (MeasureTheory.MemLp.eval
      (memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime R hd) i)

/-! ## The `hgF` obligation -/

/-- **The `hgF` side condition**: on every maximizer sub-cube the pairing of
the response gradient with the cutoff flux of the glued-field difference is
integrable: each coordinate of the pairing is a product of two `L^2`
functions, and the dot product is the finite sum of the coordinates. -/
theorem sideCondition_hgF [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (omega : ShellSeq d) (R : TriadicCube d)
    (hR : R ∈ largeCubeSubcubes d S.n S.m) :
    IntegrableOn (fun y => vecDot ((w omega).toH1Function.grad y)
      (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m
            (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega y))) (cubeSet R) volume := by
  show MeasureTheory.Integrable (fun y : Vec d => vecDot ((w omega).toH1Function.grad y)
      (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m
            (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega y)))
    (MeasureTheory.volume.restrict (cubeSet R))
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
  have : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (openCubeSet R)) :=
    SuperdiffusionCLT.Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet
      R
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d (S.m : ℤ)) := by
    rw [largeCubeSubcubes_eq_descendantsAtDepth] at hR
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hd : MemVectorL2 (openCubeSet R)
      (fun y => gluedGradientField hnu S.LPrime S.m S.m
          (fluxSlot nu S.LPrime P S.n e) omega y -
        gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega y) :=
    (memVectorL2_mono hsub
      (memVectorL2_gluedGradientField hnu S.LPrime S.m S.m
        (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ)))).sub
      (memVectorL2_mono hsub
        (memVectorL2_gluedGradientField hnu S.LPrime S.n S.m
          (fluxSlot nu S.LPrime P S.n e) omega (originCube d (S.m : ℤ))))
  have hflux : ∀ i : Fin d, MeasureTheory.MemLp
      (fun y : Vec d => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
        (gluedGradientField hnu S.LPrime S.m S.m
            (fluxSlot nu S.LPrime P S.n e) omega y -
          gluedGradientField hnu S.LPrime S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega y) i) 2
      (MeasureTheory.volume.restrict (openCubeSet R)) :=
    fun i => MeasureTheory.MemLp.eval
      (memVectorL2_matVecMul_coefficientCutoff hnu omega S.LPrime R hd) i
  have hgrad : ∀ i : Fin d, MeasureTheory.MemLp
      (fun y : Vec d => (w omega).toH1Function.grad y i) 2
      (MeasureTheory.volume.restrict (openCubeSet R)) :=
    fun i => MeasureTheory.MemLp.eval
      (memVectorL2_mono hsub (w omega).toH1Function.grad_memVectorL2) i
  have hprod : ∀ i : Fin d, MeasureTheory.Integrable
      (fun y : Vec d => (w omega).toH1Function.grad y i *
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
          (gluedGradientField hnu S.LPrime S.m S.m
              (fluxSlot nu S.LPrime P S.n e) omega y -
            gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega y) i))
      (MeasureTheory.volume.restrict (openCubeSet R)) :=
    fun i => (hgrad i).integrable_mul (hflux i)
  exact MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => hprod i)

/-! ## The `hInt1` obligation -/

/-- **The `hInt1` side condition**: the `∇w`-weighted double lattice average
with the constant weight `1` is integrable.  The constant weight drops out of
the inner lattice average, so the observable is the plain average of the
squared cube means of `∇w`, a finite measurable average of the `hsq`
observables. -/
theorem sideCondition_hInt1 [NeZero d]
    (P : ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) {nu : ℝ} {e : Vec d}
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega))
    (hfin : (∫⁻ omega : ShellSeq d,
        (vecCubeLpENorm (originCube d (S.m : ℤ)) 4 (w omega).toH1Function.grad) ^ (4 : ℕ)
      ∂P.toMeasure) ≠ ⊤) :
    Integrable (fun omega : ShellSeq d =>
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad) (fun _ => (1 : ℝ))) P.toMeasure := by
  classical
  have hone : ∀ z' : TriadicCube d,
      (((descendantsAtDepth z' (coarseBlockScale d S - S.n)).card : ℕ) : ℝ)⁻¹ *
        ∑ z ∈ descendantsAtDepth z' (coarseBlockScale d S - S.n), (1 : ℝ) = 1 := by
    intro z'
    rw [Finset.sum_const, Nat.smul_one_eq_cast]
    have hpos : (0 : ℕ) < (descendantsAtDepth z' (coarseBlockScale d S - S.n)).card :=
      Finset.card_pos.mpr (descendantsAtDepth_nonempty _ _)
    exact inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hpos)
  have havg : ∀ omega : ShellSeq d,
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad) (fun _ => (1 : ℝ)) =
        ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
          ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
            vecNormSq (volumeAverageVec (openCubeSet z')
              ((w omega).toH1Function.grad)) := by
    intro omega
    rw [weightedBlockAverage]
    simp only [hone, mul_one]
  have hfun : (fun omega : ShellSeq d =>
      weightedBlockAverage d S.n (coarseBlockScale d S) S.m
        ((w omega).toH1Function.grad) (fun _ => (1 : ℝ))) =
    fun omega : ShellSeq d => ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
      ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
        vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad)) := funext havg
  rw [hfun]
  have hmeas : Measurable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z')
            ((w omega).toH1Function.grad))) :=
    (measurable_const).mul (Finset.measurable_sum _ fun z' hz' =>
      measurable_vecNormSq_volumeAverageVec_grad P S w hw z' hz')
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hnn : ∀ omega : ShellSeq d, (0 : ℝ) ≤
      ((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z')
            ((w omega).toH1Function.grad)) :=
    fun omega => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun _ _ => vecNormSq_nonneg _)
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall hnn)]
  have hpoint : ∀ omega : ShellSeq d, ENNReal.ofReal
      (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
          vecNormSq (volumeAverageVec (openCubeSet z')
            ((w omega).toH1Function.grad))) =
    ENNReal.ofReal (((largeCubeSubcubes d (coarseBlockScale d S) S.m).card : ℝ)⁻¹) *
      ∑ z' ∈ largeCubeSubcubes d (coarseBlockScale d S) S.m,
        ENNReal.ofReal (vecNormSq (volumeAverageVec (openCubeSet z')
          ((w omega).toH1Function.grad))) := by
    intro omega
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg _)),
      ENNReal.ofReal_sum_of_nonneg fun i _ => vecNormSq_nonneg _]
  rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top),
    MeasureTheory.lintegral_finsetSum _ (fun z' hz' =>
      (Measurable.ennreal_ofReal
        (measurable_vecNormSq_volumeAverageVec_grad P S w hw z' hz')))]
  refine lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
  refine (WithTop.sum_lt_top.mpr fun z' hz' => ?_).ne
  have hintf := sideCondition_hsq P S w hw hfin z' hz'
  have hintf' : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (openCubeSet z') ((w omega).toH1Function.grad)))
      P.toMeasure := hintf.integrable (by norm_num)
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun omega => vecNormSq_nonneg _)).mp
    hintf'.hasFiniteIntegral

end

end SuperdiffusionCLT.Section3.Terms