/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1MeasurableInputs
public import SuperdiffusionCLT.Section3.Terms.GluedFieldL2Class
public import SuperdiffusionCLT.Section3.Terms.GluedFieldDifferenceMeasurable
public import SuperdiffusionCLT.Section3.Terms.MaximizerCoefficientStabilityB
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurability

/-!
# Measurable inputs of the term-1 statement, through the glued class

The four measurability obligations of `term1_of_obligations`
(in `RHSTerm1FrozenReduction`) concern the flux observables of the
term-1 statement.  Each reduces to the `L²(cu_m)` class of the built glued
gradient field: that class is a measurable function of the sample
(`measurable_gluedGradientClass` of `MaximizerCoefficientStabilityB`,
through the coefficient-stability estimate of
`MaximizerCoefficientStability`), and the cube-norm observables are fixed
constant multiples of the `enorm` of the class
(`vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField`).

## Main results

* `class_gluedGradientField_flux`: the `L²(cu_m)` class of the cutoff-multiplied
  difference of two glued fields is the multiplication class of the difference
  of the two glued classes.
* `aemeasurable_vecCubeLpENorm_pairingField_glued`: the `L²` obligation.
* `aemeasurable_vecCubeLpENorm_fluxDifference_glued`: the flux obligation.
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

/-! ## The class of the cutoff-multiplied difference of two glued fields -/

/-- The `L²` class of the cutoff matrix field applied to the pointwise
difference of two glued gradient fields is the multiplication class of the
difference of the two glued classes: the difference field is `L²`
(`MemVectorL2.sub`, then multiplication by the bounded cutoff matrix field),
the multiplication class of the class of the difference reads the class map on
the plain representative, and the class map subtracts. -/
theorem class_gluedGradientField_flux {nu : ℝ} (hnu : 0 < nu) (L₁ L₂ L k m : ℕ)
    (F : Vec d) (omega : ShellSeq d) (Q : TriadicCube d) :
    toHilbertVectorL2OfVecField
        (memVectorL2_matVecMul_coefficientCutoff hnu omega L Q
          ((memVectorL2_openCubeSet_gluedGradientField hnu L₁ k m F omega Q).sub
            (memVectorL2_openCubeSet_gluedGradientField hnu L₂ k m F omega Q))) =
      matFieldMulClass
        (fun x : Vec d => (coefficientCutoff nu omega L).toCoeffField x)
        (fun _ hf => memVectorL2_matVecMul_coefficientCutoff hnu omega L Q hf)
        (toHilbertVectorL2OfVecField
            (memVectorL2_openCubeSet_gluedGradientField hnu L₁ k m F omega Q) -
          toHilbertVectorL2OfVecField
            (memVectorL2_openCubeSet_gluedGradientField hnu L₂ k m F omega Q)) := by
  have hmem := memVectorL2_openCubeSet_gluedGradientField hnu L₁ k m F omega Q
  have hmem' := memVectorL2_openCubeSet_gluedGradientField hnu L₂ k m F omega Q
  rw [← toHilbertVectorL2OfVecField_sub hmem hmem',
    matFieldMulClass_toHilbertVectorL2OfVecField _ _ (hmem.sub hmem')]

/-! ## The `L²` obligation -/

/-- **The `L²` measurability obligation of `l.RHS.term1`**: the observable
`omega ↦ ‖a_ℓ(ω) ∇ũ_n − q̃‖_{L̲²(cu_m)}` is `P`-a.e. measurable.  The field is
the pairing field of `GluedFieldL2Class` at the pinned data, its class is a
measurable function of the sample from the glued gradient class, and the cube
norm is a fixed constant multiple of the `enorm` of the class. -/
theorem aemeasurable_vecCubeLpENorm_pairingField_glued [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e qTilde : Vec d) :
    AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde)) P.toMeasure := by
  set F : Vec d := fluxSlot nu S.LPrime P S.n e
  set Q : TriadicCube d := originCube d (S.m : ℤ)
  have hglued := measurable_gluedGradientClass (d := d) hnu S.ell S.n S.m F
  set C : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ ((1 : ℝ≥0∞) / 2).toReal
  have hEq : (fun omega : ShellSeq d =>
      vecCubeLpENorm Q 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m F omega x) - qTilde)) =
    fun omega : ShellSeq d => C * ‖toHilbertVectorL2OfVecField
      (memVectorL2_pairingField hnu S.ell S.n S.m F qTilde omega Q)‖ₑ := by
    funext omega
    exact vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField
      (memVectorL2_pairingField hnu S.ell S.n S.m F qTilde omega Q)
  rw [hEq]
  exact AEMeasurable.const_mul
    (continuous_enorm.measurable.comp_aemeasurable
      (aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass hnu
        S.ell S.n S.m F qTilde hglued.aemeasurable)) C

/-! ## The flux obligation -/

/-- **The flux measurability obligation of `l.RHS.term1`**: the observable
`omega ↦ ‖a_ℓ(ω) (∇u_n − ∇ũ_n)‖_{L̲²(cu_m)}` is `P`-a.e. measurable.  The
class of the cutoff-multiplied difference field is the multiplication class of
the difference of the two glued classes (`class_gluedGradientField_flux`), the
multiplication class map is Caratheodory in (class, sample)
(`measurable_matFieldMulClass_family`, the cutoff matrix field being jointly
measurable in (sample, point) and uniformly bounded on the cube), and the cube
norm is a fixed constant multiple of the `enorm` of the class. -/
theorem aemeasurable_vecCubeLpENorm_fluxDifference_glued [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e : Vec d) :
    AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x -
            gluedGradientField hnu S.ell S.n S.m
              (fluxSlot nu S.LPrime P S.n e) omega x))) P.toMeasure := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  set F : Vec d := fluxSlot nu S.LPrime P S.n e
  set Q : TriadicCube d := originCube d (S.m : ℤ)
  have hA := measurable_gluedGradientClass (d := d) hnu S.LPrime S.n S.m F
  have hB := measurable_gluedGradientClass (d := d) hnu S.ell S.n S.m F
  have hpair : AEMeasurable (fun omega : ShellSeq d =>
      (toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q),
      toHilbertVectorL2OfVecField
        (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q)))
      P.toMeasure := hA.aemeasurable.prodMk hB.aemeasurable
  set C : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ ((1 : ℝ≥0∞) / 2).toReal
  have hEq : (fun omega : ShellSeq d =>
      vecCubeLpENorm Q 2
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.LPrime S.n S.m F omega x -
            gluedGradientField hnu S.ell S.n S.m F omega x))) =
    fun omega : ShellSeq d => C * ‖matFieldMulClass
        (fun x : Vec d => (coefficientCutoff nu omega S.ell).toCoeffField x)
        (fun f hf => memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q hf)
        (toHilbertVectorL2OfVecField
            (memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q) -
          toHilbertVectorL2OfVecField
            (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q))‖ₑ := by
    funext omega
    have hbridge := vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField
      (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q
        ((memVectorL2_openCubeSet_gluedGradientField hnu S.LPrime S.n S.m F omega Q).sub
          (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega Q)))
    rw [class_gluedGradientField_flux hnu S.LPrime S.ell S.ell S.n S.m F omega Q] at hbridge
    exact hbridge
  rw [hEq]
  exact AEMeasurable.const_mul
    (continuous_enorm.measurable.comp_aemeasurable
      (measurable_matFieldMulClass_family (measurableSet_openCubeSet Q)
        (fun omega x => (coefficientCutoff nu omega S.ell).toCoeffField x)
        (measurable_prod_coefficientCutoff nu S.ell)
        (fun omega _ hf => memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell Q hf)
        (fun omega => exists_matVecMul_bound_openCubeSet Q
          (fun i j => continuous_coefficientCutoff_entry nu omega S.ell i j))
        (continuous_sub.measurable.comp_aemeasurable hpair))) C

/-! ## The depth obligation -/

/-- The squared norm of a vector-valued map with measurable components is
measurable. -/
private theorem measurable_vecNormSq_of_components {Omega : Type*}
    [MeasurableSpace Omega] {v : Omega → Vec d}
    (hv : ∀ i, Measurable fun omega => v omega i) :
    Measurable fun omega => vecNormSq (v omega) := by
  show Measurable fun omega => vecDot (v omega) (v omega)
  exact Finset.measurable_sum _ fun i _ => (hv i).mul (hv i)

/-- The cut-off coefficient row of a sub-cube is a measurable `L²(cu_m)` class:
the row is continuous in the point and jointly measurable in (sample, point),
so the indicator field is square-integrable on the ambient cube and its class
map is measurable. -/
theorem measurable_cutOffRowClass [NeZero d] {nu : ℝ} (L m : ℕ) (R : TriadicCube d)
    (hRm : MeasurableSet (openCubeSet R)) (i : Fin d)
    (hK : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (Set.indicator (openCubeSet R)
        (fun y => (fun j => (coefficientCutoff nu omega L).toCoeffField y i j : Vec d)))) :
    Measurable (fun omega : ShellSeq d => toHilbertVectorL2OfVecField (hK omega)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hrowcont : ∀ omega : ShellSeq d, Continuous fun y : Vec d =>
      (fun j => (coefficientCutoff nu omega L).toCoeffField y i j : Vec d) :=
    fun omega => continuous_pi fun j => continuous_coefficientCutoff_entry nu omega L i j
  have hrowjoint : Measurable fun q : ShellSeq d × Vec d =>
      (fun j => (coefficientCutoff nu q.1 L).toCoeffField q.2 i j : Vec d) :=
    measurable_prod_of_continuous_of_measurable hrowcont
      (fun y => Measurable.of_eval fun j =>
        (measurable_apply_entry y i j).comp (measurable_coefficientCutoff nu L))
  have hKjoint : Measurable fun q : ShellSeq d × Vec d =>
      Set.indicator (openCubeSet R)
        (fun y => (fun j => (coefficientCutoff nu q.1 L).toCoeffField y i j : Vec d)) q.2 := by
    have hrw : (fun q : ShellSeq d × Vec d =>
        Set.indicator (openCubeSet R)
          (fun y => (fun j => (coefficientCutoff nu q.1 L).toCoeffField y i j : Vec d)) q.2) =
        Set.indicator (Prod.snd ⁻¹' openCubeSet R)
          (fun q : ShellSeq d × Vec d =>
            (fun j => (coefficientCutoff nu q.1 L).toCoeffField q.2 i j : Vec d)) := by
      funext q
      by_cases hq : q.2 ∈ openCubeSet R
      · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' openCubeSet R from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' openCubeSet R from hq)]
    rw [hrw]
    exact hrowjoint.indicator (measurable_snd hRm)
  exact measurable_toHilbertVectorL2OfVecField_of_measurable hKjoint hK

/-- The cube mean of the pairing field on a sub-cube of `cu_m` is the vector of
inner products of the cut-off coefficient rows with the glued class, minus the
drift. -/
theorem volumeAverageVec_cubeSet_pairingField_sub_eq_inner {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L k m : ℕ) (F qTilde : Vec d) {U V : Set (Vec d)}
    (hVU : V ⊆ U) (hV : MeasurableSet V)
    (hg : MemVectorL2 U (gluedGradientField hnu L k m F omega))
    (hK : ∀ i : Fin d, MemVectorL2 U (Set.indicator V
      (fun y => (fun j => (coefficientCutoff nu omega L).toCoeffField y i j : Vec d))))
    (h0 : MeasureTheory.volume V ≠ 0) (htop : MeasureTheory.volume V ≠ ⊤)
    (hint : ∀ i : Fin d, MeasureTheory.IntegrableOn
      (fun y : Vec d => matVecMul ((coefficientCutoff nu omega L).toCoeffField y)
        (gluedGradientField hnu L k m F omega y) i) V MeasureTheory.volume) :
    volumeAverageVec V (fun y => matVecMul
        ((coefficientCutoff nu omega L).toCoeffField y)
        (gluedGradientField hnu L k m F omega y) - qTilde) =
      fun i : Fin d => (MeasureTheory.volume V).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField (hK i))
          (toHilbertVectorL2OfVecField hg) - qTilde i := by
  funext i
  have h1 : volumeAverageVec V (fun y => matVecMul
        ((coefficientCutoff nu omega L).toCoeffField y)
        (gluedGradientField hnu L k m F omega y) - qTilde) i =
      volumeAverageVec V (fun y => matVecMul
        ((coefficientCutoff nu omega L).toCoeffField y)
        (gluedGradientField hnu L k m F omega y)) i - qTilde i := by
    rw [show volumeAverageVec V (fun y => matVecMul
          ((coefficientCutoff nu omega L).toCoeffField y)
          (gluedGradientField hnu L k m F omega y) - qTilde) i
      = volumeAverage V (fun y => matVecMul
          ((coefficientCutoff nu omega L).toCoeffField y)
          (gluedGradientField hnu L k m F omega y) i - qTilde i) from rfl,
      volumeAverage_sub_const h0 htop (hint i) (qTilde i),
      show volumeAverageVec V (fun y => matVecMul
          ((coefficientCutoff nu omega L).toCoeffField y)
          (gluedGradientField hnu L k m F omega y)) i
        = volumeAverage V (fun y => matVecMul
            ((coefficientCutoff nu omega L).toCoeffField y)
            (gluedGradientField hnu L k m F omega y) i) from rfl]
  rw [h1, volumeAverageVec_matVecMul_eq_inner hVU hV
    (fun y : Vec d => (coefficientCutoff nu omega L).toCoeffField y) hg i (hK i)]

/-- **The depth measurability obligation of `l.RHS.term1`**: for every depth `j` the
observable `omega ↦ (‖·‖²_{·})`-moment over the depth-`j` descendants of `cu_m`
of the centred pairing field `a_ℓ(ω) ∇ũ_n(ω) − q̃` is `P`-a.e. measurable.  Each
descendant cube mean is the inner product of the cut-off coefficient row class
with the glued class, minus the drift (`volumeAverageVec_cubeSet_pairingField_sub_eq_inner`);
the row classes and the glued class are measurable functions of the sample, so
each descendant mean is, and the moment is the (card⁻¹-weighted) finite sum of
the squared norms of the descendant means. -/
theorem aemeasurable_ofReal_vecDepthSqMoment_pairingField [NeZero d] {nu : ℝ}
    (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection)
    (e qTilde : Vec d) (j : ℕ) :
    AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m
            (fluxSlot nu S.LPrime P S.n e) omega x) - qTilde))) P.toMeasure := by
  set F : Vec d := fluxSlot nu S.LPrime P S.n e
  set Q : TriadicCube d := originCube d (S.m : ℤ)
  have hglued := measurable_gluedGradientClass (d := d) hnu S.ell S.n S.m F
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hsummand : ∀ R ∈ descendantsAtDepth Q j, Measurable (fun omega : ShellSeq d =>
      vecNormSq (volumeAverageVec (cubeSet R)
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m F omega x) - qTilde))) := by
    intro R hR
    have hVU : openCubeSet R ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hvec : ∀ omega : ShellSeq d, volumeAverageVec (cubeSet R)
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m F omega x) - qTilde) =
      fun i : Fin d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
        inner ℝ (toHilbertVectorL2OfVecField
          ((memVectorL2_of_continuous (S.m : ℤ)
              (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega S.ell i j)).indicator
            (isOpen_openCubeSet R).measurableSet))
          (toHilbertVectorL2OfVecField
            (memVectorL2_gluedGradientField hnu S.ell S.n S.m F omega Q)) - qTilde i :=
      fun omega => by
        rw [volumeAverageVec_cubeSet_eq_openCubeSet R
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.ell S.n S.m F omega x) - qTilde)]
        exact volumeAverageVec_cubeSet_pairingField_sub_eq_inner hnu omega S.ell
          S.n S.m F qTilde hVU (isOpen_openCubeSet R).measurableSet
          (memVectorL2_gluedGradientField hnu S.ell S.n S.m F omega Q)
          (fun i => (memVectorL2_of_continuous (S.m : ℤ)
              (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega S.ell i j)).indicator
            (isOpen_openCubeSet R).measurableSet)
          (Section2.Annealed.volume_openCubeSet_ne_zero R)
          (Homogenization.volume_openCubeSet_lt_top R).ne
          (fun i => MeasureTheory.MemLp.integrable (by norm_num)
            (MeasureTheory.MemLp.eval
              (memVectorL2_matVecMul_coefficientCutoff hnu omega S.ell R
                (memVectorL2_openCubeSet_gluedGradientField hnu S.ell S.n S.m F omega R)) i))
    have hrw : (fun omega : ShellSeq d => vecNormSq (volumeAverageVec (cubeSet R)
          (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (gluedGradientField hnu S.ell S.n S.m F omega x) - qTilde))) =
        fun omega : ShellSeq d =>
          vecNormSq (fun i : Fin d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹ *
            inner ℝ (toHilbertVectorL2OfVecField
              ((memVectorL2_of_continuous (S.m : ℤ)
                  (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega S.ell i j)).indicator
                (isOpen_openCubeSet R).measurableSet))
              (toHilbertVectorL2OfVecField
                (memVectorL2_gluedGradientField hnu S.ell S.n S.m F omega Q)) - qTilde i) := by
      funext omega
      exact congrArg vecNormSq (hvec omega)
    rw [hrw]
    have hcomp : ∀ i : Fin d, Measurable (fun omega : ShellSeq d =>
        inner ℝ (toHilbertVectorL2OfVecField
          ((memVectorL2_of_continuous (S.m : ℤ)
              (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega S.ell i j)).indicator
            (isOpen_openCubeSet R).measurableSet))
          (toHilbertVectorL2OfVecField
            (memVectorL2_gluedGradientField hnu S.ell S.n S.m F omega Q))) := by
      intro i
      exact continuous_inner.measurable.comp
        ((measurable_cutOffRowClass S.ell S.m R (isOpen_openCubeSet R).measurableSet i
          (fun omega => (memVectorL2_of_continuous (S.m : ℤ)
              (continuous_pi fun j => continuous_coefficientCutoff_entry nu omega S.ell i j)).indicator
            (isOpen_openCubeSet R).measurableSet)).prodMk hglued)
    exact measurable_vecNormSq_of_components (fun i =>
      (((measurable_const : Measurable
        (fun _ : ShellSeq d => (MeasureTheory.volume (openCubeSet R)).toReal⁻¹)).mul
        (hcomp i)).sub measurable_const))
  have hmeas : Measurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (vecDepthSqMoment Q j
        (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
          (gluedGradientField hnu S.ell S.n S.m F omega x) - qTilde))) := by
    unfold vecDepthSqMoment descendantsAverage
    refine Measurable.ennreal_ofReal ((measurable_const : Measurable
      (fun _ : ShellSeq d => (((descendantsAtDepth Q j).card : ℝ))⁻¹)).mul ?_)
    exact Finset.measurable_sum _ fun R hR => hsummand R hR
  exact hmeas.aemeasurable

end

end SuperdiffusionCLT.Section3.Terms