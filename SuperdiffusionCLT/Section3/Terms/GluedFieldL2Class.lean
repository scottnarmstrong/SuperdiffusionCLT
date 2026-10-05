/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2
public import SuperdiffusionCLT.Section3.Terms.GluedField
public import Homogenization.Book.Ch02.Theorems.GradientUniqueness

/-!
# The `L²(cu_m)` class of the pairing field of `l.RHS.term1`

The pairing field of the measurability obligation of `l.RHS.term1` is
`a_ℓ(ω) ∇ũ_n(ω) − q̃`, where `∇ũ_n = gluedGradientField` is the glued gradient
field of `e.u.k.def`.  This module reduces the
obligation to the `L²(cu_m)` class measurability of that field, with every
downstream step discharged.

## Main results

* `pairingField`: the pairing field `a_ℓ(ω) ∇ũ_k(ω) − q̃` of
  `l.RHS.term1`, as a definition.
* `memVectorL2_pairingField`: the pairing field is square integrable on every
  triadic cube, from the `L²` membership of the glued field
  (`memVectorL2_gluedGradientField`) and its multiplication by the bounded
  cutoff matrix (`memVectorL2_matVecMul_coefficientCutoff`).
* `pairingField_class_eq`: the `L²` class of the pairing field is the
  multiplication class of the glued gradient class by the cutoff matrix field,
  minus the class of the constant `qTilde`.
* `aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass`: the
  class measurability of the pairing field from the class measurability of the
  glued gradient field, by the multiplication-operator measurability of
  `ResponseMeasurabilityC`.
* `aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairingField`: the
  measurability obligation itself, closed by the reduction
  `Setup.aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairing` as soon
  as the glued gradient class is measurable.

The remaining input, taken as a hypothesis by
`aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass`, is
the `L²(cu_m)` class measurability of `gluedGradientField` itself.  It is not
proved in this module: the sample dependence of `gluedGradientField` runs
through `Book.Ch02.responseMaximizer` (a `Classical.choose` at a choice point
disjoint from the Dirichlet response), so it needs stability of the Chapter 2
cube maximizer under perturbation of the coefficient, unlike the Dirichlet
response, for which the `1`-Lipschitz operator `cubeDirichletGradClass`
exists.  That stability is supplied by `measurable_gluedGradientClass` (module
`MaximizerCoefficientStabilityB`), which discharges the hypothesis.  Chapter 2
also gives uniqueness: two maximizers of the same problem have a.e. equal
gradients, so the field is well defined as an `L²` class once a maximizer
exists.

## References

* The paper: `e.u.k.y.def`, `e.u.k.def` and `e.v.ky.energy`.
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

/-! ## The pairing field -/

section PairingField

/-- **The pairing field of `l.RHS.term1`**: at the point `x` it is
`a_ℓ(ω) ∇ũ_k(ω) − q̃`, the cutoff matrix field applied to the glued gradient
field of `e.u.k.def`, minus the constant drift `q̃`.  The instance used in `l.RHS.term1` is
`L = ℓ`, `k = n`, `m = m`, `F = fluxSlot ν L' P n e`, `q̃ = qTilde`. -/
def pairingField {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ) (F qTilde : Vec d)
    (omega : ShellSeq d) : Vec d → Vec d := fun x =>
  matVecMul ((coefficientCutoff nu omega L).toCoeffField x)
    (gluedGradientField hnu L k m F omega x) - qTilde

/-- **The pairing field is square integrable on every triadic cube.**  The
glued gradient field is `L²` on every triadic cube
(`memVectorL2_gluedGradientField`), and multiplication by the bounded cutoff
matrix field preserves it (`memVectorL2_matVecMul_coefficientCutoff`); the
constant `q̃` is `L²` on the finite-measure cube. -/
theorem memVectorL2_pairingField {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ)
    (F qTilde : Vec d) (omega : ShellSeq d) (Q : TriadicCube d) :
    MemVectorL2 (openCubeSet Q) (pairingField hnu L k m F qTilde omega) :=
  (memVectorL2_matVecMul_coefficientCutoff hnu omega L Q
    (memVectorL2_gluedGradientField hnu L k m F omega Q)).sub
    (memVectorL2_const qTilde)

/-- The `L²(cu_m)` class of the pairing field is the class of the product of
the cutoff matrix field with the glued gradient field, minus the class of the
constant `qTilde` — the algebraic identity of `L2Ambient.lean` read through the
multiplication operator of `ResponseMeasurabilityC.lean`. -/
theorem pairingField_class_eq {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ) (F qTilde : Vec d)
    (omega : ShellSeq d) :
    toHilbertVectorL2OfVecField (memVectorL2_pairingField hnu L k m F qTilde omega
        (originCube d (m : ℤ))) =
      matFieldMulClass
        (fun x : Vec d => (coefficientCutoff nu omega L).toCoeffField x)
        (fun _ hf => memVectorL2_matVecMul_coefficientCutoff hnu omega L
          (originCube d (m : ℤ)) hf)
        (toHilbertVectorL2OfVecField
          (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ)))) -
      toHilbertVectorL2OfVecField (memVectorL2_const qTilde) := by
  have hglued := memVectorL2_gluedGradientField hnu L k m F omega
    (originCube d (m : ℤ))
  have hA := memVectorL2_matVecMul_coefficientCutoff hnu omega L
    (originCube d (m : ℤ)) hglued
  rw [matFieldMulClass_toHilbertVectorL2OfVecField _ _ hglued,
    ← toHilbertVectorL2OfVecField_sub hA (memVectorL2_const qTilde)]
  rfl

end PairingField

/-! ## Choice independence of the maximizer gradient -/

section ChoiceIndependence

end ChoiceIndependence

/-! ## Measurability of the multiplication map on classes -/

section FamilyMeasurability

variable {alpha : Type*} [MeasurableSpace alpha] {U : Set (Vec d)}

/-- Joint measurability of a matrix field applied to a fixed measurable
field. -/
theorem measurable_prod_matVecMul_family
    (A : alpha → Vec d → Mat d)
    (hA : Measurable fun q : alpha × Vec d => A q.1 q.2)
    {g : Vec d → Vec d} (hg : Measurable g) :
    Measurable (fun q : alpha × Vec d => matVecMul (A q.1 q.2) (g q.2)) := by
  refine Measurable.of_eval fun i => ?_
  show Measurable fun q : alpha × Vec d => ∑ j, A q.1 q.2 i j * g q.2 j
  refine Finset.measurable_sum _ fun j _ => ?_
  have hAij : Measurable fun q : alpha × Vec d => A q.1 q.2 i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  exact hAij.mul ((measurable_pi_apply j).comp (hg.comp measurable_snd))

/-- **The multiplication map on classes, at a fixed class, is measurable in the
parameter.**  The class space is second countable, so the dense-sequence
criterion applies; the norm and the inner products against the dense sequence
are set integrals of jointly measurable integrands. -/
theorem measurable_matFieldMulClass_apply (A : alpha → Vec d → Mat d)
    (hA : Measurable fun q : alpha × Vec d => A q.1 q.2)
    (hmul : ∀ (a : alpha) (f : Vec d → Vec d), MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A a x) (f x)))
    (f : HilbertVectorL2 U) :
    Measurable fun a : alpha => matFieldMulClass (A a) (hmul a) f := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  refine measurable_of_measurable_norm_inner_denseRange
    (TopologicalSpace.denseSeq (HilbertVectorL2 U))
    (TopologicalSpace.denseRange_denseSeq _) ?_ ?_
  · have hval : (fun a : alpha => ‖matFieldMulClass (A a) (hmul a) f‖) =
        fun a : alpha => Real.sqrt
          (∫ x in U, vecDot (matVecMul (A a x) (hilbertClassField f x))
            (matVecMul (A a x) (hilbertClassField f x)) ∂MeasureTheory.volume) := by
      funext a
      exact norm_toHilbertVectorL2OfVecField_eq_sqrt
        (hmul a _ (memVectorL2_hilbertClassField f))
    rw [hval]
    have hint := measurable_setIntegral_vecDot_prod U
      (measurable_prod_matVecMul_family A hA (measurable_hilbertClassField f))
      (measurable_prod_matVecMul_family A hA (measurable_hilbertClassField f))
    exact Real.continuous_sqrt.measurable.comp hint
  · intro n
    have hinnereq : (fun a : alpha => inner ℝ
        (TopologicalSpace.denseSeq (HilbertVectorL2 U) n)
        (matFieldMulClass (A a) (hmul a) f)) =
        fun a : alpha => ∫ x in U,
          vecDot (hilbertClassField
              (TopologicalSpace.denseSeq (HilbertVectorL2 U) n) x)
            (matVecMul (A a x) (hilbertClassField f x)) ∂MeasureTheory.volume := by
      funext a
      have h0 : TopologicalSpace.denseSeq (HilbertVectorL2 U) n =
          toHilbertVectorL2OfVecField (memVectorL2_hilbertClassField
            (TopologicalSpace.denseSeq (HilbertVectorL2 U) n)) :=
        (toHilbertVectorL2OfVecField_hilbertClassField _).symm
      conv_lhs => rw [h0]
      exact inner_toHilbertVectorL2OfVecField_eq_integral
        (memVectorL2_hilbertClassField
          (TopologicalSpace.denseSeq (HilbertVectorL2 U) n))
        (hmul a (hilbertClassField f) (memVectorL2_hilbertClassField f))
    rw [hinnereq]
    have hint := measurable_setIntegral_vecDot_prod U
      ((measurable_hilbertClassField
        (TopologicalSpace.denseSeq (HilbertVectorL2 U) n)).comp measurable_snd)
      (measurable_prod_matVecMul_family A hA (measurable_hilbertClassField f))
    exact hint

/-- **The multiplication map on classes is Caratheodory** in the pair (class,
parameter): continuous in the class (uniform boundedness of the matrix field),
measurable in the parameter, hence jointly measurable on the product of the
second-countable class space with the parameter. -/
theorem measurable_matFieldMulClass_family {mu : MeasureTheory.Measure alpha}
    (hU : MeasurableSet U)
    (A : alpha → Vec d → Mat d)
    (hA : Measurable fun q : alpha × Vec d => A q.1 q.2)
    (hmul : ∀ (a : alpha) (f : Vec d → Vec d), MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A a x) (f x)))
    (hbd : ∀ a : alpha, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Vec d,
      vecNormSq (matVecMul (A a x) v) ≤ C ^ 2 * vecNormSq v)
    {g : alpha → HilbertVectorL2 U} (hg : AEMeasurable g mu) :
    AEMeasurable (fun a : alpha => matFieldMulClass (A a) (hmul a) (g a)) mu := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have huncurry : Measurable (Function.uncurry
      (fun (f : HilbertVectorL2 U) (a : alpha) => matFieldMulClass (A a) (hmul a) f)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun a => by
        obtain ⟨C, hC, hCbd⟩ := hbd a
        exact continuous_matFieldMulClass hU (A a) (hmul a) hC hCbd)
      (measurable_matFieldMulClass_apply A hA hmul)
  have hpair : AEMeasurable (fun a : alpha => (g a, a)) mu :=
    hg.prodMk measurable_id.aemeasurable
  have hcomp := huncurry.comp_aemeasurable hpair
  exact hcomp

end FamilyMeasurability

/-! ## Measurability of the cutoff matrix field -/

section CutoffMeasurability

/-- The cutoff coefficient field has continuous entries. -/
theorem continuous_coefficientCutoff_entry (nu : ℝ) (omega : ShellSeq d)
    (L : ℕ) (i j : Fin d) :
    Continuous fun x : Vec d => ((coefficientCutoff nu omega L).toCoeffField x) i j := by
  have hgoal : (fun x : Vec d => ((coefficientCutoff nu omega L).toCoeffField x) i j) =
      fun x : Vec d => ((nu • (1 : Mat d)) i j + (streamCutoff omega L x) i j) := by
    funext x
    rw [coefficientCutoff_toCoeffField_apply nu omega L x, Matrix.add_apply,
      Matrix.smul_apply]
  rw [hgoal]
  exact continuous_const.add
    ((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_streamCutoff_apply omega L)))

/-- The cutoff coefficient field is jointly measurable in the sample and the
point, entrywise. -/
theorem measurable_prod_coefficientCutoff (nu : ℝ) (L : ℕ) :
    Measurable (fun q : ShellSeq d × Vec d =>
      (coefficientCutoff nu q.1 L).toCoeffField q.2) := by
  have hstream : ∀ i j : Fin d,
      Measurable (fun q : ShellSeq d × Vec d => (streamCutoff q.1 L q.2) i j) := by
    intro i j
    have hunc : Measurable (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
        streamCutoff omega L x i j)) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun omega => (continuous_apply j).comp
          ((continuous_apply i).comp (continuous_streamCutoff_apply omega L)))
        (fun x => (measurable_pi_apply j).comp
          ((measurable_pi_apply i).comp (measurable_streamCutoff_apply L x)))
    have hcomp : (fun q : ShellSeq d × Vec d => (streamCutoff q.1 L q.2) i j) =
        (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
          streamCutoff omega L x i j)) ∘ Prod.swap := rfl
    rw [hcomp]
    exact hunc.comp measurable_swap
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hrw : (fun q : ShellSeq d × Vec d =>
      ((coefficientCutoff nu q.1 L).toCoeffField q.2) i j) =
      fun q : ShellSeq d × Vec d =>
        ((nu • (1 : Mat d)) i j + (streamCutoff q.1 L q.2) i j) := by
    funext q
    simp only [coefficientCutoff_toCoeffField_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [hrw]
  exact (measurable_const : Measurable (fun _ : ShellSeq d × Vec d =>
    (nu • (1 : Mat d)) i j)).add (hstream i j)

end CutoffMeasurability

/-! ## The class measurability of the pairing field -/

/-- **The `L²(cu_m)` class of the pairing field is measurable from the glued
gradient class.**  By `pairingField_class_eq` it is the multiplication class of
the glued gradient class by the cutoff matrix field, minus the class of the
constant `qTilde`; the multiplication map on classes is Caratheodory in
(class, sample), so composing with the measurable glued class map and a
constant gives the observable. -/
theorem aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass
    {nu : ℝ} (hnu : 0 < nu) (L k m : ℕ) (F qTilde : Vec d)
    {mu : MeasureTheory.Measure (ShellSeq d)}
    (hgluedClass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField
        (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ)))) mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField
        (memVectorL2_pairingField hnu L k m F qTilde omega (originCube d (m : ℤ)))) mu := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hbd : ∀ omega : ShellSeq d, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈
      openCubeSet (originCube d (m : ℤ)), ∀ v : Vec d,
      vecNormSq (matVecMul ((coefficientCutoff nu omega L).toCoeffField x) v)
        ≤ C ^ 2 * vecNormSq v :=
    fun omega => exists_matVecMul_bound_openCubeSet (originCube d (m : ℤ))
      (fun i j => continuous_coefficientCutoff_entry nu omega L i j)
  have hclass : (fun omega : ShellSeq d => toHilbertVectorL2OfVecField
      (memVectorL2_pairingField hnu L k m F qTilde omega (originCube d (m : ℤ)))) =
      fun omega : ShellSeq d => matFieldMulClass
          (fun x : Vec d => (coefficientCutoff nu omega L).toCoeffField x)
          (fun _ hf => memVectorL2_matVecMul_coefficientCutoff hnu omega L
            (originCube d (m : ℤ)) hf)
          (toHilbertVectorL2OfVecField
            (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ)))) -
        toHilbertVectorL2OfVecField (memVectorL2_const qTilde) := by
    funext omega
    exact pairingField_class_eq hnu L k m F qTilde omega
  rw [hclass]
  have hfam := measurable_matFieldMulClass_family (measurableSet_openCubeSet
      (originCube d (m : ℤ))) (fun omega x => (coefficientCutoff nu omega L).toCoeffField x)
    (measurable_prod_coefficientCutoff nu L)
    (fun omega _ hf => memVectorL2_matVecMul_coefficientCutoff hnu omega L
      (originCube d (m : ℤ)) hf) hbd hgluedClass
  have hconst : AEMeasurable (fun _ : ShellSeq d =>
      toHilbertVectorL2OfVecField
        (memVectorL2_const (U := openCubeSet (originCube d (m : ℤ))) qTilde)) mu :=
    (measurable_const : Measurable (fun _ : ShellSeq d =>
      toHilbertVectorL2OfVecField
        (memVectorL2_const (U := openCubeSet (originCube d (m : ℤ))) qTilde))).aemeasurable
  have hsubm : Measurable (fun z : HilbertVectorL2 (openCubeSet (originCube d (m : ℤ))) ×
      HilbertVectorL2 (openCubeSet (originCube d (m : ℤ))) => z.1 - z.2) :=
    continuous_sub.measurable
  have hsub := hsubm.comp_aemeasurable (hfam.prodMk hconst)
  exact hsub

/-- **The measurability obligation from the glued gradient class.**  The reduction
`Setup.aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairing` proves the
obligation verbatim as soon as the `L²(cu_m)` class of the pairing field is
measurable, and the preceding theorem provides that class from the glued
gradient class.  What remains is the hypothesis: the sample measurability
of `ω ↦ [gluedGradientField]_{L²(cu_m)}`, which is not proved here because it
needs stability of the Chapter 2 cube maximizer under coefficient perturbation;
see `measurable_gluedGradientClass`. -/
theorem aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairingField
    [NeZero d] {LPrime ellPrime k m : ℕ} {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {F qTilde p : Vec d}
    {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (hgluedClass : AEMeasurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField
        (memVectorL2_gluedGradientField hnu L k m F omega (originCube d (m : ℤ)))) mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (pairingField hnu L k m F qTilde omega x))|) mu :=
  aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_pairing hw
    (fun omega => memVectorL2_pairingField hnu L k m F qTilde omega
      (originCube d (m : ℤ)))
    (aemeasurable_toHilbertVectorL2OfVecField_pairingField_of_gluedClass hnu L k m F
      qTilde hgluedClass)

/-! ## The joint-measurability route to the glued gradient class -/

section JointRoute

end JointRoute

end

end SuperdiffusionCLT.Section3.Terms