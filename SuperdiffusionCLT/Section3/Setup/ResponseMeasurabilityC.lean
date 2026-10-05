/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1

/-!
# Multiplication by a matrix field, and the cutoff-difference observable of `l.RHS.term2`

`ResponseMeasurability` reduces every observable of the Dirichlet response
of `e.def.w` to the same observable at the canonical response
`dirichletResponse`, and `ResponseMeasurabilityB` proves that the gradient
class of the canonical response is a measurable function of the sample.  The
measurability of the observable of `l.RHS.term2` asks for one more step: it is not
the cube energy of the gradient but the cube energy of `A ∇w`, the gradient
multiplied by the cutoff-difference coefficient field
`A = a_{L'} − a_ℓ = k_{L'} − k_ℓ`.

This module supplies that step.  Multiplication by a matrix field that is
bounded on the cube is a Lipschitz map of `L²(Q; ℝ^d)` classes
(`matFieldMulClass`, `lipschitz_matFieldMulClass`), and the matrix field of the
obligation is continuous in the point and measurable in the sample.  So the
observable `(f, ω) ↦ ‖M_{A ω} f‖` is a Caratheodory function of the class and
the sample, hence jointly measurable, and composing it with the measurable
gradient class of the canonical response gives the obligation.

## Main results

* `vecNormSq_matVecMul_le_rowSum`, `exists_matVecMul_bound_openCubeSet`: a
  matrix field with continuous entries is a uniformly bounded operator on the
  open cube.
* `matFieldMulClass`, `lipschitz_matFieldMulClass`,
  `continuous_matFieldMulClass`: multiplication by such a field, read on `L²`
  classes.
* `measurable_norm_toHilbertVectorL2OfVecField_matVecMul`: the `L²(U)` norm of
  the product is measurable in the parameter, for any measurable parameter.
* `measurable_prod_coefficientCutoff_sub`,
  `continuous_coefficientCutoff_sub_entry`,
  `memVectorL2_matVecMul_coefficientCutoff_sub`: the cutoff-difference
  coefficient field `a_{L₁} − a_{L₂} = k_{L₁} − k_{L₂}` is a Caratheodory
  matrix field whose flux preserves `L²` on a cube.
* `aemeasurable_vecCubeLpENorm_matVecMul_coefficientCutoff_sub_grad`:
  the measurability of the observable of `l.RHS.term2`, for every selection of
  the Dirichlet response and every measure on the shell-sequence carrier.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Pointwise bounds -/

/-- The squared Euclidean length of `A v` is at most the sum of the squared
row lengths of `A` times the squared Euclidean length of `v`. -/
theorem vecNormSq_matVecMul_le_rowSum (A : Mat d) (v : Vec d) :
    vecNormSq (matVecMul A v) ≤ (∑ i : Fin d, vecNormSq (fun j => A i j)) * vecNormSq v := by
  have hrow : ∀ i : Fin d, (matVecMul A v i) ^ 2 ≤
      vecNormSq (fun j => A i j) * vecNormSq v := by
    intro i
    have hdot : matVecMul A v i = vecDot (fun j => A i j) v := rfl
    rw [hdot]
    exact sq_vecDot_le_vecNormSq_mul_vecNormSq _ _
  have hsum : vecNormSq (matVecMul A v) = ∑ i : Fin d, (matVecMul A v i) ^ 2 := by
    simp only [vecNormSq, vecDot, pow_two]
  rw [hsum, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => hrow i

/-- A matrix field with continuous entries is uniformly bounded as an operator
on the open cube: the cube sits inside a compact closed ball. -/
theorem exists_matVecMul_bound_openCubeSet (Q : TriadicCube d) {A : Vec d → Mat d}
    (hA : ∀ i j, Continuous fun x => A x i j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ openCubeSet Q, ∀ v : Vec d,
      vecNormSq (matVecMul (A x) v) ≤ C ^ 2 * vecNormSq v := by
  have hcont : Continuous fun x : Vec d => ∑ i : Fin d, vecNormSq (fun j => A x i j) := by
    refine continuous_finsetSum _ fun i _ => ?_
    simp only [vecNormSq, vecDot]
    exact continuous_finsetSum _ fun j _ => (hA i j).mul (hA i j)
  have hsub : openCubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
    rw [← ball_cubeCenter_eq_openCubeSet Q]
    exact Metric.ball_subset_closedBall
  have hK : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    ProperSpace.isCompact_closedBall _ _
  have hbdd : BddAbove
      ((fun x : Vec d => ∑ i : Fin d, vecNormSq (fun j => A x i j)) ''
        Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    hK.bddAbove_image hcont.continuousOn
  set M : ℝ := sSup ((fun x : Vec d => ∑ i : Fin d, vecNormSq (fun j => A x i j)) ''
    Metric.closedBall (cubeCenter Q) (cubeRadius Q)) with hMdef
  refine ⟨Real.sqrt (max M 0), Real.sqrt_nonneg _, fun x hx v => ?_⟩
  have hle : ∑ i : Fin d, vecNormSq (fun j => A x i j) ≤ M :=
    le_csSup hbdd (Set.mem_image_of_mem _ (hsub hx))
  have hsq : Real.sqrt (max M 0) ^ 2 = max M 0 :=
    Real.sq_sqrt (le_max_right _ _)
  have hv : 0 ≤ vecNormSq v := vecNormSq_nonneg v
  calc vecNormSq (matVecMul (A x) v)
      ≤ (∑ i : Fin d, vecNormSq (fun j => A x i j)) * vecNormSq v :=
        vecNormSq_matVecMul_le_rowSum (A x) v
    _ ≤ max M 0 * vecNormSq v := by
        exact mul_le_mul_of_nonneg_right (le_trans hle (le_max_left _ _)) hv
    _ = Real.sqrt (max M 0) ^ 2 * vecNormSq v := by rw [hsq]

/-! ## The `L²` norm bound for multiplication by a bounded matrix field -/

/-- Two `L²` witnesses of almost-everywhere equal fields give the same class. -/
theorem toHilbertVectorL2OfVecField_congr {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g)
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    toHilbertVectorL2OfVecField hf = toHilbertVectorL2OfVecField hg := by
  refine (toHilbertVectorL2_eq_toHilbertVectorL2_iff
    (memHilbertVectorL2_hilbertifyVecField hf)
    (memHilbertVectorL2_hilbertifyVecField hg)).2 ?_
  filter_upwards [hfg] with x hx
  exact congrArg HilbertVec.ofVec hx

/-- The plain representative of the class of a field agrees with the field
almost everywhere. -/
theorem hilbertClassField_toHilbertVectorL2OfVecField {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    hilbertClassField (toHilbertVectorL2OfVecField hf) =ᵐ[volumeMeasureOn U] f := by
  have hrep : hilbertClassField (toHilbertVectorL2OfVecField hf) =
      ((toVectorL2 hf : VectorL2 U) : Vec d → Vec d) := by
    rw [hilbertClassField, hilbertVectorL2ToVectorL2_toHilbertVectorL2 hf]
  rw [hrep]
  exact coeFn_toVectorL2 hf

/-- **Multiplication by a bounded matrix field is bounded on `L²(U; ℝ^d)`.** -/
theorem norm_toHilbertVectorL2OfVecField_matVecMul_le {U : Set (Vec d)}
    (hU : MeasurableSet U) {A : Vec d → Mat d} {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ x ∈ U, ∀ v : Vec d, vecNormSq (matVecMul (A x) v) ≤ C ^ 2 * vecNormSq v)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f)
    (hAf : MemVectorL2 U (fun x => matVecMul (A x) (f x))) :
    ‖toHilbertVectorL2OfVecField hAf‖ ≤ C * ‖toHilbertVectorL2OfVecField hf‖ := by
  refine MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards
    [coeFn_toHilbertVectorL2OfVecField (U := U)
      (f := fun x => matVecMul (A x) (f x)) hAf,
     coeFn_toHilbertVectorL2OfVecField (U := U) (f := f) hf,
     MeasureTheory.ae_restrict_mem hU] with x hAx hfx hxU
  rw [hAx, hfx]
  show ‖HilbertVec.ofVec (matVecMul (A x) (f x))‖ ≤ C * ‖HilbertVec.ofVec (f x)‖
  have hsq : ‖HilbertVec.ofVec (matVecMul (A x) (f x))‖ ^ 2 ≤
      (C * ‖HilbertVec.ofVec (f x)‖) ^ 2 := by
    have h1 : ‖HilbertVec.ofVec (matVecMul (A x) (f x))‖ ^ 2 =
        vecNormSq (matVecMul (A x) (f x)) := HilbertVec.norm_sq_ofVec _
    have h2 : ‖HilbertVec.ofVec (f x)‖ ^ 2 = vecNormSq (f x) := HilbertVec.norm_sq_ofVec _
    have h3 : (C * ‖HilbertVec.ofVec (f x)‖) ^ 2 = C ^ 2 * vecNormSq (f x) := by
      rw [mul_pow, h2]
    rw [h1, h3]
    exact hbd x hxU (f x)
  have hrhs : 0 ≤ C * ‖HilbertVec.ofVec (f x)‖ := mul_nonneg hC (norm_nonneg _)
  have habs : |‖HilbertVec.ofVec (matVecMul (A x) (f x))‖| ≤
      |C * ‖HilbertVec.ofVec (f x)‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs] at habs


/-! ## Multiplication as a map of `L²` classes -/

section Multiplication

variable {U : Set (Vec d)}

/-- `matVecMul` is additive in the vector slot under subtraction. -/
private theorem matVecMul_sub' (A : Mat d) (v w : Vec d) :
    matVecMul A (v - w) = matVecMul A v - matVecMul A w := by
  funext i
  simp only [matVecMul, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Multiplication of an `L²(U; ℝ^d)` class by a matrix field, read on the
plain representative of the class. -/
def matFieldMulClass (A : Vec d → Mat d)
    (hmul : ∀ f : Vec d → Vec d, MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A x) (f x)))
    (f : HilbertVectorL2 U) : HilbertVectorL2 U :=
  toHilbertVectorL2OfVecField (hmul _ (memVectorL2_hilbertClassField f))

/-- The multiplication map on classes evaluates a field through its class. -/
theorem matFieldMulClass_toHilbertVectorL2OfVecField (A : Vec d → Mat d)
    (hmul : ∀ f : Vec d → Vec d, MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A x) (f x)))
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    matFieldMulClass A hmul (toHilbertVectorL2OfVecField hf) =
      toHilbertVectorL2OfVecField (hmul f hf) := by
  refine toHilbertVectorL2OfVecField_congr _ _ ?_
  filter_upwards [hilbertClassField_toHilbertVectorL2OfVecField hf] with x hx
  rw [hx]

/-- The multiplication map on classes is `C`-Lipschitz. -/
theorem lipschitz_matFieldMulClass (hU : MeasurableSet U) (A : Vec d → Mat d)
    (hmul : ∀ f : Vec d → Vec d, MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A x) (f x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ x ∈ U, ∀ v : Vec d, vecNormSq (matVecMul (A x) v) ≤ C ^ 2 * vecNormSq v)
    (f g : HilbertVectorL2 U) :
    ‖matFieldMulClass A hmul f - matFieldMulClass A hmul g‖ ≤ C * ‖f - g‖ := by
  have hsubmem : MemVectorL2 U (hilbertClassField f - hilbertClassField g) :=
    (memVectorL2_hilbertClassField f).sub (memVectorL2_hilbertClassField g)
  have hdiff : matFieldMulClass A hmul f - matFieldMulClass A hmul g =
      toHilbertVectorL2OfVecField (hmul _ hsubmem) := by
    rw [matFieldMulClass, matFieldMulClass,
      ← toHilbertVectorL2OfVecField_sub (hmul _ (memVectorL2_hilbertClassField f))
        (hmul _ (memVectorL2_hilbertClassField g))]
    refine toHilbertVectorL2OfVecField_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    show matVecMul (A x) (hilbertClassField f x) - matVecMul (A x) (hilbertClassField g x) =
      matVecMul (A x) ((hilbertClassField f - hilbertClassField g) x)
    rw [Pi.sub_apply, matVecMul_sub' (A x)]
  have hbase : toHilbertVectorL2OfVecField hsubmem = f - g := by
    rw [toHilbertVectorL2OfVecField_sub (memVectorL2_hilbertClassField f)
      (memVectorL2_hilbertClassField g), toHilbertVectorL2OfVecField_hilbertClassField,
      toHilbertVectorL2OfVecField_hilbertClassField]
  rw [hdiff, ← hbase]
  exact norm_toHilbertVectorL2OfVecField_matVecMul_le hU hC hbd hsubmem (hmul _ hsubmem)

/-- The multiplication map on classes is continuous. -/
theorem continuous_matFieldMulClass (hU : MeasurableSet U) (A : Vec d → Mat d)
    (hmul : ∀ f : Vec d → Vec d, MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A x) (f x)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ x ∈ U, ∀ v : Vec d, vecNormSq (matVecMul (A x) v) ≤ C ^ 2 * vecNormSq v) :
    Continuous (matFieldMulClass A hmul) := by
  refine LipschitzWith.continuous (K := C.toNNReal) (LipschitzWith.of_dist_le_mul ?_)
  intro f g
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal C hC]
  exact lipschitz_matFieldMulClass hU A hmul hC hbd f g

end Multiplication


/-! ## Joint measurability of the multiplication observable -/

section JointMeasurability

variable {alpha : Type*} [MeasurableSpace alpha]

/-- A representative of a Hilbert `L²` class is measurable. -/
theorem measurable_hilbertClassField {U : Set (Vec d)} (f : HilbertVectorL2 U) :
    Measurable (hilbertClassField f) :=
  (MeasureTheory.AEEqFun.stronglyMeasurable
    ((hilbertVectorL2ToVectorL2 (U := U) f : VectorL2 U) :
      Vec d →ₘ[volumeMeasureOn U] Vec d)).measurable

/-- The `L²` norm of a class is the square root of the integral of the squared
Euclidean length of any representative. -/
theorem norm_toHilbertVectorL2OfVecField_eq_sqrt {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    ‖toHilbertVectorL2OfVecField hf‖ =
      Real.sqrt (∫ x in U, vecDot (f x) (f x) ∂MeasureTheory.volume) := by
  conv_lhs => rw [← Real.sqrt_sq (norm_nonneg (toHilbertVectorL2OfVecField hf))]
  congr 1
  rw [← real_inner_self_eq_norm_sq]
  exact inner_toHilbertVectorL2OfVecField_eq_integral _ _

/-- The set integral of the pairing of two jointly measurable fields is
measurable in the parameter. -/
theorem measurable_setIntegral_vecDot_prod (U : Set (Vec d))
    {G H : alpha × Vec d → Vec d} (hG : Measurable G) (hH : Measurable H) :
    Measurable (fun a : alpha =>
      ∫ x in U, vecDot (G (a, x)) (H (a, x)) ∂MeasureTheory.volume) := by
  have hjoint : Measurable (fun q : alpha × Vec d => vecDot (G q) (H q)) := by
    show Measurable fun q : alpha × Vec d => ∑ i, G q i * H q i
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((measurable_pi_apply i).comp hG).mul ((measurable_pi_apply i).comp hH)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- Joint measurability of a matrix field applied to a fixed measurable field. -/
private theorem measurable_prod_matVecMul (A : alpha → Vec d → Mat d)
    (hA : Measurable fun q : alpha × Vec d => A q.1 q.2)
    {g : Vec d → Vec d} (hg : Measurable g) :
    Measurable (fun q : alpha × Vec d => matVecMul (A q.1 q.2) (g q.2)) := by
  refine Measurable.of_eval fun i => ?_
  show Measurable fun q : alpha × Vec d => ∑ j, A q.1 q.2 i j * g q.2 j
  refine Finset.measurable_sum _ fun j _ => ?_
  have hAij : Measurable fun q : alpha × Vec d => A q.1 q.2 i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  exact hAij.mul ((measurable_pi_apply j).comp (hg.comp measurable_snd))

/-- The multiplication observable at a fixed class is measurable in the
parameter. -/
private theorem measurable_norm_matFieldMulClass_apply {U : Set (Vec d)}
    (A : alpha → Vec d → Mat d)
    (hA : Measurable fun q : alpha × Vec d => A q.1 q.2)
    (hmul : ∀ (a : alpha) (f : Vec d → Vec d), MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A a x) (f x)))
    (f : HilbertVectorL2 U) :
    Measurable (fun a : alpha => ‖matFieldMulClass (A a) (hmul a) f‖) := by
  have hval : (fun a : alpha => ‖matFieldMulClass (A a) (hmul a) f‖) =
      fun a : alpha => Real.sqrt
        (∫ x in U, vecDot (matVecMul (A a x) (hilbertClassField f x))
          (matVecMul (A a x) (hilbertClassField f x)) ∂MeasureTheory.volume) := by
    funext a
    exact norm_toHilbertVectorL2OfVecField_eq_sqrt
      (hmul a _ (memVectorL2_hilbertClassField f))
  rw [hval]
  exact Real.continuous_sqrt.measurable.comp
    (measurable_setIntegral_vecDot_prod U
      (measurable_prod_matVecMul A hA (measurable_hilbertClassField f))
      (measurable_prod_matVecMul A hA (measurable_hilbertClassField f)))

omit [MeasurableSpace alpha] in
/-- The multiplication observable is continuous in the class at a fixed
parameter. -/
private theorem continuous_norm_matFieldMulClass {U : Set (Vec d)}
    (hU : MeasurableSet U) (A : alpha → Vec d → Mat d)
    (hmul : ∀ (a : alpha) (f : Vec d → Vec d), MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A a x) (f x)))
    (hbd : ∀ a : alpha, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Vec d,
      vecNormSq (matVecMul (A a x) v) ≤ C ^ 2 * vecNormSq v)
    (a : alpha) :
    Continuous (fun f : HilbertVectorL2 U => ‖matFieldMulClass (A a) (hmul a) f‖) := by
  obtain ⟨C, hC, hCbd⟩ := hbd a
  exact continuous_norm.comp (continuous_matFieldMulClass hU (A a) (hmul a) hC hCbd)

/-- **The multiplication observable is measurable in the parameter.**  For a
matrix field jointly measurable in the parameter and the point, uniformly
bounded on `U` at every parameter, and a measurable family of `L²(U)` classes,
the `L²(U)` norm of the product is a measurable function of the parameter. -/
theorem measurable_norm_toHilbertVectorL2OfVecField_matVecMul {U : Set (Vec d)}
    (hU : MeasurableSet U) (A : alpha → Vec d → Mat d)
    (hA : Measurable fun q : alpha × Vec d => A q.1 q.2)
    (hmul : ∀ (a : alpha) (f : Vec d → Vec d), MemVectorL2 U f →
      MemVectorL2 U (fun x => matVecMul (A a x) (f x)))
    (hbd : ∀ a : alpha, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U, ∀ v : Vec d,
      vecNormSq (matVecMul (A a x) v) ≤ C ^ 2 * vecNormSq v)
    {G : alpha → Vec d → Vec d} (hG : ∀ a : alpha, MemVectorL2 U (G a))
    (hGclass : Measurable fun a : alpha => toHilbertVectorL2OfVecField (hG a)) :
    Measurable fun a : alpha => ‖toHilbertVectorL2OfVecField (hmul a (G a) (hG a))‖ := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have huncurry : Measurable (Function.uncurry
      (fun (f : HilbertVectorL2 U) (a : alpha) => ‖matFieldMulClass (A a) (hmul a) f‖)) :=
    measurable_uncurry_of_continuous_of_measurable
      (continuous_norm_matFieldMulClass hU A hmul hbd)
      (measurable_norm_matFieldMulClass_apply A hA hmul)
  have hpair : Measurable fun a : alpha => (toHilbertVectorL2OfVecField (hG a), a) :=
    hGclass.prodMk measurable_id
  have hcomp := huncurry.comp hpair
  have hfun : (Function.uncurry
        (fun (f : HilbertVectorL2 U) (a : alpha) => ‖matFieldMulClass (A a) (hmul a) f‖)) ∘
      (fun a : alpha => (toHilbertVectorL2OfVecField (hG a), a)) =
      fun a : alpha => ‖toHilbertVectorL2OfVecField (hmul a (G a) (hG a))‖ := by
    funext a
    exact congrArg norm
      (matFieldMulClass_toHilbertVectorL2OfVecField (A a) (hmul a) (hG a))
  rwa [hfun] at hcomp

end JointMeasurability


/-! ## The cutoff-difference coefficient field -/

section CutoffDifference

/-- The stream cutoff is jointly measurable in the sample and the point,
entrywise. -/
private theorem measurable_prod_streamCutoff_entry (L : ℕ) (i j : Fin d) :
    Measurable (fun q : ShellSeq d × Vec d => streamCutoff q.1 L q.2 i j) := by
  have h : Measurable (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
      streamCutoff omega L x i j)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun omega => (continuous_apply j).comp
        ((continuous_apply i).comp (continuous_streamCutoff_apply omega L)))
      (fun x => (measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp (measurable_streamCutoff_apply L x)))
  have hcomp : (fun q : ShellSeq d × Vec d => streamCutoff q.1 L q.2 i j) =
      (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
        streamCutoff omega L x i j)) ∘ Prod.swap := rfl
  rw [hcomp]
  exact h.comp measurable_swap

/-- The difference of two cutoff coefficient fields is the difference of the
two stream cutoffs: the constant `ν Id` cancels. -/
theorem coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub (nu : ℝ)
    (omega : ShellSeq d) (L1 L2 : ℕ) (x : Vec d) :
    (coefficientCutoff nu omega L1).toCoeffField x -
        (coefficientCutoff nu omega L2).toCoeffField x =
      streamCutoff omega L1 x - streamCutoff omega L2 x := by
  simp only [coefficientCutoff_toCoeffField_apply]
  abel

/-- **The cutoff-difference coefficient field is jointly measurable** in the
sample and the point. -/
theorem measurable_prod_coefficientCutoff_sub (nu : ℝ) (L1 L2 : ℕ) :
    Measurable (fun q : ShellSeq d × Vec d =>
      (coefficientCutoff nu q.1 L1).toCoeffField q.2 -
        (coefficientCutoff nu q.1 L2).toCoeffField q.2) := by
  have hfun : (fun q : ShellSeq d × Vec d =>
      (coefficientCutoff nu q.1 L1).toCoeffField q.2 -
        (coefficientCutoff nu q.1 L2).toCoeffField q.2) =
      fun q : ShellSeq d × Vec d => streamCutoff q.1 L1 q.2 - streamCutoff q.1 L2 q.2 := by
    funext q
    exact coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub nu q.1 L1 L2 q.2
  rw [hfun]
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  exact (measurable_prod_streamCutoff_entry L1 i j).sub
    (measurable_prod_streamCutoff_entry L2 i j)

/-- The cutoff-difference coefficient field has continuous entries. -/
theorem continuous_coefficientCutoff_sub_entry (nu : ℝ) (omega : ShellSeq d)
    (L1 L2 : ℕ) (i j : Fin d) :
    Continuous fun x : Vec d =>
      ((coefficientCutoff nu omega L1).toCoeffField x -
        (coefficientCutoff nu omega L2).toCoeffField x) i j := by
  have hfun : (fun x : Vec d =>
      ((coefficientCutoff nu omega L1).toCoeffField x -
        (coefficientCutoff nu omega L2).toCoeffField x) i j) =
      fun x : Vec d => streamCutoff omega L1 x i j - streamCutoff omega L2 x i j := by
    funext x
    rw [coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub nu omega L1 L2 x]
    rfl
  rw [hfun]
  exact ((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_streamCutoff_apply omega L1))).sub
    ((continuous_apply j).comp
      ((continuous_apply i).comp (continuous_streamCutoff_apply omega L2)))

/-- The cutoff-difference flux of an `L²` field on a triadic cube is `L²`. -/
theorem memVectorL2_matVecMul_coefficientCutoff_sub {nu : ℝ} (hnu : 0 < nu)
    (omega : ShellSeq d) (L1 L2 : ℕ) (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MemVectorL2 (openCubeSet Q) f) :
    MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul ((coefficientCutoff nu omega L1).toCoeffField x -
        (coefficientCutoff nu omega L2).toCoeffField x) (f x)) := by
  have hA := Terms.memVectorL2_matVecMul_coefficientCutoff hnu omega L1 Q hf
  have hB := Terms.memVectorL2_matVecMul_coefficientCutoff hnu omega L2 Q hf
  have hsplit : (fun x => matVecMul ((coefficientCutoff nu omega L1).toCoeffField x -
      (coefficientCutoff nu omega L2).toCoeffField x) (f x)) =
      fun x => matVecMul ((coefficientCutoff nu omega L1).toCoeffField x) (f x) -
        matVecMul ((coefficientCutoff nu omega L2).toCoeffField x) (f x) := by
    funext x
    exact sub_matVecMul _ _ _
  rw [hsplit]
  exact hA.sub hB

end CutoffDifference


/-! ## Measurability of the cutoff-difference observable of `l.RHS.term2` -/

section Obligation

variable [NeZero d]

/-- **Measurability of the cutoff-difference observable.**  The annealed observable
`ω ↦ ‖(a_{L₁}(ω) − a_{L₂}(ω)) ∇w_ω‖_{L̲²(cu_m)}` is `AEMeasurable` for every
selection `w` of the Dirichlet response of `e.def.w`, on every measure of the
shell-sequence carrier.

Choice independence (`aemeasurable_vecCubeLpENorm_matVecMul_grad_of_canonical`)
moves the observable to the canonical response; there the field is the
multiplication of the response gradient class by the cutoff-difference
coefficient field, which is jointly measurable in the sample and the point and
uniformly bounded on the cube at every sample, while the gradient class itself
is measurable in the sample
(`measurable_gradToHilbertVectorL2_dirichletResponse`). -/
theorem aemeasurable_vecCubeLpENorm_matVecMul_coefficientCutoff_sub_grad
    {nu : ℝ} (hnu : 0 < nu) (L1 L2 : ℕ) {LPrime ellPrime m : ℕ} {p : Vec d}
    {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    AEMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (fun y => matVecMul ((coefficientCutoff nu omega L1).toCoeffField y -
            (coefficientCutoff nu omega L2).toCoeffField y)
          ((w omega).toH1Function.grad y))) mu := by
  refine aemeasurable_vecCubeLpENorm_matVecMul_grad_of_canonical 2
    (fun omega y => (coefficientCutoff nu omega L1).toCoeffField y -
      (coefficientCutoff nu omega L2).toCoeffField y) hw ?_
  have hU : MeasurableSet (openCubeSet (originCube d (m : ℤ))) :=
    (isOpen_openCubeSet (originCube d (m : ℤ))).measurableSet
  have hmul : ∀ (omega : ShellSeq d) (f : Vec d → Vec d),
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) f →
      MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
        (fun y => matVecMul ((coefficientCutoff nu omega L1).toCoeffField y -
          (coefficientCutoff nu omega L2).toCoeffField y) (f y)) :=
    fun omega _ hf =>
      memVectorL2_matVecMul_coefficientCutoff_sub hnu omega L1 L2 (originCube d (m : ℤ)) hf
  have hG : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet (originCube d (m : ℤ)))
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad :=
    fun omega => (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad_memVectorL2
  have hGclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hG omega) :=
    measurable_gradToHilbertVectorL2_dirichletResponse
  have hbd : ∀ omega : ShellSeq d, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ openCubeSet (originCube d (m : ℤ)), ∀ v : Vec d,
      vecNormSq (matVecMul ((coefficientCutoff nu omega L1).toCoeffField x -
        (coefficientCutoff nu omega L2).toCoeffField x) v) ≤ C ^ 2 * vecNormSq v :=
    fun omega => exists_matVecMul_bound_openCubeSet (originCube d (m : ℤ))
      (fun i j => continuous_coefficientCutoff_sub_entry nu omega L1 L2 i j)
  have hmeas : Measurable fun omega : ShellSeq d =>
      ‖toHilbertVectorL2OfVecField (hmul omega _ (hG omega))‖ :=
    measurable_norm_toHilbertVectorL2OfVecField_matVecMul hU _
      (measurable_prod_coefficientCutoff_sub nu L1 L2) hmul hbd hG hGclass
  have hfun : (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (fun y => matVecMul ((coefficientCutoff nu omega L1).toCoeffField y -
            (coefficientCutoff nu omega L2).toCoeffField y)
          ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad y))) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal ((cubeVolume (originCube d (m : ℤ)))⁻¹) ^
            ((1 : ENNReal) / 2).toReal *
          ENNReal.ofReal ‖toHilbertVectorL2OfVecField (hmul omega _ (hG omega))‖ := by
    funext omega
    rw [vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField (hmul omega _ (hG omega)),
      ofReal_norm]
  rw [hfun]
  exact AEMeasurable.const_mul
    ((ENNReal.measurable_ofReal.comp hmeas).aemeasurable) _

end Obligation


end

end SuperdiffusionCLT.Section3.Setup
