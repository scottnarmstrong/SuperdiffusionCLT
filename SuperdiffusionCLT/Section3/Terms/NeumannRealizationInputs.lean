/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB

/-!
# The Neumann energy observables are measurable in the sample

`ResponseMeasurability.lean` and `ResponseMeasurabilityB.lean` solve the
Dirichlet half of the cube-energy measurability obligation of `l.LHS.term1`:
two Dirichlet responses of the same flux have the same weak-gradient `L²` class
(`gradToVectorL2_eq_of_isCubeDirichletResponse`), the response gradient class is
a `1`-Lipschitz function of the flux class
(`norm_gradToHilbertVectorL2_sub_le_of_isCubeDirichletResponse`), so the
solution operator `cubeDirichletGradClass` is continuous, and the flux class of
`e.def.w` is measurable in the sample
(`measurable_toHilbertVectorL2OfVecField_dirichletRhsField`).  The present
module runs the same argument for the **prescribed-flux Neumann** problem.

The obstruction one might expect — that the Neumann response lives in
`H1MeanZeroFunction`, the zero-average `H¹` carrier, rather than in the
zero-trace `H10Function` of the Dirichlet problem — is not an obstruction.
`IsCubeNeumannResponse` tests against the whole mean-zero `H¹` carrier
(`Section3/ResponseFields/Definitions.lean`), and that carrier is closed under
subtraction (`H1MeanZeroFunction.toH1Function_sub`), so the difference of two
Neumann responses is again an admissible test function and the elliptic
stability identity goes through verbatim.  The uniqueness input
`gradToVectorL2_eq_of_isCubeNeumannResponse` is proved alongside its Dirichlet
twin.

## Main results

* `norm_gradToHilbertVectorL2_sub_le_of_isCubeNeumannResponse`: the Neumann
  response gradient class is a `1`-Lipschitz function of the flux class, for
  *every* realization of `IsCubeNeumannResponse`.
* `isCubeNeumannResponse_congr_ae`,
  `gradToHilbertVectorL2_eq_of_isCubeNeumannResponse_ae`: the response predicate
  and the gradient class depend on the flux only through its `L²` class.
* `cubeNeumannGradClass`, `cubeNeumannGradClass_eq_of_isCubeNeumannResponse`,
  `lipschitzWith_cubeNeumannGradClass`, `continuous_cubeNeumannGradClass`: the
  Neumann solution operator and its characterization.
* `measurable_gradToHilbertVectorL2_neumannResponse`: the gradient class of
  *every* selection of the Neumann response of `e.def.w` is a measurable
  function of the sample.
* `aestronglyMeasurable_vecCubeLpENorm_grad_neumann` and
  `aesm_vecCubeLpENorm_grad_neumann_of_fluxFormula`: the `AEStronglyMeasurable`
  cube-energy obligation of the `l.LHS.term1` chain, discharged for the
  Neumann response.  This is the hypothesis `hNmeas` of
  `SuperdiffusionCLT.Section3.Terms.lhs_sandwich_of_neumannMeas_of_realization`
  and of the `hData` residue of the master assembly, proved with
  no remaining hypothesis beyond the concrete flux of the defining clause.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Stability of the Neumann response in the forcing -/

section Stability

/-- `vecDot` is additive in the left slot under subtraction. -/
private theorem vecDot_sub_left_neumann (a b c : Vec d) :
    vecDot (a - b) c = vecDot a c - vecDot b c := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The weak gradient of a difference of mean-zero `H¹` functions.  The carrier
`H1MeanZeroFunction` is closed under subtraction, and its coercion to
`H1Function` is the `H1Function` subtraction, so this is
`H1Function.sub_grad` read on the mean-zero layer. -/
private theorem grad_sub_apply_neumann (Q : TriadicCube d)
    (w w' : H1MeanZeroFunction (openCubeSet Q)) (x : Vec d) :
    (w - w').toH1Function.grad x =
      w.toH1Function.grad x - w'.toH1Function.grad x := by
  change (w.toH1Function - w'.toH1Function).grad x = _
  exact congrFun (H1Function.sub_grad w.toH1Function w'.toH1Function) x

/-- **The energy identity for the difference of two cube Neumann responses.**
Testing the difference of the two weak equations against the difference itself,
which is mean-zero and hence admissible for the enlarged Neumann test class,
turns the cube energy of `∇w − ∇w'` into the pairing of the difference of the
flux fields with that same gradient. -/
private theorem integral_vecNormSq_grad_sub_eq_neg_pairing_neumann {Q : TriadicCube d}
    {F F' : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (hF' : MemVectorL2 (openCubeSet Q) F')
    {w w' : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w)
    (hw' : IsCubeNeumannResponse Q F' w') :
    ∫ x in openCubeSet Q,
        vecNormSq (w.toH1Function.grad x - w'.toH1Function.grad x)
          ∂MeasureTheory.volume =
      -∫ x in openCubeSet Q, vecDot (F x - F' x)
          (w.toH1Function.grad x - w'.toH1Function.grad x) ∂MeasureTheory.volume := by
  obtain ⟨u, hu⟩ : ∃ u : H1MeanZeroFunction (openCubeSet Q), u = w - w' := ⟨w - w', rfl⟩
  have hgrad : ∀ x : Vec d, u.toH1Function.grad x =
      w.toH1Function.grad x - w'.toH1Function.grad x := by
    intro x
    rw [hu]
    exact grad_sub_apply_neumann Q w w' x
  have hgu : MemVectorL2 (openCubeSet Q) u.toH1Function.grad :=
    u.toH1Function.grad_memVectorL2
  have hiw : MeasureTheory.IntegrableOn
      (fun x => vecDot (w.toH1Function.grad x) (u.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2 hgu
  have hiw' : MeasureTheory.IntegrableOn
      (fun x => vecDot (w'.toH1Function.grad x) (u.toH1Function.grad x))
      (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 w'.toH1Function.grad_memVectorL2 hgu
  have hiF : MeasureTheory.IntegrableOn
      (fun x => vecDot (F x) (u.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF hgu
  have hiF' : MeasureTheory.IntegrableOn
      (fun x => vecDot (F' x) (u.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF' hgu
  have hsplit : ∫ x in openCubeSet Q,
        vecNormSq (w.toH1Function.grad x - w'.toH1Function.grad x)
          ∂MeasureTheory.volume =
      (∫ x in openCubeSet Q,
          vecDot (w.toH1Function.grad x) (u.toH1Function.grad x)
            ∂MeasureTheory.volume) -
        ∫ x in openCubeSet Q,
          vecDot (w'.toH1Function.grad x) (u.toH1Function.grad x)
            ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_sub hiw hiw']
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [← vecDot_sub_left_neumann, ← hgrad x]
    rfl
  have hsplitF : (∫ x in openCubeSet Q,
          vecDot (F x) (u.toH1Function.grad x) ∂MeasureTheory.volume) -
        ∫ x in openCubeSet Q,
          vecDot (F' x) (u.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, vecDot (F x - F' x)
          (u.toH1Function.grad x) ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_sub hiF hiF']
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    exact (vecDot_sub_left_neumann _ _ _).symm
  have hgoal : ∫ x in openCubeSet Q, vecDot (F x - F' x)
          (w.toH1Function.grad x - w'.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, vecDot (F x - F' x)
          (u.toH1Function.grad x) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [hgrad x]
  rw [hsplit, hw u, hw' u, hgoal, ← hsplitF]
  ring

/-- The Young step.  If the cube energy of `B` is the negative pairing of `B`
with `A`, then it is bounded by the cube energy of `A`. -/
private theorem integral_vecNormSq_le_of_eq_neg_pairing_neumann {U : Set (Vec d)}
    {A B : Vec d → Vec d} (hA : MemVectorL2 U A) (hB : MemVectorL2 U B)
    (h : (∫ x in U, vecNormSq (B x) ∂MeasureTheory.volume) =
      -∫ x in U, vecDot (A x) (B x) ∂MeasureTheory.volume) :
    (∫ x in U, vecNormSq (B x) ∂MeasureTheory.volume) ≤
      ∫ x in U, vecNormSq (A x) ∂MeasureTheory.volume := by
  have hiAB : MeasureTheory.IntegrableOn (fun x => vecDot (A x) (B x)) U :=
    integrableOn_vecDot_of_memVectorL2 hA hB
  have hiA : MeasureTheory.IntegrableOn (fun x => vecNormSq (A x)) U :=
    integrableOn_vecDot_of_memVectorL2 hA hA
  have hiB : MeasureTheory.IntegrableOn (fun x => vecNormSq (B x)) U :=
    integrableOn_vecDot_of_memVectorL2 hB hB
  have hyoung : (∫ x in U, |vecDot (A x) (B x)| ∂MeasureTheory.volume) ≤
      ∫ x in U, (vecNormSq (A x) / 2 + vecNormSq (B x) / 2) ∂MeasureTheory.volume :=
    MeasureTheory.integral_mono_ae hiAB.abs ((hiA.div_const 2).add (hiB.div_const 2))
      (Filter.Eventually.of_forall fun x =>
        abs_vecDot_le_add_halves_vecNormSq (A x) (B x))
  have hsplit : (∫ x in U, (vecNormSq (A x) / 2 + vecNormSq (B x) / 2)
        ∂MeasureTheory.volume) =
      (∫ x in U, vecNormSq (A x) ∂MeasureTheory.volume) / 2 +
        (∫ x in U, vecNormSq (B x) ∂MeasureTheory.volume) / 2 := by
    rw [MeasureTheory.integral_add (hiA.div_const 2) (hiB.div_const 2),
      MeasureTheory.integral_div, MeasureTheory.integral_div]
  have hkey : (∫ x in U, vecNormSq (B x) ∂MeasureTheory.volume) ≤
      (∫ x in U, vecNormSq (A x) ∂MeasureTheory.volume) / 2 +
        (∫ x in U, vecNormSq (B x) ∂MeasureTheory.volume) / 2 :=
    calc (∫ x in U, vecNormSq (B x) ∂MeasureTheory.volume)
        = -∫ x in U, vecDot (A x) (B x) ∂MeasureTheory.volume := h
      _ ≤ |∫ x in U, vecDot (A x) (B x) ∂MeasureTheory.volume| := neg_le_abs _
      _ ≤ ∫ x in U, |vecDot (A x) (B x)| ∂MeasureTheory.volume :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ x in U, (vecNormSq (A x) / 2 + vecNormSq (B x) / 2)
            ∂MeasureTheory.volume := hyoung
      _ = (∫ x in U, vecNormSq (A x) ∂MeasureTheory.volume) / 2 +
            (∫ x in U, vecNormSq (B x) ∂MeasureTheory.volume) / 2 := hsplit
  linarith only [hkey]

/-- **Stability of the cube Neumann response in the forcing.**  The cube energy
of the difference of two Neumann response gradients is bounded by the cube
energy of the difference of the two flux fields.  No selection is involved: the
bound holds for every realization of `IsCubeNeumannResponse` at either flux.
This is the Neumann twin of
`integral_vecNormSq_grad_sub_le_of_isCubeDirichletResponse`. -/
theorem integral_vecNormSq_grad_sub_le_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F F' : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (hF' : MemVectorL2 (openCubeSet Q) F')
    {w w' : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w)
    (hw' : IsCubeNeumannResponse Q F' w') :
    ∫ x in openCubeSet Q,
        vecNormSq (w.toH1Function.grad x - w'.toH1Function.grad x)
          ∂MeasureTheory.volume ≤
      ∫ x in openCubeSet Q, vecNormSq (F x - F' x) ∂MeasureTheory.volume :=
  integral_vecNormSq_le_of_eq_neg_pairing_neumann (hF.sub hF')
    (w.toH1Function.grad_memVectorL2.sub w'.toH1Function.grad_memVectorL2)
    (integral_vecNormSq_grad_sub_eq_neg_pairing_neumann hF hF' hw hw')

/-- The squared `HilbertVectorL2(U)` norm of a square-integrable field is its
Euclidean energy. -/
private theorem norm_sq_toHilbertVectorL2OfVecField_neumann {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    ‖toHilbertVectorL2OfVecField hf‖ ^ 2 =
      ∫ x in U, vecNormSq (f x) ∂MeasureTheory.volume := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_toHilbertVectorL2OfVecField_eq_integral hf hf

/-- **Stability in the `HilbertVectorL2(Q)` norm.**  The cube Neumann response
gradient class is a `1`-Lipschitz function of the flux class. -/
theorem norm_gradToHilbertVectorL2_sub_le_of_isCubeNeumannResponse
    {Q : TriadicCube d} {F F' : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (hF' : MemVectorL2 (openCubeSet Q) F')
    {w w' : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w)
    (hw' : IsCubeNeumannResponse Q F' w') :
    ‖w.toH1Function.gradToHilbertVectorL2 -
        w'.toH1Function.gradToHilbertVectorL2‖ ≤
      ‖toHilbertVectorL2OfVecField hF - toHilbertVectorL2OfVecField hF'‖ := by
  have hgrad : w.toH1Function.gradToHilbertVectorL2 -
      w'.toH1Function.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField
        (w.toH1Function.grad_memVectorL2.sub w'.toH1Function.grad_memVectorL2) :=
    (toHilbertVectorL2OfVecField_sub w.toH1Function.grad_memVectorL2
      w'.toH1Function.grad_memVectorL2).symm
  have hflux : toHilbertVectorL2OfVecField hF - toHilbertVectorL2OfVecField hF' =
      toHilbertVectorL2OfVecField (hF.sub hF') :=
    (toHilbertVectorL2OfVecField_sub hF hF').symm
  have hsq : ‖w.toH1Function.gradToHilbertVectorL2 -
        w'.toH1Function.gradToHilbertVectorL2‖ ^ 2 ≤
      ‖toHilbertVectorL2OfVecField hF - toHilbertVectorL2OfVecField hF'‖ ^ 2 := by
    rw [hgrad, hflux, norm_sq_toHilbertVectorL2OfVecField_neumann,
      norm_sq_toHilbertVectorL2OfVecField_neumann]
    exact integral_vecNormSq_grad_sub_le_of_isCubeNeumannResponse hF hF' hw hw'
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hroot

end Stability

/-! ## Choice independence for the Neumann response -/

section SelectionFree

/-- The Neumann response predicate only sees the `L²` class of the flux. -/
theorem isCubeNeumannResponse_congr_ae {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G)
    {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w) :
    IsCubeNeumannResponse Q G w := by
  intro phi
  have hint : ∫ x in openCubeSet Q, vecDot (F x) (phi.toH1Function.grad x)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, vecDot (G x) (phi.toH1Function.grad x)
        ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hFG] with x hx
    rw [hx]
  rw [hw phi, hint]

/-- Two Neumann responses of the same flux class have the same gradient class. -/
theorem gradToHilbertVectorL2_eq_of_isCubeNeumannResponse_ae {Q : TriadicCube d}
    {F G : Vec d → Vec d} (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G)
    {w v : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w)
    (hv : IsCubeNeumannResponse Q G v) :
    w.toH1Function.gradToHilbertVectorL2 = v.toH1Function.gradToHilbertVectorL2 :=
  gradToHilbertVectorL2_eq_of_gradToVectorL2_eq
    (gradToVectorL2_eq_of_isCubeNeumannResponse (isCubeNeumannResponse_congr_ae hFG hw) hv)

end SelectionFree

/-! ## The cube Neumann solution operator -/

section Operator

/-- A Neumann response of the representative of a flux class. -/
def cubeNeumannResponseOfClass (Q : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) : H1MeanZeroFunction (openCubeSet Q) :=
  Classical.choose
    (exists_isCubeNeumannResponse Q (memVectorL2_hilbertClassField f))

private theorem isCubeNeumannResponse_cubeNeumannResponseOfClass (Q : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) :
    IsCubeNeumannResponse Q (hilbertClassField f) (cubeNeumannResponseOfClass Q f) :=
  Classical.choose_spec
    (exists_isCubeNeumannResponse Q (memVectorL2_hilbertClassField f))

/-- **The Neumann solution operator of the cube `Q`**: the map sending a flux
class in `L²(Q; ℝ^d)` to the weak-gradient class of the zero-average solution
of the prescribed-flux Neumann problem `−Δw = ∇·F`, `n·(∇w + F) = 0`.  It is
well defined by `cubeNeumannGradClass_eq_of_isCubeNeumannResponse` and
`1`-Lipschitz by `lipschitzWith_cubeNeumannGradClass`. -/
def cubeNeumannGradClass (Q : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) : HilbertVectorL2 (openCubeSet Q) :=
  (cubeNeumannResponseOfClass Q f).toH1Function.gradToHilbertVectorL2

/-- **The characterization of the solution operator.**  Every Neumann response
of a flux field `F` has weak-gradient class `cubeNeumannGradClass Q` applied to
the class of `F`.  In particular the value does not depend on which response,
or which representative of the flux class, was used. -/
theorem cubeNeumannGradClass_eq_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    {w : H1MeanZeroFunction (openCubeSet Q)}
    (hw : IsCubeNeumannResponse Q F w) :
    w.toH1Function.gradToHilbertVectorL2 =
      cubeNeumannGradClass Q (toHilbertVectorL2OfVecField hF) := by
  have hrep : hilbertClassField (toHilbertVectorL2OfVecField hF) =
      ((toVectorL2 hF : VectorL2 (openCubeSet Q)) : Vec d → Vec d) := by
    rw [hilbertClassField, hilbertVectorL2ToVectorL2_toHilbertVectorL2 hF]
  have hae : F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      hilbertClassField (toHilbertVectorL2OfVecField hF) := by
    rw [hrep]
    exact (coeFn_toVectorL2 hF).symm
  exact gradToHilbertVectorL2_eq_of_isCubeNeumannResponse_ae hae hw
    (isCubeNeumannResponse_cubeNeumannResponseOfClass Q _)

/-- **The solution operator is `1`-Lipschitz.**  This is the stability estimate
of this module read on the class space. -/
theorem lipschitzWith_cubeNeumannGradClass (Q : TriadicCube d) :
    LipschitzWith 1 (cubeNeumannGradClass Q) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have h := norm_gradToHilbertVectorL2_sub_le_of_isCubeNeumannResponse
    (memVectorL2_hilbertClassField f) (memVectorL2_hilbertClassField g)
    (isCubeNeumannResponse_cubeNeumannResponseOfClass Q f)
    (isCubeNeumannResponse_cubeNeumannResponseOfClass Q g)
  rwa [toHilbertVectorL2OfVecField_hilbertClassField,
    toHilbertVectorL2OfVecField_hilbertClassField] at h

/-- The solution operator is continuous. -/
theorem continuous_cubeNeumannGradClass (Q : TriadicCube d) :
    Continuous (cubeNeumannGradClass Q) :=
  (lipschitzWith_cubeNeumannGradClass Q).continuous

end Operator

/-! ## The Neumann response of `e.def.w` through the solution operator -/

section Response

variable {LPrime ellPrime m : ℕ} {p : Vec d}

/-- **The Neumann response is the solution operator applied to the flux class
of the sample.**  This holds for every realization of `IsCubeNeumannResponse`,
so the free binder of the Section 3 statements is eliminated. -/
theorem gradToHilbertVectorL2_eq_cubeNeumannGradClass_of_isCubeNeumannResponse
    (omega : ShellSeq d)
    {w : H1MeanZeroFunction (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsCubeNeumannResponse (originCube d (m : ℤ))
        (dirichletRhsField omega LPrime ellPrime p) w) :
    w.toH1Function.gradToHilbertVectorL2 =
      cubeNeumannGradClass (originCube d (m : ℤ))
        (toHilbertVectorL2OfVecField
          (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)) :=
  cubeNeumannGradClass_eq_of_isCubeNeumannResponse
    (memVectorL2_dirichletRhsField omega LPrime ellPrime m p) hw

/-- **The gradient class of every Neumann response of `e.def.w` is measurable in
the sample.**  The response gradient class is the continuous solution operator
applied to the flux class, and the flux class of `e.def.w` is measurable by
`measurable_toHilbertVectorL2OfVecField_dirichletRhsField`; no selection is
involved. -/
theorem measurable_gradToHilbertVectorL2_neumannResponse
    {w : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsCubeNeumannResponse (originCube d (m : ℤ))
        (dirichletRhsField omega LPrime ellPrime p) (w omega)) :
    Measurable (fun omega : ShellSeq d =>
      (w omega).toH1Function.gradToHilbertVectorL2) := by
  have hfun : (fun omega : ShellSeq d =>
      (w omega).toH1Function.gradToHilbertVectorL2) =
      fun omega : ShellSeq d => cubeNeumannGradClass (originCube d (m : ℤ))
        (toHilbertVectorL2OfVecField
          (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)) := by
    funext omega
    exact gradToHilbertVectorL2_eq_cubeNeumannGradClass_of_isCubeNeumannResponse omega
      (hw omega)
  rw [hfun]
  exact (continuous_cubeNeumannGradClass (originCube d (m : ℤ))).measurable.comp
    (measurable_toHilbertVectorL2OfVecField_dirichletRhsField LPrime ellPrime m p)

/-- **The Neumann energy map is measurable in the sample for every selection.**
The cube `L̲²` norm is a fixed constant multiple of the `enorm` of the gradient
class, so this is `measurable_gradToHilbertVectorL2_neumannResponse` read through
a continuous function.  The measure is arbitrary. -/
theorem aestronglyMeasurable_vecCubeLpENorm_grad_neumann
    {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsCubeNeumannResponse (originCube d (m : ℤ))
        (dirichletRhsField omega LPrime ellPrime p) (w omega)) :
    AEStronglyMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) mu := by
  have hmeas := measurable_gradToHilbertVectorL2_neumannResponse (LPrime := LPrime)
    (ellPrime := ellPrime) (m := m) (p := p) hw
  have hfun : (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal ((cubeVolume (originCube d (m : ℤ)))⁻¹) ^
            ((1 : ENNReal) / 2).toReal *
          ‖(w omega).toH1Function.gradToHilbertVectorL2‖ₑ := by
    funext omega
    exact vecCubeLpENorm_grad_eq_enorm_gradToHilbertVectorL2 _
  rw [hfun]
  exact (AEMeasurable.const_mul
    (continuous_enorm.measurable.comp_aemeasurable hmeas.aemeasurable) _).aestronglyMeasurable

/-- **`hNmeas` supplied for the concrete flux of the defining clause.**

This is the `hNmeas` hypothesis of
`SuperdiffusionCLT.Section3.Terms.lhs_sandwich_of_neumannMeas_of_realization`
and of the `hData` residue of the master assembly, proved
outright: the flux field is the concrete `(k_{L'} − k_{ℓ'}) p` of the
binder, so the Neumann energy measurability follows from the solution operator
and the measurability of the flux class alone. -/
theorem aesm_vecCubeLpENorm_grad_neumann_of_fluxFormula
    (S : ScaleSelection) (p : Vec d)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p)
    {mu : MeasureTheory.Measure (ShellSeq d)}
    {wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))}
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega)) :
    AEStronglyMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (wN omega).toH1Function.grad) mu := by
  have hw : ∀ omega : ShellSeq d, IsCubeNeumannResponse (originCube d (S.m : ℤ))
      (dirichletRhsField omega S.LPrime S.ellPrime p) (wN omega) := by
    intro omega
    have heq : dirichletRhsField omega S.LPrime S.ellPrime p = F omega := by
      show (fun x : Vec d => matVecMul
        (streamCutoff omega S.LPrime x - streamCutoff omega S.ellPrime x) p) = F omega
      exact (hF omega).symm
    rw [heq]
    exact hwN omega
  exact aestronglyMeasurable_vecCubeLpENorm_grad_neumann
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m) (p := p) hw

end Response

end

end SuperdiffusionCLT.Section3.Terms
