/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurability

/-!
# The Dirichlet solution operator on a cube

`ResponseMeasurability.lean` shows that every observable of the Dirichlet
response of `e.def.w` is a genuine function of the sample, and that the response
gradient class is a `1`-Lipschitz function of the flux class.  This module turns
that Lipschitz estimate into an honest map.

`cubeDirichletGradClass Q : HilbertVectorL2 (openCubeSet Q) →
HilbertVectorL2 (openCubeSet Q)` sends a flux class to the gradient class of a
Dirichlet response of any of its representatives.  It is well defined
(`cubeDirichletGradClass_eq_of_isCubeDirichletResponse`) because the response
gradient class depends on the flux only through its `L²` class, and it is
`1`-Lipschitz (`lipschitzWith_cubeDirichletGradClass`), hence continuous.

The gradient class of the response of `e.def.w` is therefore
`cubeDirichletGradClass` applied to the flux class of the sample
(`gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse`), so
its measurability follows from the measurability of the flux class alone
(`measurable_gradToHilbertVectorL2_dirichletResponse`), a statement
about the shell data with no partial differential equation in it.  That
statement is then proved outright: the flux field is a Caratheodory function of
the sample and the point (`measurable_uncurry_dirichletRhsField`), the class
space is second countable, and the distance criterion against a countable dense
sequence applies (`measurable_toHilbertVectorL2OfVecField_dirichletRhsField`).

## Main results

* `cubeDirichletGradClass`, `cubeDirichletGradClass_eq_of_isCubeDirichletResponse`,
  `lipschitzWith_cubeDirichletGradClass`, `continuous_cubeDirichletGradClass`.
* `measurable_uncurry_dirichletRhsField`,
  `measurable_toHilbertVectorL2OfVecField_dirichletRhsField`.
* `measurable_gradToHilbertVectorL2_dirichletResponse`: the gradient class of
  the Dirichlet response of `e.def.w` is a measurable function of the sample.
* `aemeasurable_vecCubeLpENorm_grad`,
  `aestronglyMeasurable_vecCubeLpENorm_grad`: the cube-energy map of `e.def.w`
  is measurable in the sample for *every* selection of the response.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The `Vec d`-valued representative of a Hilbert `L²` class -/

/-- The plain vector field underlying a Hilbert-vector `L²` class. -/
def hilbertClassField {U : Set (Vec d)} (f : HilbertVectorL2 U) : Vec d → Vec d :=
  ((hilbertVectorL2ToVectorL2 (U := U) f : VectorL2 U) : Vec d → Vec d)

theorem memVectorL2_hilbertClassField {U : Set (Vec d)} (f : HilbertVectorL2 U) :
    MemVectorL2 U (hilbertClassField f) :=
  MeasureTheory.Lp.memLp _

/-- The representative recovers the class. -/
theorem toHilbertVectorL2OfVecField_hilbertClassField {U : Set (Vec d)}
    (f : HilbertVectorL2 U) :
    toHilbertVectorL2OfVecField (memVectorL2_hilbertClassField f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [coeFn_toHilbertVectorL2OfVecField (U := U) (memVectorL2_hilbertClassField f),
      coeFn_hilbertVectorL2ToVectorL2 (U := U) f] with x h1 h2
  rw [h1]
  show HilbertVec.ofVec (hilbertClassField f x) = f x
  rw [hilbertClassField, h2, HilbertVec.ofVec_toVec]

/-! ## Flux fields with the same class have the same response gradient -/

/-- The Dirichlet response predicate only sees the `L²` class of the flux. -/
theorem isCubeDirichletResponse_congr_ae {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G)
    {w : H10Function (openCubeSet Q)}
    (hw : ResponseFields.IsCubeDirichletResponse Q F w) :
    ResponseFields.IsCubeDirichletResponse Q G w := by
  intro phi
  have hint : ∫ x in openCubeSet Q, vecDot (F x) (phi.toH1Function.grad x)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, vecDot (G x) (phi.toH1Function.grad x)
        ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hFG] with x hx
    rw [hx]
  rw [hw phi, hint]

/-- Two `H¹` functions with the same weak-gradient `L²` class have the same
weak-gradient Hilbert `L²` class. -/
theorem gradToHilbertVectorL2_eq_of_gradToVectorL2_eq {U : Set (Vec d)}
    {u v : H1Function U} (h : u.gradToVectorL2 = v.gradToVectorL2) :
    u.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 := by
  have hu : u.gradToHilbertVectorL2 =
      vectorL2ToHilbertVectorL2 (U := U) u.gradToVectorL2 :=
    (vectorL2ToHilbertVectorL2_toVectorL2 (U := U) u.grad_memVectorL2).symm
  have hv : v.gradToHilbertVectorL2 =
      vectorL2ToHilbertVectorL2 (U := U) v.gradToVectorL2 :=
    (vectorL2ToHilbertVectorL2_toVectorL2 (U := U) v.grad_memVectorL2).symm
  rw [hu, hv, h]

/-- **The response gradient class depends on the flux only through its class.**
-/
theorem gradToHilbertVectorL2_eq_of_isCubeDirichletResponse_ae {Q : TriadicCube d}
    {F G : Vec d → Vec d} (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G)
    {w v : H10Function (openCubeSet Q)}
    (hw : ResponseFields.IsCubeDirichletResponse Q F w)
    (hv : ResponseFields.IsCubeDirichletResponse Q G v) :
    w.toH1Function.gradToHilbertVectorL2 = v.toH1Function.gradToHilbertVectorL2 :=
  gradToHilbertVectorL2_eq_of_gradToVectorL2_eq
    (ResponseFields.gradToVectorL2_eq_of_isCubeDirichletResponse
      (isCubeDirichletResponse_congr_ae hFG hw) hv)

/-! ## Joint measurability of the flux field -/

section Flux

/-- The flux field `(k_{L'} − k_{ℓ'}) p` of `e.def.w` at a fixed point is
measurable in the shell sequence. -/
theorem measurable_dirichletRhsField_apply (LPrime ellPrime : ℕ) (p : Vec d) (x : Vec d) :
    Measurable (fun omega : ShellSeq d =>
      dirichletRhsField omega LPrime ellPrime p x) := by
  refine Measurable.of_eval fun i => ?_
  show Measurable fun omega : ShellSeq d =>
    ∑ j, (streamCutoff omega LPrime x - streamCutoff omega ellPrime x) i j * p j
  refine Finset.measurable_sum _ fun j _ => ?_
  have hL : Measurable fun omega : ShellSeq d => streamCutoff omega LPrime x i j :=
    (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (measurable_streamCutoff_apply LPrime x))
  have hl : Measurable fun omega : ShellSeq d => streamCutoff omega ellPrime x i j :=
    (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (measurable_streamCutoff_apply ellPrime x))
  exact (hL.sub hl).mul_const (p j)

/-- **Joint measurability of the flux field** in the sample and the point: it is
continuous in the point and measurable in the sample, a Caratheodory function.
-/
theorem measurable_uncurry_dirichletRhsField (LPrime ellPrime : ℕ) (p : Vec d) :
    Measurable (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
      dirichletRhsField omega LPrime ellPrime p x)) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega => continuous_dirichletRhsField omega LPrime ellPrime p)
    (fun x => measurable_dirichletRhsField_apply LPrime ellPrime p x)

/-- The flux field as a function of the pair, with the sample first. -/
private theorem measurable_prod_dirichletRhsField (LPrime ellPrime : ℕ) (p : Vec d) :
    Measurable (fun q : ShellSeq d × Vec d =>
      dirichletRhsField q.1 LPrime ellPrime p q.2) := by
  have hcomp : (fun q : ShellSeq d × Vec d =>
      dirichletRhsField q.1 LPrime ellPrime p q.2) =
      (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
        dirichletRhsField omega LPrime ellPrime p x)) ∘ Prod.swap := rfl
  rw [hcomp]
  exact (measurable_uncurry_dirichletRhsField LPrime ellPrime p).comp measurable_swap

/-- The `x`-integral of a pairing of a fixed measurable field with the flux
field is measurable in the sample. -/
private theorem measurable_setIntegral_vecDot_dirichletRhsField
    (LPrime ellPrime : ℕ) (p : Vec d) (U : Set (Vec d))
    {G : ShellSeq d × Vec d → Vec d} (hG : Measurable G) :
    Measurable (fun omega : ShellSeq d => ∫ x in U,
      vecDot (G (omega, x)) (dirichletRhsField omega LPrime ellPrime p x)
        ∂MeasureTheory.volume) := by
  have hjoint : Measurable (fun q : ShellSeq d × Vec d =>
      vecDot (G q) (dirichletRhsField q.1 LPrime ellPrime p q.2)) := by
    show Measurable fun q : ShellSeq d × Vec d =>
      ∑ i, G q i * dirichletRhsField q.1 LPrime ellPrime p q.2 i
    refine Finset.measurable_sum _ fun i _ => ?_
    exact ((measurable_pi_apply i).comp hG).mul
      ((measurable_pi_apply i).comp (measurable_prod_dirichletRhsField LPrime ellPrime p))
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- A representative of a Hilbert `L²` class is measurable. -/
private theorem measurable_hilbertClassField {U : Set (Vec d)} (f : HilbertVectorL2 U) :
    Measurable (hilbertClassField f) :=
  (MeasureTheory.AEEqFun.stronglyMeasurable
    ((hilbertVectorL2ToVectorL2 (U := U) f : VectorL2 U) :
      Vec d →ₘ[volumeMeasureOn U] Vec d)).measurable

/-- **The flux class of `e.def.w` is a measurable function of the sample.**  The
flux field is a Caratheodory function, so its `L²(cu_m)` class is measurable by
the distance criterion against a countable dense sequence of the class space,
which is second countable. -/
theorem measurable_toHilbertVectorL2OfVecField_dirichletRhsField
    (LPrime ellPrime m : ℕ) (p : Vec d) :
    Measurable (fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField
        (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)) := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  refine measurable_of_measurable_norm_inner_denseRange
    (TopologicalSpace.denseSeq
      (HilbertVectorL2 (openCubeSet (originCube d (m : ℤ)))))
    (TopologicalSpace.denseRange_denseSeq _) ?_ ?_
  · have hnormeq : (fun omega : ShellSeq d => ‖toHilbertVectorL2OfVecField
        (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)‖) =
        fun omega : ShellSeq d => Real.sqrt (∫ x in openCubeSet (originCube d (m : ℤ)),
          vecDot (dirichletRhsField omega LPrime ellPrime p x)
            (dirichletRhsField omega LPrime ellPrime p x) ∂MeasureTheory.volume) := by
      funext omega
      conv_lhs => rw [← Real.sqrt_sq (norm_nonneg (toHilbertVectorL2OfVecField
        (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)))]
      congr 1
      rw [← real_inner_self_eq_norm_sq]
      exact inner_toHilbertVectorL2OfVecField_eq_integral _ _
    rw [hnormeq]
    exact Real.continuous_sqrt.measurable.comp
      (measurable_setIntegral_vecDot_dirichletRhsField LPrime ellPrime p _
        (measurable_prod_dirichletRhsField LPrime ellPrime p))
  · intro n
    have hinnereq : (fun omega : ShellSeq d => inner ℝ
        (TopologicalSpace.denseSeq
          (HilbertVectorL2 (openCubeSet (originCube d (m : ℤ)))) n)
        (toHilbertVectorL2OfVecField
          (memVectorL2_dirichletRhsField omega LPrime ellPrime m p))) =
        fun omega : ShellSeq d => ∫ x in openCubeSet (originCube d (m : ℤ)),
          vecDot (hilbertClassField (TopologicalSpace.denseSeq
              (HilbertVectorL2 (openCubeSet (originCube d (m : ℤ)))) n) x)
            (dirichletRhsField omega LPrime ellPrime p x) ∂MeasureTheory.volume := by
      funext omega
      have h0 : TopologicalSpace.denseSeq
          (HilbertVectorL2 (openCubeSet (originCube d (m : ℤ)))) n =
          toHilbertVectorL2OfVecField (memVectorL2_hilbertClassField
            (TopologicalSpace.denseSeq
              (HilbertVectorL2 (openCubeSet (originCube d (m : ℤ)))) n)) :=
        (toHilbertVectorL2OfVecField_hilbertClassField _).symm
      conv_lhs => rw [h0]
      exact inner_toHilbertVectorL2OfVecField_eq_integral _ _
    rw [hinnereq]
    exact measurable_setIntegral_vecDot_dirichletRhsField LPrime ellPrime p _
      ((measurable_hilbertClassField _).comp measurable_snd)

end Flux

/-! ## The cube Dirichlet solution operator -/

section Operator

variable [NeZero d]

/-- A Dirichlet response of the representative of a flux class. -/
def cubeDirichletResponseOfClass (Q : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) : H10Function (openCubeSet Q) :=
  Classical.choose
    (ResponseFields.exists_isCubeDirichletResponse Q (memVectorL2_hilbertClassField f))

private theorem isCubeDirichletResponse_cubeDirichletResponseOfClass (Q : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) :
    ResponseFields.IsCubeDirichletResponse Q (hilbertClassField f)
      (cubeDirichletResponseOfClass Q f) :=
  Classical.choose_spec
    (ResponseFields.exists_isCubeDirichletResponse Q (memVectorL2_hilbertClassField f))

/-- **The Dirichlet solution operator of the cube `Q`**: the map sending a flux
class in `L²(Q; ℝ^d)` to the weak-gradient class of the zero-trace solution of
`−Δw = ∇·F`.  It is well defined by
`cubeDirichletGradClass_eq_of_isCubeDirichletResponse` and `1`-Lipschitz by
`lipschitzWith_cubeDirichletGradClass`. -/
def cubeDirichletGradClass (Q : TriadicCube d)
    (f : HilbertVectorL2 (openCubeSet Q)) : HilbertVectorL2 (openCubeSet Q) :=
  (cubeDirichletResponseOfClass Q f).toH1Function.gradToHilbertVectorL2

/-- **The characterization of the solution operator.**  Every Dirichlet response
of a flux field `F` has weak-gradient class `cubeDirichletGradClass Q` applied to
the class of `F`.  In particular the value does not depend on which response,
or which representative of the flux class, was used. -/
theorem cubeDirichletGradClass_eq_of_isCubeDirichletResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    {w : H10Function (openCubeSet Q)}
    (hw : ResponseFields.IsCubeDirichletResponse Q F w) :
    w.toH1Function.gradToHilbertVectorL2 =
      cubeDirichletGradClass Q (toHilbertVectorL2OfVecField hF) := by
  have hrep : hilbertClassField (toHilbertVectorL2OfVecField hF) =
      ((toVectorL2 hF : VectorL2 (openCubeSet Q)) : Vec d → Vec d) := by
    rw [hilbertClassField, hilbertVectorL2ToVectorL2_toHilbertVectorL2 hF]
  have hae : F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      hilbertClassField (toHilbertVectorL2OfVecField hF) := by
    rw [hrep]
    exact (coeFn_toVectorL2 hF).symm
  exact gradToHilbertVectorL2_eq_of_isCubeDirichletResponse_ae hae hw
    (isCubeDirichletResponse_cubeDirichletResponseOfClass Q _)

/-- **The solution operator is `1`-Lipschitz.**  This is the stability estimate
of `ResponseMeasurability.lean` read on the class space. -/
theorem lipschitzWith_cubeDirichletGradClass (Q : TriadicCube d) :
    LipschitzWith 1 (cubeDirichletGradClass Q) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have h := norm_gradToHilbertVectorL2_sub_le_of_isCubeDirichletResponse
    (memVectorL2_hilbertClassField f) (memVectorL2_hilbertClassField g)
    (isCubeDirichletResponse_cubeDirichletResponseOfClass Q f)
    (isCubeDirichletResponse_cubeDirichletResponseOfClass Q g)
  rwa [toHilbertVectorL2OfVecField_hilbertClassField,
    toHilbertVectorL2OfVecField_hilbertClassField] at h

/-- The solution operator is continuous. -/
theorem continuous_cubeDirichletGradClass (Q : TriadicCube d) :
    Continuous (cubeDirichletGradClass Q) :=
  (lipschitzWith_cubeDirichletGradClass Q).continuous

end Operator

/-! ## The Dirichlet response of `e.def.w` through the solution operator -/

section Response

variable [NeZero d] {LPrime ellPrime m : ℕ} {p : Vec d}

/-- **The response of `e.def.w` is the solution operator applied to the flux
class of the sample.**  This holds for every realization of
`IsDirichletResponse`, so the free binder of the Section 3 statements is
eliminated. -/
theorem gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse
    (omega : ShellSeq d)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    w.toH1Function.gradToHilbertVectorL2 =
      cubeDirichletGradClass (originCube d (m : ℤ))
        (toHilbertVectorL2OfVecField
          (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)) :=
  cubeDirichletGradClass_eq_of_isCubeDirichletResponse
    (memVectorL2_dirichletRhsField omega LPrime ellPrime m p) hw

/-! ### The obligations discharged -/

/-- **The gradient class of the Dirichlet response of `e.def.w` is a measurable
function of the sample.**  This is the statement the Section 3 measurability
obligations were missing: the solution operator is continuous and the flux class
is measurable. -/
theorem measurable_gradToHilbertVectorL2_dirichletResponse :
    Measurable (fun omega : ShellSeq d =>
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2) := by
  have hfun : (fun omega : ShellSeq d =>
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2) =
      fun omega : ShellSeq d => cubeDirichletGradClass (originCube d (m : ℤ))
        (toHilbertVectorL2OfVecField
          (memVectorL2_dirichletRhsField omega LPrime ellPrime m p)) := by
    funext omega
    exact gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse omega
      (isDirichletResponse_dirichletResponse omega LPrime ellPrime m p)
  rw [hfun]
  exact (continuous_cubeDirichletGradClass (originCube d (m : ℤ))).measurable.comp
    (measurable_toHilbertVectorL2OfVecField_dirichletRhsField LPrime ellPrime m p)

/-- **Measurability of the cube energy of `∇w`.**  The cube-energy map of `e.def.w` is
`AEMeasurable` for every selection `w` of the Dirichlet response, on every
measure of the shell-sequence carrier. -/
theorem aemeasurable_vecCubeLpENorm_grad
    {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    AEMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) mu :=
  aemeasurable_vecCubeLpENorm_grad_of_canonical_class hw
    (measurable_gradToHilbertVectorL2_dirichletResponse).aemeasurable

/-- **`hDmeas`, discharged**, in the `AEStronglyMeasurable` shape the
`l.LHS.term1` chain consumes. -/
theorem aestronglyMeasurable_vecCubeLpENorm_grad
    {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    AEStronglyMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) mu :=
  (aemeasurable_vecCubeLpENorm_grad hw).aestronglyMeasurable

end Response

end

end SuperdiffusionCLT.Section3.Setup
