/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.DirichletResponse
public import SuperdiffusionCLT.Section3.ResponseFields.Norms

/-!
# Observables of the Dirichlet response do not depend on the selection

The paper introduces `w` as *the* Dirichlet response of `e.def.w`.  The
statements of Section 3 bind it
as an arbitrary selection
`w : ShellSeq d → H10Function (openCubeSet (originCube d m))` subject only to
`∀ omega, IsDirichletResponse omega L' ℓ' m p (w omega)`, so nothing in the
binder records how `w omega` depends on `omega`.

This module records the structural fact that removes the arbitrariness: by
`isDirichletResponse_gradToVectorL2_eq` two responses of the same sample have
the *same* weak-gradient `L²(cu_m)` class, hence a.e. equal weak gradients, so
every observable built from the weak gradient by an a.e.-invariant construction
is literally the same function of the sample for every selection.  In
particular each such observable of an arbitrary selection is **equal, as a
function of `omega`**, to the observable of the one canonical response
`dirichletResponse omega L' ℓ' m p`.

## Main results

* `grad_ae_eq_dirichletResponse`, `grad_ae_eq_dirichletResponse_cubeMeasure`:
  the weak gradient of any selection agrees a.e. with the canonical one, on the
  restricted Lebesgue measure of the open cube and on the normalized cube
  measure of the half-open cube.
* `vecCubeLpENorm_grad_eq_dirichletResponse`,
  `vecCubeLpENorm_comp_grad_eq_dirichletResponse`: the normalized `L̲^q(cu_m)`
  norms of the response gradient, and of any pointwise field built from it, are
  selection-free.
* `setIntegral_comp_grad_eq_dirichletResponse`,
  `volumeAverage_comp_grad_eq_dirichletResponse`,
  `volumeAverageVec_comp_grad_eq_dirichletResponse`: the same for set integrals
  and cube means over any subset of the cube.
* The `…_funext` family: the sample-level function equalities, stated so that a
  measurability obligation about an arbitrary selection is rewritten into the
  same obligation about `dirichletResponse`.
* `aemeasurable_vecCubeLpENorm_matVecMul_grad_of_canonical`,
  `measurable_volumeAverageVec_matVecMul_grad_of_canonical` and
  `aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_canonical`: the named
  reductions of the measurability obligations of the Section 3 term statements to the
  corresponding observable of the canonical response.
* `vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField` and
  `aemeasurable_vecCubeLpENorm_grad_of_canonical_class`: the cube `L̲²` norm is a
  fixed constant multiple of the `HilbertVectorL2` enorm of the class, so the
  cube-energy obligations reduce to one class-level fact.
* `integral_vecNormSq_grad_sub_le_of_isCubeDirichletResponse` and
  `norm_gradToHilbertVectorL2_sub_le_of_isCubeDirichletResponse`: the elliptic
  energy bound and the `1`-Lipschitz dependence of the response gradient on the flux.

`ResponseMeasurabilityB.lean` turns the Lipschitz estimate into the cube
Dirichlet solution operator and discharges the cube-energy obligations.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The canonical response as a reference selection -/

/-- Every Dirichlet response of `e.def.w` has a.e. the same weak gradient on
`cu_m` as the canonical response. -/
theorem grad_ae_eq_dirichletResponse (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    w.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (m : ℤ)))]
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad :=
  isDirichletResponse_grad_ae_eq omega LPrime ellPrime m p hw
    (isDirichletResponse_dirichletResponse omega LPrime ellPrime m p)

/-- The same a.e. identification for the normalized cube measure of the
half-open realization, the measure of the `L̲^q(cu_m)` norms. -/
theorem grad_ae_eq_dirichletResponse_cubeMeasure (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    w.toH1Function.grad =ᵐ[normalizedCubeMeasure (originCube d (m : ℤ))]
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad := by
  have h := grad_ae_eq_dirichletResponse omega LPrime ellPrime m p hw
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact MeasureTheory.Measure.ae_smul_measure h _

/-! ## Selection-free observables of the response gradient -/

/-- A pointwise field built from the response gradient is a.e. the same for
every selection, on the open cube. -/
theorem comp_grad_ae_eq_dirichletResponse {E : Type*} (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d) (G : Vec d → Vec d → E)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    (fun x => G x (w.toH1Function.grad x)) =ᵐ[volumeMeasureOn
        (openCubeSet (originCube d (m : ℤ)))]
      fun x => G x ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x) := by
  filter_upwards [grad_ae_eq_dirichletResponse omega LPrime ellPrime m p hw] with x hx
  rw [hx]

/-- The same for the normalized cube measure of the half-open realization. -/
theorem comp_grad_ae_eq_dirichletResponse_cubeMeasure {E : Type*} (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d) (G : Vec d → Vec d → E)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    (fun x => G x (w.toH1Function.grad x)) =ᵐ[normalizedCubeMeasure (originCube d (m : ℤ))]
      fun x => G x ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x) := by
  filter_upwards [grad_ae_eq_dirichletResponse_cubeMeasure omega LPrime ellPrime m p hw]
    with x hx
  rw [hx]

/-- **The `L̲^q(cu_m)` norm of a field built from the response gradient is
selection-free.** -/
theorem vecCubeLpENorm_comp_grad_eq_dirichletResponse (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d) (q : ENNReal) (G : Vec d → Vec d → Vec d)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (fun x => G x (w.toH1Function.grad x)) =
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (fun x => G x ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)) := by
  refine eLpNorm_congr_ae ?_
  filter_upwards
    [comp_grad_ae_eq_dirichletResponse_cubeMeasure omega LPrime ellPrime m p G hw] with x hx
  exact congrArg HilbertVec.ofVec hx

/-- The instance of `vecCubeLpENorm_comp_grad_eq_dirichletResponse` at the bare
response gradient: the cube energy of `e.def.w` is selection-free. -/
theorem vecCubeLpENorm_grad_eq_dirichletResponse (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d) (q : ENNReal)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q w.toH1Function.grad =
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad :=
  vecCubeLpENorm_comp_grad_eq_dirichletResponse omega LPrime ellPrime m p q
    (fun _ v => v) hw

/-- **Set integrals over a subset of the cube are selection-free.** -/
theorem setIntegral_comp_grad_eq_dirichletResponse {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (omega : ShellSeq d) (LPrime ellPrime m : ℕ) (p : Vec d)
    {V : Set (Vec d)} (hV : V ⊆ openCubeSet (originCube d (m : ℤ)))
    (G : Vec d → Vec d → E)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    ∫ x in V, G x (w.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in V, G x ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)
        ∂MeasureTheory.volume := by
  refine integral_congr_ae ?_
  have hle : MeasureTheory.volume.restrict V ≤
      MeasureTheory.volume.restrict (openCubeSet (originCube d (m : ℤ))) :=
    MeasureTheory.Measure.restrict_mono hV le_rfl
  exact (comp_grad_ae_eq_dirichletResponse omega LPrime ellPrime m p G hw).filter_mono
    (MeasureTheory.ae_mono hle)

/-- **Cube means of scalar observables of the response gradient are
selection-free.** -/
theorem volumeAverage_comp_grad_eq_dirichletResponse (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d)
    {V : Set (Vec d)} (hV : V ⊆ openCubeSet (originCube d (m : ℤ)))
    (G : Vec d → Vec d → ℝ)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    volumeAverage V (fun x => G x (w.toH1Function.grad x)) =
      volumeAverage V
        (fun x => G x ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)) := by
  unfold volumeAverage
  exact congrArg (fun t : ℝ => (MeasureTheory.volume V).toReal⁻¹ * t)
    (setIntegral_comp_grad_eq_dirichletResponse omega LPrime ellPrime m p hV G hw)

/-- **Vector cube means of observables of the response gradient are
selection-free**, the form used by the measurability sentence of the paper. -/
theorem volumeAverageVec_comp_grad_eq_dirichletResponse (omega : ShellSeq d)
    (LPrime ellPrime m : ℕ) (p : Vec d)
    {V : Set (Vec d)} (hV : V ⊆ openCubeSet (originCube d (m : ℤ)))
    (G : Vec d → Vec d → Vec d)
    {w : H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : IsDirichletResponse omega LPrime ellPrime m p w) :
    volumeAverageVec V (fun x => G x (w.toH1Function.grad x)) =
      volumeAverageVec V
        (fun x => G x ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)) := by
  funext i
  exact volumeAverage_comp_grad_eq_dirichletResponse omega LPrime ellPrime m p hV
    (fun x v => G x v i) hw

/-! ## The sample-level identities and the measurability reductions

The lemmas above are identities for a fixed sample.  Read as identities of
functions of the sample they say that a measurability obligation about an
arbitrary selection `w` is *the same obligation* about the canonical response
`dirichletResponse`, whatever the `σ`-algebra and whatever the measure.
-/

section Sample

variable {LPrime ellPrime m : ℕ} {p : Vec d}
  {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}

/-- The cube `L̲^q(cu_m)` norm of a field built from the response gradient, as a
function of the sample, does not depend on the selection. -/
theorem vecCubeLpENorm_comp_grad_response_funext (q : ENNReal)
    (G : ShellSeq d → Vec d → Vec d → Vec d)
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    (fun omega : ShellSeq d => ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (fun x => G omega x ((w omega).toH1Function.grad x))) =
      fun omega : ShellSeq d => ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (fun x => G omega x
          ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)) := by
  funext omega
  exact vecCubeLpENorm_comp_grad_eq_dirichletResponse omega LPrime ellPrime m p q
    (G omega) (hw omega)

/-- The cube energy map of `e.def.w`, as a function of the sample, does not
depend on the selection. -/
theorem vecCubeLpENorm_grad_response_funext (q : ENNReal)
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    (fun omega : ShellSeq d => ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (w omega).toH1Function.grad) =
      fun omega : ShellSeq d => ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad := by
  funext omega
  exact vecCubeLpENorm_grad_eq_dirichletResponse omega LPrime ellPrime m p q (hw omega)

/-- The cube mean of a scalar observable of the response gradient, as a function
of the sample, does not depend on the selection. -/
theorem volumeAverage_comp_grad_response_funext {V : Set (Vec d)}
    (hV : V ⊆ openCubeSet (originCube d (m : ℤ))) (G : ShellSeq d → Vec d → Vec d → ℝ)
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    (fun omega : ShellSeq d =>
        volumeAverage V (fun x => G omega x ((w omega).toH1Function.grad x))) =
      fun omega : ShellSeq d => volumeAverage V (fun x => G omega x
        ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)) := by
  funext omega
  exact volumeAverage_comp_grad_eq_dirichletResponse omega LPrime ellPrime m p hV
    (G omega) (hw omega)

/-- The vector cube mean of an observable of the response gradient, as a
function of the sample, does not depend on the selection. -/
theorem volumeAverageVec_comp_grad_response_funext {V : Set (Vec d)}
    (hV : V ⊆ openCubeSet (originCube d (m : ℤ))) (G : ShellSeq d → Vec d → Vec d → Vec d)
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    (fun omega : ShellSeq d =>
        volumeAverageVec V (fun x => G omega x ((w omega).toH1Function.grad x))) =
      fun omega : ShellSeq d => volumeAverageVec V (fun x => G omega x
        ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)) := by
  funext omega
  exact volumeAverageVec_comp_grad_eq_dirichletResponse omega LPrime ellPrime m p hV
    (G omega) (hw omega)

/-! ### Reduction of the cube energy to one class-level fact

The cube `L̲²(cu_m)` norm of a weak gradient is a fixed constant multiple of the
`enorm` of its `HilbertVectorL2(cu_m)` class, so the cube-energy obligations
reduce to the single statement that the canonical response's gradient class is
a measurable function of the sample.
-/

omit [NeZero d] in
/-- **`‖F‖_{L̲²(Q)}` is a fixed constant multiple of `‖F‖ₑ` read in the
`HilbertVectorL2(Q)` class space**: the normalized cube measure is the
restricted Lebesgue measure of the cube rescaled by `|Q|⁻¹`. -/
theorem vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F) :
    ResponseFields.vecCubeLpENorm Q 2 F =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ ((1 : ENNReal) / 2).toReal *
        ‖toHilbertVectorL2OfVecField hF‖ₑ := by
  have hbase : (toHilbertVectorL2OfVecField hF : Vec d → HilbertVec d)
      =ᵐ[volumeMeasureOn (openCubeSet Q)] hilbertifyVecField F :=
    coeFn_toHilbertVectorL2OfVecField hF
  have hnorm : hilbertifyVecField F
      =ᵐ[normalizedCubeMeasure Q]
      (toHilbertVectorL2OfVecField hF : Vec d → HilbertVec d) := by
    rw [normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact MeasureTheory.Measure.ae_smul_measure hbase.symm _
  rw [ResponseFields.vecCubeLpENorm, Section2.Norms.cubeLpENorm,
    eLpNorm_congr_ae hnorm, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    eLpNorm_smul_measure_of_ne_zero
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne', ← MeasureTheory.Lp.enorm_def,
    smul_eq_mul]

omit [NeZero d] in
/-- The instance of `vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField` at a
weak gradient. -/
theorem vecCubeLpENorm_grad_eq_enorm_gradToHilbertVectorL2
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) :
    ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2 u.grad =
      ENNReal.ofReal ((cubeVolume (originCube d (m : ℤ)))⁻¹) ^
          ((1 : ENNReal) / 2).toReal * ‖u.gradToHilbertVectorL2‖ₑ :=
  vecCubeLpENorm_eq_enorm_toHilbertVectorL2OfVecField u.grad_memVectorL2

/-- **The cube-energy obligation from one class-level fact.**  Measurability of
the canonical response's gradient class in the sample gives the `AEMeasurable`
cube-energy obligation for *every* selection. -/
theorem aemeasurable_vecCubeLpENorm_grad_of_canonical_class
    {mu : MeasureTheory.Measure (ShellSeq d)}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (hcan : AEMeasurable (fun omega : ShellSeq d =>
      (dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2)
      mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (w omega).toH1Function.grad) mu := by
  rw [vecCubeLpENorm_grad_response_funext 2 hw]
  have hfun : (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) 2
        (dirichletResponse omega LPrime ellPrime m p).toH1Function.grad) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal ((cubeVolume (originCube d (m : ℤ)))⁻¹) ^
            ((1 : ENNReal) / 2).toReal *
          ‖(dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2‖ₑ := by
    funext omega
    exact vecCubeLpENorm_grad_eq_enorm_gradToHilbertVectorL2 _
  rw [hfun]
  exact AEMeasurable.const_mul (continuous_enorm.measurable.comp_aemeasurable hcan) _

/-! ### The named obligations of the Section 3 term statements -/

/-- **The field half of the `l.RHS.term2` obligations**: the `AEMeasurable`
obligation for `‖R‖_{L̲^q(cu_m)}`, `R = A ∇w`, follows from the same statement
for the canonical response.  The coefficient factor `A` is arbitrary, so this
covers `R = (k_{L'} − k_ℓ) ∇w` at
`A omega x = (a_{L'}(omega) − a_ℓ(omega))(x)`. -/
theorem aemeasurable_vecCubeLpENorm_matVecMul_grad_of_canonical
    {mu : MeasureTheory.Measure (ShellSeq d)} (q : ENNReal)
    (A : ShellSeq d → Vec d → Mat d)
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (hcan : AEMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (fun x => matVecMul (A omega x)
          ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x))) mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      ResponseFields.vecCubeLpENorm (originCube d (m : ℤ)) q
        (fun x => matVecMul (A omega x) ((w omega).toH1Function.grad x))) mu := by
  rw [vecCubeLpENorm_comp_grad_response_funext q
    (fun omega x v => matVecMul (A omega x) v) hw]
  exact hcan

/-- **`hRmeas`, the field half of the printed measurability sentence**: the
`σ`-algebra is arbitrary, so this covers `Measurable[highShellSigma d ℓ]`.  The
cube mean of `R = A ∇w` over any subset of `cu_m`
follows from the same statement for the canonical response. -/
theorem measurable_volumeAverageVec_matVecMul_grad_of_canonical
    {m0 : MeasurableSpace (ShellSeq d)} {V : Set (Vec d)}
    (hV : V ⊆ openCubeSet (originCube d (m : ℤ))) (A : ShellSeq d → Vec d → Mat d)
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (hcan : Measurable[m0] (fun omega : ShellSeq d =>
      volumeAverageVec V (fun y => matVecMul (A omega y)
        ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad y)))) :
    Measurable[m0] (fun omega : ShellSeq d =>
      volumeAverageVec V (fun y => matVecMul (A omega y)
        ((w omega).toH1Function.grad y))) := by
  rw [volumeAverageVec_comp_grad_response_funext hV
    (fun omega y v => matVecMul (A omega y) v) hw]
  exact hcan

/-- **Measurability of the second-step observable**: the pairing observable
`|(∇w · V)_{cu_m}|` of the second step of `l.RHS.term1` follows from the same
statement for the canonical response, for an arbitrary sample-dependent field
`V`. -/
theorem aemeasurable_ofReal_abs_volumeAverage_vecDot_grad_of_canonical
    {mu : MeasureTheory.Measure (ShellSeq d)} {V : Set (Vec d)}
    (hV : V ⊆ openCubeSet (originCube d (m : ℤ))) (Vfield : ShellSeq d → Vec d → Vec d)
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (hcan : AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal |volumeAverage V (fun x =>
        vecDot ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)
          (Vfield omega x))|) mu) :
    AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal |volumeAverage V (fun x =>
        vecDot ((w omega).toH1Function.grad x) (Vfield omega x))|) mu := by
  have hfun : (fun omega : ShellSeq d =>
      ENNReal.ofReal |volumeAverage V (fun x =>
        vecDot ((w omega).toH1Function.grad x) (Vfield omega x))|) =
      fun omega : ShellSeq d =>
        ENNReal.ofReal |volumeAverage V (fun x =>
          vecDot ((dirichletResponse omega LPrime ellPrime m p).toH1Function.grad x)
            (Vfield omega x))| := by
    funext omega
    exact congrArg (fun t : ℝ => ENNReal.ofReal |t|)
      (volumeAverage_comp_grad_eq_dirichletResponse omega LPrime ellPrime m p hV
        (fun x v => vecDot v (Vfield omega x)) (hw omega))
  rw [hfun]
  exact hcan

end Sample

/-! ## Stability of the response in the forcing

The identification above makes every observable a genuine function of the
sample but says nothing about how that function varies.  The next theorem
does: the response gradient is `1`-Lipschitz in the forcing field, in the
energy norm of `cu_m`.  It is the deterministic half of any future proof that
the canonical response is measurable in the sample, and it is what rules out a
pathological selection: two samples with nearby flux fields have nearby
response gradients, for *every* choice of response.
-/

section Stability

omit [NeZero d] in
/-- `vecDot` is additive in the left slot under subtraction. -/
private theorem vecDot_sub_left' (a b c : Vec d) :
    vecDot (a - b) c = vecDot a c - vecDot b c := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

omit [NeZero d] in
/-- The weak gradient of a difference of zero-trace functions. -/
private theorem grad_sub_apply {U : Set (Vec d)}
    (w w' : H10Function U) (x : Vec d) :
    (w - w').toH1Function.grad x =
      w.toH1Function.grad x - w'.toH1Function.grad x := by
  change (w.toH1Function - w'.toH1Function).grad x = _
  exact congrFun (H1Function.sub_grad w.toH1Function w'.toH1Function) x

omit [NeZero d] in
/-- **The energy identity for the difference of two cube Dirichlet responses.**
Testing the difference of the two weak equations against the difference itself
turns the cube energy of `∇w − ∇w'` into the pairing of the difference of the
flux fields with that same gradient. -/
private theorem integral_vecNormSq_grad_sub_eq_neg_pairing {Q : TriadicCube d}
    {F F' : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (hF' : MemVectorL2 (openCubeSet Q) F')
    {w w' : H10Function (openCubeSet Q)}
    (hw : ResponseFields.IsCubeDirichletResponse Q F w)
    (hw' : ResponseFields.IsCubeDirichletResponse Q F' w') :
    ∫ x in openCubeSet Q,
        vecNormSq (w.toH1Function.grad x - w'.toH1Function.grad x)
          ∂MeasureTheory.volume =
      -∫ x in openCubeSet Q, vecDot (F x - F' x)
          (w.toH1Function.grad x - w'.toH1Function.grad x) ∂MeasureTheory.volume := by
  obtain ⟨u, hu⟩ : ∃ u : H10Function (openCubeSet Q), u = w - w' := ⟨w - w', rfl⟩
  have hgrad : ∀ x : Vec d, u.toH1Function.grad x =
      w.toH1Function.grad x - w'.toH1Function.grad x := by
    intro x
    rw [hu]
    exact grad_sub_apply w w' x
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
    rw [← vecDot_sub_left', ← hgrad x]
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
    exact (vecDot_sub_left' _ _ _).symm
  have hgoal : ∫ x in openCubeSet Q, vecDot (F x - F' x)
          (w.toH1Function.grad x - w'.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, vecDot (F x - F' x)
          (u.toH1Function.grad x) ∂MeasureTheory.volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [hgrad x]
  rw [hsplit, hw u, hw' u, hgoal, ← hsplitF]
  ring

omit [NeZero d] in
/-- The Young step.  If the cube energy of `B` is the negative pairing of `B`
with `A`, then it is bounded by the cube energy of `A`. -/
private theorem integral_vecNormSq_le_of_eq_neg_pairing {U : Set (Vec d)}
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

omit [NeZero d] in
/-- **Stability of the cube Dirichlet response in the forcing.**  The cube
energy of the difference of two response gradients is bounded by the cube
energy of the difference of the two flux fields.  No selection is involved: the
bound holds for every realization of `IsCubeDirichletResponse` at either
flux. -/
theorem integral_vecNormSq_grad_sub_le_of_isCubeDirichletResponse {Q : TriadicCube d}
    {F F' : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (hF' : MemVectorL2 (openCubeSet Q) F')
    {w w' : H10Function (openCubeSet Q)}
    (hw : ResponseFields.IsCubeDirichletResponse Q F w)
    (hw' : ResponseFields.IsCubeDirichletResponse Q F' w') :
    ∫ x in openCubeSet Q,
        vecNormSq (w.toH1Function.grad x - w'.toH1Function.grad x)
          ∂MeasureTheory.volume ≤
      ∫ x in openCubeSet Q, vecNormSq (F x - F' x) ∂MeasureTheory.volume :=
  integral_vecNormSq_le_of_eq_neg_pairing (hF.sub hF')
    (w.toH1Function.grad_memVectorL2.sub w'.toH1Function.grad_memVectorL2)
    (integral_vecNormSq_grad_sub_eq_neg_pairing hF hF' hw hw')

omit [NeZero d] in
/-- The squared `HilbertVectorL2(U)` norm of a square-integrable field is its
Euclidean energy. -/
private theorem norm_sq_toHilbertVectorL2OfVecField {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    ‖toHilbertVectorL2OfVecField hf‖ ^ 2 =
      ∫ x in U, vecNormSq (f x) ∂MeasureTheory.volume := by
  rw [← real_inner_self_eq_norm_sq]
  exact inner_toHilbertVectorL2OfVecField_eq_integral hf hf

omit [NeZero d] in
/-- **Stability in the `HilbertVectorL2(Q)` norm.**  The cube Dirichlet response
gradient class is a `1`-Lipschitz function of the flux class. -/
theorem norm_gradToHilbertVectorL2_sub_le_of_isCubeDirichletResponse
    {Q : TriadicCube d} {F F' : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (hF' : MemVectorL2 (openCubeSet Q) F')
    {w w' : H10Function (openCubeSet Q)}
    (hw : ResponseFields.IsCubeDirichletResponse Q F w)
    (hw' : ResponseFields.IsCubeDirichletResponse Q F' w') :
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
    rw [hgrad, hflux, norm_sq_toHilbertVectorL2OfVecField,
      norm_sq_toHilbertVectorL2OfVecField]
    exact integral_vecNormSq_grad_sub_le_of_isCubeDirichletResponse hF hF' hw hw'
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hroot

end Stability

end

end SuperdiffusionCLT.Section3.Setup
