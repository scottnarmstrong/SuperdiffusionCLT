/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityB
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1WeakHessian
public import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Measurability
public import Homogenization.Probability.SeparableHilbertMeasurability

/-!
# Sample-measurability of the response Hessian norm

The Section 3 statement of `e.def.W1` carries the residue `_hMeasH1`: the
sample-measurability of `omega ↦ ‖D² w_omega‖_{L²(cu_m)}`, where `D² w_omega` is
a weak Hessian of the Dirichlet response at the sample `omega`.
`Section3/Setup/ResponseMeasurabilityD.aemeasurable_vecCubeH1ENorm_grad_of_hessian`
reduces that residue one-for-one to the measurability of this Hessian *norm*.

The Hessian is only unique up to almost everywhere equality, so it is not a
function of `omega` on the nose; its `L²` class is, and the class determines the
norm.  The route is the standard one for maps into an `L²` space: pair against a
dense sequence of smooth compactly supported test matrices, and use that a map
into a Polish space is measurable as soon as its inner products against a dense
sequence are.  The pairing against a test matrix is evaluated with the *weak*
second-derivative identity `HasWeakHessianOn.weak_second`, which turns it into
the `L²` class of the response gradient that
`Section3/Setup/ResponseMeasurabilityB.measurable_gradToHilbertVectorL2_dirichletResponse`
already proves measurable.

## Main results

* `measurable_of_measurable_inner_denseRange_Lp`: the abstract engine — a map
  into a separable `L²` space whose inner products against a dense sequence are
  measurable is itself measurable.
* `measurable_of_smoothProbe_inner_measurable`: the engine fed by the dense
  smooth test-matrix sequence of the fixed-competitor toolkit
  (`dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset`).
* `inner_toLp_ofMat_eq_neg_sum`: the pairing of an `L²` matrix class against a
  smooth compactly supported test matrix, evaluated by `weak_second`.
* `measurable_hessianCarrierLp`: the Hessian carrier of a family of weak Hessians
  of measurable-gradient `H¹` functions is a measurable `L²` class.
* `aemeasurable_cubeLpENorm_hessian_of_hasWeakHessianOn` and
  `aemeasurable_vecCubeH1ENorm_grad_of_hasWeakHessianOn`: the Hessian norm is
  sample-measurable, for an arbitrary family of weak Hessians.
* `aemeasurable_vecCubeH1ENorm_grad_canonicalResponseHessian`: the residue
  `_hMeasH1` of the statement of `l.RHS.term1`, discharged at the canonical
  witness `canonicalResponseHessian`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The abstract engine -/

/-- **Norm measurability from inner-product measurability against a dense
sequence.**  If `u : ℕ → H` has dense range in a separable Hilbert space `H`
carrying the Borel structure of a Polish space, then a map `F : Ω → H` is
measurable as soon as every `omega ↦ ⟪u n, F omega⟫` is: the inner products
against a dense family separate points.

The measurable structure on `H` is supplied explicitly as `borel H`, since the
ambient `L²` types of this development carry no global `MeasurableSpace`
instance. -/
theorem measurable_of_measurable_inner_denseRange_Lp
    {Ω : Type*} [MeasurableSpace Ω] {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : ℕ → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) (hu : DenseRange u)
    {F : Ω → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)}
    (hInner : ∀ n : ℕ, Measurable fun omega => inner ℝ (u n) (F omega)) :
    @Measurable Ω (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) _
      (borel (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))) F := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let H := MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  exact measurable_of_measurable_inner_denseRange_polish u hu hInner

/-! ## The dense smooth test-matrix sequence -/

/-- On an open finite-measure set, the smooth compactly supported
`HilbertMat`-valued fields supported in the set form a dense *sequence* in
`L²`. -/
theorem exists_dense_smoothProbeSequence_of_isOpen_volume_ne_top {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤) :
    ∃ u : ℕ → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U), DenseRange u ∧
      ∀ n : ℕ, ∃ g : Vec d → HilbertMat d,
        ∃ hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U),
          u n = hgL2.toLp g ∧ ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
            tsupport g ⊆ U :=
  exists_dense_smoothProbeSequence_of_dense_smoothProbeSet (U := U)
    (dense_smoothCompactSupportHilbertMatrixL2_tsupport_subset (d := d) (U := U)
      hUopen hUfinite)

/-- **The engine fed by smooth test matrices.**  A map into `L²(U; HilbertMat d)` is
measurable as soon as its inner products against every smooth compactly supported
test matrix supported in `U` are. -/
theorem measurable_of_smoothProbe_inner_measurable
    {Ω : Type*} [MeasurableSpace Ω] {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤)
    {F : Ω → MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)}
    (hInner : ∀ (g : Vec d → HilbertMat d)
      (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U)),
      ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ U →
      Measurable fun omega => inner ℝ (hgL2.toLp g) (F omega)) :
    @Measurable Ω (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) _
      (borel (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))) F := by
  obtain ⟨u, hu, hSmooth⟩ :=
    exists_dense_smoothProbeSequence_of_isOpen_volume_ne_top (d := d) (U := U) hUopen hUfinite
  refine measurable_of_measurable_inner_denseRange_Lp (d := d) (U := U) u hu ?_
  intro n
  obtain ⟨g, hgL2, hEq, hcont, hcpt, hsupp⟩ := hSmooth n
  rw [hEq]
  exact hInner g hgL2 hcont hcpt hsupp

/-! ## The Hilbert-matrix carrier as an `L²` class -/

/-- The `(i,j)` entry of the Hilbert-matrix realization of a matrix field. -/
theorem hilbertMat_ofLp_entry_ofMat {d : ℕ} (A : Mat d) (i j : Fin d) :
    ((HilbertMat.ofMat A).ofLp i).ofLp j = A i j :=
  HilbertMat.entryL_ofMat i j A

/-- A matrix field with square-integrable entries is square integrable as a
Hilbert-matrix-valued field. -/
theorem memLp_hilbertMat_ofMat {U : Set (Vec d)} {A : Vec d → Mat d}
    (hA : ∀ i j : Fin d, MeasureTheory.MemLp (fun x => A x i j) 2 (volumeMeasureOn U)) :
    MeasureTheory.MemLp (fun x => HilbertMat.ofMat (A x)) 2 (volumeMeasureOn U) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  rw [MeasureTheory.memLp_piLp_iff]
  intro j
  simpa only [hilbertMat_ofLp_entry_ofMat] using hA i j

/-- The `L²(U)` class of the Hilbert-matrix carrier of a matrix field. -/
def hessianCarrierLp {U : Set (Vec d)} (A : Vec d → Mat d)
    (hA : ∀ i j : Fin d, MeasureTheory.MemLp (fun x => A x i j) 2 (volumeMeasureOn U)) :
    MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U) :=
  (memLp_hilbertMat_ofMat (U := U) hA).toLp (fun x => HilbertMat.ofMat (A x))

theorem hessianCarrierLp_coeFn_ae {U : Set (Vec d)} {A : Vec d → Mat d}
    (hA : ∀ i j : Fin d, MeasureTheory.MemLp (fun x => A x i j) 2 (volumeMeasureOn U)) :
    (fun x => (hessianCarrierLp (U := U) A hA : Vec d → HilbertMat d) x) =ᵐ[volumeMeasureOn U]
      (fun x => HilbertMat.ofMat (A x)) :=
  (memLp_hilbertMat_ofMat (U := U) hA).coeFn_toLp

/-! ## Entries of a smooth Hilbert-matrix test function -/

theorem contDiff_hilbertMat_entry {g : Vec d → HilbertMat d}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => ((g y).ofLp i).ofLp j) := by
  simpa [Function.comp_def] using
    ContDiff.continuousLinearMap_comp (HilbertMat.entryL i j) hg

theorem hasCompactSupport_hilbertMat_entry {g : Vec d → HilbertMat d}
    (hg : HasCompactSupport g) (i j : Fin d) :
    HasCompactSupport (fun y : Vec d => ((g y).ofLp i).ofLp j) := by
  simpa [Function.comp_def] using
    hg.comp_left (g := fun A : HilbertMat d => ((A.ofLp i).ofLp j)) (by simp)

theorem tsupport_hilbertMat_entry_subset {g : Vec d → HilbertMat d} {U : Set (Vec d)}
    (hg : tsupport g ⊆ U) (i j : Fin d) :
    tsupport (fun y : Vec d => ((g y).ofLp i).ofLp j) ⊆ U := by
  have hsub : tsupport (fun y : Vec d => ((g y).ofLp i).ofLp j) ⊆ tsupport g := by
    simpa [Function.comp_def] using
      tsupport_comp_subset (g := fun A : HilbertMat d => ((A.ofLp i).ofLp j)) (by simp) g
  exact hsub.trans hg

/-! ## The test field is square integrable -/

/-- The coordinate field `x ↦ (∂_j φ x) • e_i` of a smooth compactly supported
scalar test function lies in `L²(U; Vec d)`. -/
theorem memVectorL2_smul_basisVec_fderiv {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcpt : HasCompactSupport φ) (i j : Fin d) :
    MemVectorL2 U (fun x : Vec d => (fderiv ℝ φ x) (basisVec j) • basisVec i) := by
  have hfder_cont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hfder : MeasureTheory.MemLp (fderiv ℝ φ) 2 (volumeMeasureOn U) :=
    hfder_cont.memLp_of_hasCompactSupport (hφcpt.fderiv (𝕜 := ℝ))
  have hcoord : MeasureTheory.MemLp (fun x : Vec d => (fderiv ℝ φ x) (basisVec j)) 2
      (volumeMeasureOn U) :=
    (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).comp_memLp' hfder
  have hsmul : MeasureTheory.MemLp
      (fun x : Vec d => (fderiv ℝ φ x) (basisVec j) • basisVec i) 2 (volumeMeasureOn U) :=
    (ContinuousLinearMap.toSpanSingleton ℝ (basisVec i)).comp_memLp' hcoord
  simpa [MemVectorL2] using hsmul

/-! ## The pairing identity -/

/-- **The pairing of an `L²` matrix class against a smooth compactly supported
test matrix, evaluated by the weak second-derivative identity.**  Expanding the two
`L²` inner products over the matrix entries turns the pairing into the sum of the
weak second derivatives of the response against the entries of the test matrix; the
entries of the test matrix are smooth, compactly supported and supported in `U`, so each
weak identity applies verbatim. -/
theorem inner_toLp_ofMat_eq_neg_sum {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : H1Function U} {A : Vec d → Mat d}
    (hA : ∀ i j : Fin d, HasWeakPartialDerivOn U j (fun x => u.grad x i) (fun x => A x i j))
    (hAmem : ∀ i j : Fin d, MeasureTheory.MemLp (fun x => A x i j) 2 (volumeMeasureOn U))
    {g : Vec d → HilbertMat d} (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) (hg_compact : HasCompactSupport g)
    (hg_supp : tsupport g ⊆ U) :
    inner ℝ (hgL2.toLp g) (hessianCarrierLp (U := U) A hAmem) =
      -∑ i : Fin d, ∑ j : Fin d, ∫ x in U,
        u.grad x i * (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
  have hmem : MeasureTheory.MemLp (fun x : Vec d => HilbertMat.ofMat (A x)) 2 (volumeMeasureOn U) :=
    memLp_hilbertMat_ofMat (U := U) hAmem
  have hInt : ∀ i j : Fin d,
      Integrable (fun x : Vec d => ((g x).ofLp i).ofLp j * A x i j) (volumeMeasureOn U) := by
    intro i j
    exact MemLp.integrable_mul
      ((HilbertMat.entryL i j).comp_memLp' hgL2) (hAmem i j)
  have hstep1 : inner ℝ (hgL2.toLp g) (hessianCarrierLp (U := U) A hAmem) =
      ∫ x : Vec d, ∑ i : Fin d, ∑ j : Fin d,
        ((g x).ofLp i).ofLp j * A x i j ∂(volumeMeasureOn U) := by
    rw [hessianCarrierLp, MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hgL2.coeFn_toLp, hmem.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, HilbertMat.inner_def]
  have hstep2 : (∫ x : Vec d, ∑ i : Fin d, ∑ j : Fin d,
        ((g x).ofLp i).ofLp j * A x i j ∂(volumeMeasureOn U)) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x : Vec d,
        ((g x).ofLp i).ofLp j * A x i j ∂(volumeMeasureOn U) := by
    have hOuter : ∀ i : Fin d, Integrable
        (fun x : Vec d => ∑ j : Fin d, ((g x).ofLp i).ofLp j * A x i j)
        (volumeMeasureOn U) := fun i =>
      MeasureTheory.integrable_finsetSum Finset.univ fun j _ => hInt i j
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hOuter i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact MeasureTheory.integral_finsetSum Finset.univ fun j _ => hInt i j
  have hstep3 : (∑ i : Fin d, ∑ j : Fin d, ∫ x : Vec d,
        ((g x).ofLp i).ofLp j * A x i j ∂(volumeMeasureOn U)) =
      -∑ i : Fin d, ∑ j : Fin d, ∫ x in U,
        u.grad x i * (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
    have hterm : ∀ i j : Fin d,
        (∫ x : Vec d, ((g x).ofLp i).ofLp j * A x i j ∂(volumeMeasureOn U)) =
          -∫ x in U, u.grad x i *
            (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
      intro i j
      rw [show (fun x : Vec d => ((g x).ofLp i).ofLp j * A x i j) =
          (fun x : Vec d => A x i j * ((g x).ofLp i).ofLp j) from
        funext fun x => mul_comm _ _]
      rw [hA i j (fun y : Vec d => ((g y).ofLp i).ofLp j)
        (contDiff_hilbertMat_entry hg_cont i j)
        (hasCompactSupport_hilbertMat_entry hg_compact i j)
        (tsupport_hilbertMat_entry_subset hg_supp i j), neg_neg]
    calc (∑ i : Fin d, ∑ j : Fin d, ∫ x : Vec d,
          ((g x).ofLp i).ofLp j * A x i j ∂(volumeMeasureOn U))
        = ∑ i : Fin d, ∑ j : Fin d, -∫ x in U, u.grad x i *
            (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
      _ = -∑ i : Fin d, ∑ j : Fin d, ∫ x in U, u.grad x i *
            (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
          simp only [Finset.sum_neg_distrib]
  exact hstep1.trans (hstep2.trans hstep3)

/-! ## Measurability of the pairing against a smooth test matrix -/

/-- **The pairing against a fixed smooth test matrix is measurable in the sample.**
The weak second-derivative identity rewrites it as the `L²` pairing of the
response gradient class — measurable by hypothesis — against a fixed `L²` vector
field, and the inner product is continuous. -/
theorem measurable_inner_smoothProbe_ofMatLp {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : ShellSeq d → H1Function U} {A : ShellSeq d → Vec d → Mat d}
    (hu : Measurable fun omega : ShellSeq d => (u omega).gradToHilbertVectorL2)
    (hA : ∀ omega : ShellSeq d, ∀ i j : Fin d,
      HasWeakPartialDerivOn U j (fun x => (u omega).grad x i) (fun x => A omega x i j))
    (hAmem : ∀ omega : ShellSeq d, ∀ i j : Fin d,
      MeasureTheory.MemLp (fun x => A omega x i j) 2 (volumeMeasureOn U))
    {g : Vec d → HilbertMat d} (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) (hg_compact : HasCompactSupport g)
    (hg_supp : tsupport g ⊆ U) :
    Measurable fun omega : ShellSeq d =>
      inner ℝ (hgL2.toLp g) (hessianCarrierLp (U := U) (A omega) (hAmem omega)) := by
  have hpair : ∀ omega : ShellSeq d,
      inner ℝ (hgL2.toLp g) (hessianCarrierLp (U := U) (A omega) (hAmem omega)) =
        -∑ i : Fin d, ∑ j : Fin d, ∫ x in U,
          (u omega).grad x i *
            (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) :=
    fun omega => inner_toLp_ofMat_eq_neg_sum (U := U) (u := u omega) (A := A omega)
      (hA omega) (hAmem omega) hgL2 hg_cont hg_compact hg_supp
  rw [funext hpair]
  refine Measurable.neg ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hprobe : MemVectorL2 U (fun x : Vec d =>
      (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) • basisVec i) :=
    memVectorL2_smul_basisVec_fderiv (U := U)
      (contDiff_hilbertMat_entry hg_cont i j)
      (hasCompactSupport_hilbertMat_entry hg_compact i j) i j
  have hterm : (fun omega : ShellSeq d => ∫ x in U, (u omega).grad x i *
        (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j)) =
      fun omega : ShellSeq d =>
        inner ℝ ((u omega).gradToHilbertVectorL2) (toHilbertVectorL2OfVecField hprobe) := by
    funext omega
    rw [show (u omega).gradToHilbertVectorL2 =
        toHilbertVectorL2OfVecField (u omega).grad_memVectorL2 from rfl,
      inner_toHilbertVectorL2OfVecField_eq_integral (u omega).grad_memVectorL2 hprobe]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [vecDot_smul_right, vecDot_basisVec_right, mul_comm]
  rw [hterm]
  have hcont : Continuous fun h : HilbertVectorL2 (d := d) U =>
      inner ℝ h (toHilbertVectorL2OfVecField hprobe) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  exact hcont.measurable.comp hu

/-! ## Measurability of the response gradient class -/

/-- **The response gradient class is sample-measurable**, for any family of
Dirichlet responses.  This is the content of
`Section3/Setup/ResponseMeasurabilityB.lean`: the gradient class agrees with the
canonical one, which is the image of the measurable right-hand side under the
continuous solution operator. -/
theorem measurable_gradToHilbertVectorL2_of_isDirichletResponse [NeZero d]
    {LPrime ellPrime m : ℕ} {p : Vec d}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega)) :
    Measurable fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2 := by
  have hfun : (fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2) =
      fun omega : ShellSeq d =>
        (dirichletResponse omega LPrime ellPrime m p).toH1Function.gradToHilbertVectorL2 := by
    funext omega
    exact (gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse omega
        (hw omega)).trans
      (gradToHilbertVectorL2_eq_cubeDirichletGradClass_of_isDirichletResponse omega
        (isDirichletResponse_dirichletResponse omega LPrime ellPrime m p)).symm
  rw [hfun]
  exact measurable_gradToHilbertVectorL2_dirichletResponse

/-! ## The Hessian carrier of a family of weak Hessians -/

/-- **The Hessian carrier of a family of weak Hessians is a measurable `L²`
class**, whenever the response gradient classes are measurable.  This is the
content that was needed for the residue `_hMeasH1`: the weak-Hessian operator is unbounded, but its
`L²` class is a measurable function of the sample. -/
theorem measurable_hessianCarrierLp {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤)
    {u : ShellSeq d → H1Function U} {H : ∀ omega : ShellSeq d, HasWeakHessianOn U (u omega)}
    (hu : Measurable fun omega : ShellSeq d => (u omega).gradToHilbertVectorL2) :
    @Measurable (ShellSeq d) (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) _
      (borel (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)))
      (fun omega : ShellSeq d =>
        hessianCarrierLp (U := U) (fun x i j => (H omega).hess i j x)
          (fun i j => (H omega).hess_memL2 i j)) := by
  refine measurable_of_smoothProbe_inner_measurable (d := d) (U := U) hUopen hUfinite ?_
  intro g hgL2 hg_cont hg_compact hg_supp
  exact measurable_inner_smoothProbe_ofMatLp (U := U) hu
    (fun omega i j => (H omega).weak_second i j)
    (fun omega i j => (H omega).hess_memL2 i j) hgL2 hg_cont hg_compact hg_supp

/-! ## The Hessian norm of the cube is measurable -/

/-- The normalized cube `L^q` norm is a constant multiple of the `L^q` norm for
the restricted volume on the open cube. -/
theorem cubeLpENorm_eq_const_mul_eLpNorm {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {q : ℝ≥0∞} (_hq : q ≠ ⊤) (f : Vec d → E) :
    cubeLpENorm Q q f =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) ^ (1 / q).toReal •
        eLpNorm f q (volumeMeasureOn (openCubeSet Q)) := by
  rw [cubeLpENorm,
    SuperdiffusionCLT.Section3.ResponseFields.normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet Q]
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Homogenization.cubeVolume_pos Q))).ne'
  exact MeasureTheory.eLpNorm_smul_measure_of_ne_zero hc f q _

/-- **`_hMeasH1`, the Hessian half: the cube `L²` norm of the Hessian carrier is
sample-measurable**, for an arbitrary family of weak Hessians of the Dirichlet
response.  The Hessian is not unique, but its `L²` class is, and the class is
measurable by `measurable_hessianCarrierLp`. -/
theorem aemeasurable_cubeLpENorm_hessian_of_hasWeakHessianOn [NeZero d]
    {LPrime ellPrime m : ℕ} {p : Vec d} {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (hHess : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) (w omega).toH1Function) :
    AEMeasurable (fun omega : ShellSeq d =>
      cubeLpENorm (originCube d (m : ℤ)) 2
        (fun x => HilbertMat.ofMat (fun i j => (hHess omega).hess i j x))) mu := by
  have : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet (originCube d (m : ℤ)))) :=
    SuperdiffusionCLT.Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet _
  let eps := MeasureTheory.Lp (HilbertMat d) 2
    (volumeMeasureOn (openCubeSet (originCube d (m : ℤ))))
  let : MeasurableSpace eps := borel eps
  have : BorelSpace eps := ⟨rfl⟩
  have hFmeas : @Measurable (ShellSeq d) eps _
      (borel eps)
      (fun omega : ShellSeq d =>
        hessianCarrierLp (U := openCubeSet (originCube d (m : ℤ)))
          (fun x i j => (hHess omega).hess i j x)
          (fun i j => (hHess omega).hess_memL2 i j)) :=
    measurable_hessianCarrierLp (U := openCubeSet (originCube d (m : ℤ)))
      (isOpen_openCubeSet _) (ne_of_lt (volume_openCubeSet_lt_top _))
      (measurable_gradToHilbertVectorL2_of_isDirichletResponse hw)
  have hnorm : Measurable fun omega : ShellSeq d =>
      ‖hessianCarrierLp (U := openCubeSet (originCube d (m : ℤ)))
        (fun x i j => (hHess omega).hess i j x)
        (fun i j => (hHess omega).hess_memL2 i j)‖ₑ :=
    hFmeas.enorm
  have hEqFun : (fun omega : ShellSeq d =>
      ‖hessianCarrierLp (U := openCubeSet (originCube d (m : ℤ)))
        (fun x i j => (hHess omega).hess i j x)
        (fun i j => (hHess omega).hess_memL2 i j)‖ₑ) =
      fun omega : ShellSeq d => eLpNorm
        (fun x => HilbertMat.ofMat (fun i j => (hHess omega).hess i j x)) 2
        (volumeMeasureOn (openCubeSet (originCube d (m : ℤ)))) := by
    funext omega
    rw [MeasureTheory.Lp.enorm_def]
    exact MeasureTheory.eLpNorm_congr_ae
      (memLp_hilbertMat_ofMat (U := openCubeSet (originCube d (m : ℤ)))
        (fun i j => (hHess omega).hess_memL2 i j)).coeFn_toLp
  have hE : Measurable fun omega : ShellSeq d => eLpNorm
      (fun x => HilbertMat.ofMat (fun i j => (hHess omega).hess i j x)) 2
      (volumeMeasureOn (openCubeSet (originCube d (m : ℤ)))) := by
    rw [← hEqFun]
    exact hnorm
  rw [funext fun omega => cubeLpENorm_eq_const_mul_eLpNorm (d := d)
    (originCube d (m : ℤ)) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) _]
  exact ((measurable_const (a := ENNReal.ofReal ((cubeVolume (originCube d (m : ℤ)))⁻¹) ^ (1 / (2 : ℝ≥0∞)).toReal)).smul hE).aemeasurable

/-! ## The residue `_hMeasH1` -/

/-- **`_hMeasH1`, discharged for an arbitrary family of weak Hessians**: the
`H̲¹(cu_m)` carrier of the response is sample-measurable. -/
theorem aemeasurable_vecCubeH1ENorm_grad_of_hasWeakHessianOn [NeZero d]
    {LPrime ellPrime m : ℕ} {p : Vec d} {mu : MeasureTheory.Measure (ShellSeq d)}
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (m : ℤ)))}
    (hw : ∀ omega : ShellSeq d, IsDirichletResponse omega LPrime ellPrime m p (w omega))
    (hHess : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (m : ℤ))) (w omega).toH1Function) :
    AEMeasurable (fun omega : ShellSeq d =>
      vecCubeH1ENorm (originCube d (m : ℤ)) (w omega).toH1Function.grad
        (fun x => fun i j => (hHess omega).hess i j x)) mu :=
  aemeasurable_vecCubeH1ENorm_grad_of_hessian hw
    (fun omega x i j => (hHess omega).hess i j x)
    (aemeasurable_cubeLpENorm_hessian_of_hasWeakHessianOn hw hHess)

/-- **The residue `_hMeasH1` of the statement of `l.RHS.term1`, discharged at
the canonical weak-Hessian witness** `canonicalResponseHessian` of
`RHSTerm1WeakHessian.lean`.  This is the exact shape of the `_hMeasH1` binder of
`term1_of_residueB`, so no reduction is left. -/
theorem aemeasurable_vecCubeH1ENorm_grad_canonicalResponseHessian [NeZero d]
    (hd : 2 ≤ d) (S : ScaleSelection) (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (e : Vec d)
    {w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ)))}
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    AEMeasurable (fun omega : ShellSeq d =>
      vecCubeH1ENorm (originCube d (S.m : ℤ)) (w omega).toH1Function.grad
        (fun x => fun i j =>
          (canonicalResponseHessian d hd S nu P e w hw omega).hess i j x))
      P.toMeasure :=
  aemeasurable_vecCubeH1ENorm_grad_of_hasWeakHessianOn
    (LPrime := S.LPrime) (ellPrime := S.ellPrime) (m := S.m)
    (p := testVector nu S.LPrime P S.n e) (mu := P.toMeasure) hw
    (canonicalResponseHessian d hd S nu P e w hw)

end

end SuperdiffusionCLT.Section3.Terms
