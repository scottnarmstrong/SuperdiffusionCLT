/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RFiniteB
public import SuperdiffusionCLT.Section3.Terms.ResponseHessianMeasurableB
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityC
public import SuperdiffusionCLT.Section3.Setup.ResponseMeasurabilityD
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2FinalB

/-!
# The integrability block of the term-2 assembly

## Summary

The term-2 assembly carries four binders
describing the annealed integrability of the term-2 integrand, at the named
weak-Jacobian witness `canonicalRJacobian`:

* `hfinR` — finiteness of the annealed squared `L̲²(cu_m)` norm of
  `R = (k_{L'} − k_ℓ) ∇w`;
* `hFinDR` — finiteness of the annealed squared `L̲²(cu_m)` norm of the weak
  Jacobian `DR` of `R`, read through the `HilbertMat` carrier;
* `hMeasDR` — sample-measurability of the same `L̲²(cu_m)` norm;
* `hDispDR` — the display `e.RHS.term2.R.bounds` at the literal `C₁ = 1`.

This module discharges `hfinR` and `hMeasDR` at the exact binder shape of
the term-2 assembly:

* `term2_hfinR_integrability` is `RHSTerm2RFiniteB.term2_hfinR`,
  which carries **no** hypotheses beyond the standing shell laws;
* `term2_hMeasDR_integrability` discharges `hMeasDR` from the
  measurability engines: the weak-gradient pairing identity
  (`inner_toLp_ofMat_eq_negSum_weakGradient`) identifies the `L²` pairing of the
  Jacobian carrier against a smooth test function with the flux pairing
  `∫ ⟪∇w, Aᵀ φ⟫`, and the flux pairing is a continuous functional of two
  sample-measurable `L²` classes (`measurable_gradToHilbertVectorL2_of_isDirichletResponse`
  and `measurable_toHilbertVectorL2OfVecField_of_measurable`), so the
  smooth-test-function engine `measurable_of_smoothProbe_inner_measurable` closes it.

`hFinDR` and `hDispDR` are **not** discharged in this file.  The two `##` notes
"The clause `hFinDR`" and "The clause `hDispDR`" below say where they are treated.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.ResponseFields
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `hfinR`: the annealed second moment of `R = (k_{L'} − k_ℓ) ∇w` -/

/-- **`hfinR`, discharged without residue.**  This is
`RHSTerm2RFiniteB.term2_hfinR` re-stated at the exact shape of the `hfinR`
binder of the term-2 assembly: the route is Hölder `(4,4) → 2` on the cube
against the canonical increment density `x ↦ ‖k_{L'}(x) − k_ℓ(x)‖_op` (whose
annealed fourth moment is the stream-increment display, read at `p = 4`)
and the response gradient (whose annealed fourth moment is the first clause of
the response anchor `w_basic_regbounds`).

The theorem carries no hypothesis beyond `d`, `2 ≤ d`, the two spectral
parameters, the five shell laws, the scale selection, the unit test vector and
the Dirichlet-response selection `w`. -/
theorem term2_hfinR_integrability (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ1V2 : ShellLawJ1Restriction d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (e : Vec d) (he : vecNormSq e = 1)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun y => matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                (coefficientCutoff nu omega S.ell).toCoeffField y)
              ((w omega).toH1Function.grad y)) ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ :=
  term2_hfinR d hd nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw

/-! ## The weak-gradient pairing identity for a general matrix field

`ResponseHessianMeasurableB.inner_toLp_ofMat_eq_neg_sum` pairs an `L²` matrix
field against a smooth test function through the weak *second* derivatives of a single
`H¹` function.  The weak Jacobian of `R = (k_{L'} − k_ℓ) ∇w` pairs the other
way round: its entries are the weak derivatives of the *flux* components
`(k_{L'} − k_ℓ) ∇w`, which are not themselves the gradient of an `H¹` function.
The statement below is the same computation with the `H¹` gradient abstracted to
an arbitrary family `F` of weak-derivative primitives, which is what the
measurability engine of the next section consumes. -/

/-- **The weak-gradient pairing identity.**  If `F i` has weak partial
derivative `A · i j` in direction `j` on `U`, then the `L²(U; Mat)` pairing of
the carrier of `A` against a smooth compactly supported test function `g` is minus the
sum of the pairings of the `F i` against the test function's derivatives. -/
theorem inner_toLp_ofMat_eq_negSum_weakGradient {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {F : Fin d → Vec d → ℝ} {A : Vec d → Mat d}
    (hA : ∀ i j : Fin d, HasWeakPartialDerivOn U j (F i) (fun x => A x i j))
    (hAmem : ∀ i j : Fin d, MeasureTheory.MemLp (fun x => A x i j) 2 (volumeMeasureOn U))
    {g : Vec d → HilbertMat d} (hgL2 : MeasureTheory.MemLp g 2 (volumeMeasureOn U))
    (hg_cont : ContDiff ℝ (⊤ : ℕ∞) g) (hg_compact : HasCompactSupport g)
    (hg_supp : tsupport g ⊆ U) :
    inner ℝ (hgL2.toLp g) (hessianCarrierLp (U := U) A hAmem) =
      -∑ i : Fin d, ∑ j : Fin d, ∫ x in U,
        F i x * (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
  have hmem : MeasureTheory.MemLp (fun x : Vec d => HilbertMat.ofMat (A x)) 2
      (volumeMeasureOn U) :=
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
        F i x * (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
    have hterm : ∀ i j : Fin d,
        (∫ x : Vec d, ((g x).ofLp i).ofLp j * A x i j ∂(volumeMeasureOn U)) =
          -∫ x in U, F i x *
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
        = ∑ i : Fin d, ∑ j : Fin d, -∫ x in U, F i x *
            (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j
      _ = -∑ i : Fin d, ∑ j : Fin d, ∫ x in U, F i x *
            (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) := by
          simp only [Finset.sum_neg_distrib]
  exact hstep1.trans (hstep2.trans hstep3)

/-! ## The flux pairing is sample-measurable -/

/-- **The flux pairing `ω ↦ ∫ (A ∇w)_i ψ` is measurable in the sample**, for the
cutoff-difference matrix field `A = k_{L₁} − k_{L₂}`, an arbitrary measurable
family of response gradients and a fixed continuous compactly supported scalar
weight `ψ`.

The cutoff difference is jointly measurable in the sample and the point and
continuous in the point (`measurable_prod_coefficientCutoff_sub`,
`continuous_coefficientCutoff_sub_entry`), so the transposed vector field
`x ↦ (Aᵀ(ψ • e_i))` has a *measurable* `L²` class map
(`measurable_toHilbertVectorL2OfVecField_of_measurable`); the pairing is then the
continuous inner product of that class with the response gradient class
(`inner_toHilbertVectorL2OfVecField_eq_integral`), which is measurable by
hypothesis. -/
private theorem measurable_setIntegral_coeffDiff_flux_mul {U : Set (Vec d)}
    (nu : ℝ) (L₁ L₂ : ℕ)
    {w : ShellSeq d → H10Function U}
    (hw : Measurable fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2)
    {ψ : Vec d → ℝ} (hψc : Continuous ψ) (hψcpt : HasCompactSupport ψ) (i : Fin d) :
    Measurable fun omega : ShellSeq d =>
      ∫ x in U, (matVecMul ((coefficientCutoff nu omega L₁).toCoeffField x -
          (coefficientCutoff nu omega L₂).toCoeffField x)
        ((w omega).toH1Function.grad x)) i * ψ x := by
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  have hGmem : ∀ omega : ShellSeq d, MemVectorL2 U
      (fun x => fun j : Fin d =>
        ((coefficientCutoff nu omega L₁).toCoeffField x -
          (coefficientCutoff nu omega L₂).toCoeffField x) i j * ψ x) := by
    intro omega
    rw [MemVectorL2]
    refine MeasureTheory.MemLp.of_eval fun j => ?_
    have hcont : Continuous fun x : Vec d =>
        ((coefficientCutoff nu omega L₁).toCoeffField x -
          (coefficientCutoff nu omega L₂).toCoeffField x) i j * ψ x :=
      (continuous_coefficientCutoff_sub_entry nu omega L₁ L₂ i j).mul hψc
    exact hcont.memLp_of_hasCompactSupport (μ := volumeMeasureOn U) hψcpt.mul_left
  have hGm : Measurable fun q : ShellSeq d × Vec d => (fun j : Fin d =>
      ((coefficientCutoff nu q.1 L₁).toCoeffField q.2 -
        (coefficientCutoff nu q.1 L₂).toCoeffField q.2) i j * ψ q.2) := by
    refine Measurable.of_eval fun j => ?_
    have h1 : Measurable fun q : ShellSeq d × Vec d =>
        ((coefficientCutoff nu q.1 L₁).toCoeffField q.2 -
          (coefficientCutoff nu q.1 L₂).toCoeffField q.2) i j :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        (measurable_prod_coefficientCutoff_sub nu L₁ L₂))
    exact h1.mul (hψc.measurable.comp measurable_snd)
  have hclass : Measurable fun omega : ShellSeq d =>
      toHilbertVectorL2OfVecField (hGmem omega) :=
    measurable_toHilbertVectorL2OfVecField_of_measurable (U := U) hGm hGmem
  have hid : (fun omega : ShellSeq d => ∫ x in U,
        (matVecMul ((coefficientCutoff nu omega L₁).toCoeffField x -
            (coefficientCutoff nu omega L₂).toCoeffField x)
          ((w omega).toH1Function.grad x)) i * ψ x) =
      fun omega : ShellSeq d => inner ℝ ((w omega).toH1Function.gradToHilbertVectorL2)
        (toHilbertVectorL2OfVecField (hGmem omega)) := by
    funext omega
    rw [show (w omega).toH1Function.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField (w omega).toH1Function.grad_memVectorL2 from rfl]
    rw [inner_toHilbertVectorL2OfVecField_eq_integral]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (matVecMul ((coefficientCutoff nu omega L₁).toCoeffField x -
          (coefficientCutoff nu omega L₂).toCoeffField x)
        ((w omega).toH1Function.grad x)) i * ψ x =
      vecDot ((w omega).toH1Function.grad x) (fun j : Fin d =>
        ((coefficientCutoff nu omega L₁).toCoeffField x -
          (coefficientCutoff nu omega L₂).toCoeffField x) i j * ψ x)
    rw [vecDot, matVecMul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hid]
  exact continuous_inner.measurable.comp (hw.prodMk hclass)

/-! ## The weak-Jacobian carrier is sample-measurable -/

/-- **The `HilbertMat` carrier of a family of weak Jacobians is a measurable
`L²` class.**  The weak Jacobian of the flux `R = (k_{L₁} − k_{L₂}) ∇w` is not
the gradient of an `H¹` function, but each of its rows is the weak gradient of
the corresponding component of the flux; the smooth-test-function engine of
`ResponseHessianMeasurableB.measurable_of_smoothProbe_inner_measurable` pairs it
against a test function, and the pairing identity
`inner_toLp_ofMat_eq_negSum_weakGradient` reduces that pairing to the finite sum
of flux pairings `∫ (A ∇w)_i ∂_j φ`, each measurable in the sample by
`measurable_setIntegral_coeffDiff_flux_mul`. -/
private theorem measurable_rJacobianCarrierLp {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : volume U ≠ ⊤)
    (nu : ℝ) (L₁ L₂ : ℕ)
    {w : ShellSeq d → H10Function U}
    (hw : Measurable fun omega : ShellSeq d => (w omega).toH1Function.gradToHilbertVectorL2)
    {A : ShellSeq d → Vec d → Mat d}
    (hAwg : ∀ (omega : ShellSeq d) (i : Fin d),
      HasWeakGradientOn U
        (fun x => (matVecMul ((coefficientCutoff nu omega L₁).toCoeffField x -
            (coefficientCutoff nu omega L₂).toCoeffField x)
          ((w omega).toH1Function.grad x)) i) (fun x j => A omega x i j))
    (hAmem : ∀ (omega : ShellSeq d) (i j : Fin d),
      MeasureTheory.MemLp (fun x => A omega x i j) 2 (volumeMeasureOn U)) :
    @Measurable (ShellSeq d) (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)) _
      (borel (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U)))
      (fun omega : ShellSeq d => hessianCarrierLp (U := U) (A omega) (hAmem omega)) := by
  refine measurable_of_smoothProbe_inner_measurable (d := d) (U := U) hUopen hUfinite ?_
  intro g hgL2 hg_cont hg_compact hg_supp
  have hpair : ∀ omega : ShellSeq d,
      inner ℝ (hgL2.toLp g) (hessianCarrierLp (U := U) (A omega) (hAmem omega)) =
        -∑ i : Fin d, ∑ j : Fin d, ∫ x in U,
          (matVecMul ((coefficientCutoff nu omega L₁).toCoeffField x -
              (coefficientCutoff nu omega L₂).toCoeffField x)
            ((w omega).toH1Function.grad x)) i *
          (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j) :=
    fun omega => inner_toLp_ofMat_eq_negSum_weakGradient (U := U)
      (F := fun i x => (matVecMul ((coefficientCutoff nu omega L₁).toCoeffField x -
          (coefficientCutoff nu omega L₂).toCoeffField x)
        ((w omega).toH1Function.grad x)) i)
      (A := A omega) (fun i j => hAwg omega i j) (hAmem omega)
      hgL2 hg_cont hg_compact hg_supp
  rw [funext hpair]
  refine Measurable.neg ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hφc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => ((g y).ofLp i).ofLp j) :=
    contDiff_hilbertMat_entry hg_cont i j
  have hφcpt : HasCompactSupport (fun y : Vec d => ((g y).ofLp i).ofLp j) :=
    hasCompactSupport_hilbertMat_entry hg_compact i j
  have hψc : Continuous (fun x : Vec d =>
      (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j)) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψcpt : HasCompactSupport (fun x : Vec d =>
      (fderiv ℝ (fun y : Vec d => ((g y).ofLp i).ofLp j) x) (basisVec j)) :=
    hφcpt.fderiv_apply (𝕜 := ℝ) (basisVec j)
  exact measurable_setIntegral_coeffDiff_flux_mul (U := U) nu L₁ L₂ hw hψc hψcpt i

/-! ## `hMeasDR`: the annealed `L̲²(cu_m)` norm of the Jacobian is measurable -/

/-- **`hMeasDR` discharged at the named witness.**  The
sample-measurability of `ω ↦ ‖DR(ω)‖_{L̲²(cu_m)}` at the canonical weak Jacobian
`canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e) w hw`.

The norm of the `HilbertMat` carrier class is measurable because the class map is
(`measurable_rJacobianCarrierLp` at the cube `cu_m`, fed by the
weak-gradient and `L²` conjuncts `canonicalRJacobian_hasWeakGradientOn` and by
`gradMemL2On_streamGradJacobian`), and the normalized cube `L²` norm is the
`eLpNorm` of the carrier up to the constant factor
`ofReal (cubeVolume)⁻¹ ^ (1/2)`. -/
theorem term2_hMeasDR_integrability (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (testVector nu S.LPrime P S.n e) (w omega)) :
    AEMeasurable (fun omega : ShellSeq d =>
        cubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => HilbertMat.ofMat (fun i j =>
            canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
              w hw omega i x j)))
      P.toMeasure := by
  have : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ)))) :=
    instIsFiniteMeasureVolumeMeasureOnOpenCubeSet _
  let eps := MeasureTheory.Lp (HilbertMat d) 2
    (volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ))))
  let : MeasurableSpace eps := borel eps
  have : BorelSpace eps := ⟨rfl⟩
  have hgradm : Measurable fun omega : ShellSeq d =>
      (w omega).toH1Function.gradToHilbertVectorL2 :=
    measurable_gradToHilbertVectorL2_of_isDirichletResponse hw
  have hwg := canonicalRJacobian_hasWeakGradientOn d hd nu S hSorder
    (testVector nu S.LPrime P S.n e) w hw
  have hellell := ell_le_LPrime_of_scalesOrdering hSorder
  have hmem : ∀ (omega : ShellSeq d) (i j : Fin d),
      MeasureTheory.MemLp (fun x => canonicalRJacobian d hd S hSorder
        (testVector nu S.LPrime P S.n e) w hw omega i x j) 2
        (volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ)))) := by
    intro omega i j
    have h := gradMemL2On_streamGradJacobian omega hellell
      (rfieldHessianWitness d hd S hSorder (testVector nu S.LPrime P S.n e) w hw omega) i j
    simpa only [canonicalRJacobian, rfieldWeakJacobian, MemL2On] using h
  have hFmeas : @Measurable (ShellSeq d) eps _
      (borel eps)
      (fun omega : ShellSeq d =>
        hessianCarrierLp (U := openCubeSet (originCube d (S.m : ℤ)))
          (fun x i j => canonicalRJacobian d hd S hSorder
            (testVector nu S.LPrime P S.n e) w hw omega i x j)
          (hmem omega)) :=
    measurable_rJacobianCarrierLp (U := openCubeSet (originCube d (S.m : ℤ)))
      (isOpen_openCubeSet _) (ne_of_lt (volume_openCubeSet_lt_top _))
      nu S.LPrime S.ell hgradm (fun omega i => hwg.1 omega i) hmem
  have hnorm : Measurable fun omega : ShellSeq d =>
      ‖hessianCarrierLp (U := openCubeSet (originCube d (S.m : ℤ)))
        (fun x i j => canonicalRJacobian d hd S hSorder
          (testVector nu S.LPrime P S.n e) w hw omega i x j)
        (hmem omega)‖ₑ :=
    hFmeas.enorm
  have hEqFun : (fun omega : ShellSeq d =>
      ‖hessianCarrierLp (U := openCubeSet (originCube d (S.m : ℤ)))
        (fun x i j => canonicalRJacobian d hd S hSorder
          (testVector nu S.LPrime P S.n e) w hw omega i x j)
        (hmem omega)‖ₑ) =
      fun omega : ShellSeq d => eLpNorm
        (fun x => HilbertMat.ofMat (fun i j =>
          canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
            w hw omega i x j)) 2
        (volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ)))) := by
    funext omega
    rw [MeasureTheory.Lp.enorm_def]
    exact MeasureTheory.eLpNorm_congr_ae (memLp_hilbertMat_ofMat (hmem omega)).coeFn_toLp
  have hE : Measurable fun omega : ShellSeq d => eLpNorm
      (fun x => HilbertMat.ofMat (fun i j =>
        canonicalRJacobian d hd S hSorder (testVector nu S.LPrime P S.n e)
          w hw omega i x j)) 2
      (volumeMeasureOn (openCubeSet (originCube d (S.m : ℤ)))) := by
    rw [← hEqFun]
    exact hnorm
  rw [funext fun omega => cubeLpENorm_eq_const_mul_eLpNorm (d := d)
    (originCube d (S.m : ℤ)) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) _]
  exact (hE.const_smul (ENNReal.ofReal ((cubeVolume (originCube d (S.m : ℤ)))⁻¹) ^
    (1 / (2 : ℝ≥0∞)).toReal)).aemeasurable

/-! ## The clause `hFinDR`

The finiteness clause `hFinDR` is not treated in this file; it is proved as
`RHSTerm2FinDR.term2_hFinDR_integrability`.  The route to the annealed finiteness
of `∫⁻ ‖DR(ω)‖²_{L̲²(cu_m)}` is the product rule at the canonical Jacobian,

`‖DR(ω, x)‖ ≤ KN(ω, x) · |∇w(ω, x)| + GN(ω, x) · ‖∂²w(ω, x)‖`,

with the densities `KN = matrixOperatorNorm (finiteShellIncrement ω ℓ L')` and
`GN = ShellField.matrixDerivativeNorm (∑_{k ∈ (ℓ, L']} ∂ k)`.  Each of the four
resulting factors has finite annealed fourth moment: `KN` from
`annealed_L4_increment_le`, `GN` from `annealed_L4_increment_gradient_le`, and
the two response densities from the anchor `w_basic_regbounds`, exactly
as in the proof of the display `e.RHS.term2.R.bounds`.  The inequality
above is the pointwise hypothesis `hDRpt` carried by the gradient and the full
forms of that display; at the operator-norm density `GN` it is
false in dimension three (`RHSTerm2DispersionFinal`), and the correct form pays
the Hilbert–Schmidt factor `√d` on the `∂K` block
(`RHSTerm2DispersionFinal.derivContraction_norm_le`). -/

/-! ## The clause `hDispDR`

The display `hDispDR` is the paper's `e.RHS.term2.R.bounds` at the literal
constant `C₁ = 1`.  The existential form of the display
is the statement
`∃ C, 1 ≤ C ∧ (norm half) + 3^ℓ (gradient half) ≤ C · L' · |p|`, with realized
constant `C = 3 · max (knValueAnnealedConst d) knGradientAnnealedConst ·
(2 · gammaMomentConst 2 · Cwb · √(1 + h))`, where `Cwb ≥ 1` is the constant of
`w_basic_regbounds` and `1 ≤ h` from `e.scale.selection`.  Every factor is at
least `1`, so the realized constant is at least `3`; an existential bound at
some `C ≥ 1` cannot be read back as the same bound at `C = 1`, since the two
sides share no parameter that could absorb the factor.  The paper's constant `C`
is unspecified, so the binder is relaxed to an arbitrary `C₁` in
`RHSTerm2DispConst` and discharged at a dimension-only constant in
`RHSTerm2DispCanonical`. -/

end

end SuperdiffusionCLT.Section3.Terms
