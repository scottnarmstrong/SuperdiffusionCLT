/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeHatOrderOne
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section3.ResponseFields.StationaryComparison
public import Homogenization.Sobolev.Foundations.CubeCoerciveH1

/-!
# The multiscale Poincare inequality for the order-one hatted negative norm

The display `e.apply.multiscale.Poincare`, at the endpoint `s = 1`, `p = 2` of
`e.jk.Hminus.endpoint`. This module carries the deterministic part of that endpoint
for the order-one carrier `SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne`:
the real square averages `‖F‖²_{L̲²(Q)}`, the descendant averages of the printed depth
moment `avsum_{R∈D_j(Q)}|(F)_R|²`, the cube Poincare inequality for a smooth
gradient field (the coercive estimate
`Homogenization.cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm`
of the library, re-derived here), and the two real readings of the
order-one test constraint. The bound is in `ShellHminusEndpointOrderOneB`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `L̲²` on a cube as a real square average -/

/-- Every continuous field is `L²` for the normalized measure of a triadic
cube: the cube is bounded, so the field is bounded on its compact closure. -/
theorem memLp_two_normalizedCubeMeasure_of_continuous {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) {f : Vec d → E}
    (hf : Continuous f) : MemLp f 2 (normalizedCubeMeasure Q) := by
  obtain ⟨C, hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn
    (hf.norm.continuousOn)
  have hae : ∀ᵐ x ∂(normalizedCubeMeasure Q), ‖f x‖ ≤ C := by
    rw [normalizedCubeMeasure]
    refine Measure.ae_smul_measure ?_ _
    rw [cubeMeasure]
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    simpa only [Real.norm_eq_abs, abs_norm] using hC x (subset_closure hx)
  exact MemLp.of_bound hf.aestronglyMeasurable C hae

/-- `‖f‖²_{L̲²(Q)}` as a real number. -/
def cubeSquareAverage {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    (f : Vec d → E) : ℝ :=
  volumeAverage (cubeSet Q) (fun x => ‖f x‖ ^ 2)

theorem cubeSquareAverage_nonneg {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (f : Vec d → E) :
    0 ≤ cubeSquareAverage Q f := by
  have hvol : (0 : ℝ) ≤ (volume (cubeSet Q)).toReal⁻¹ := by positivity
  refine mul_nonneg hvol ?_
  refine setIntegral_nonneg (measurableSet_cubeSet Q) fun x _ => by positivity

/-- **The real square average is the square of the `L̲²(Q)` norm.** -/
theorem toReal_cubeLpENorm_two_sq {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (cubeLpENorm Q 2 f).toReal ^ 2 = cubeSquareAverage Q f := by
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (normalizedCubeMeasure Q) :=
    MemLp.integrable_norm_pow' hf
  have hlin : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂(normalizedCubeMeasure Q) =
      ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂(normalizedCubeMeasure Q)) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hsq : cubeLpENorm Q 2 f ^ (2 : ℕ) =
      ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂(normalizedCubeMeasure Q)) := by
    rw [cubeLpENorm, eLpNorm_two_sq _ _ hf.aestronglyMeasurable, hlin]
  have h1 : (cubeLpENorm Q 2 f).toReal ^ 2 = (cubeLpENorm Q 2 f ^ (2 : ℕ)).toReal := by
    rw [ENNReal.toReal_pow]
  rw [h1, hsq, ENNReal.toReal_ofReal (by positivity), cubeSquareAverage,
    volumeAverage, volume_cubeSet_toReal, ← cubeAverage,
    cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The `L̲²(Q)` norm of a continuous field is the square root of its real
square average. -/
theorem toReal_cubeLpENorm_two_eq_sqrt {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {f : Vec d → E} (hf : Continuous f) :
    (cubeLpENorm Q 2 f).toReal = Real.sqrt (cubeSquareAverage Q f) := by
  rw [← toReal_cubeLpENorm_two_sq Q (memLp_two_normalizedCubeMeasure_of_continuous Q hf),
    Real.sqrt_sq ENNReal.toReal_nonneg]

/-- `‖F‖²_{L̲²(Q)}` for a vector field. -/
def vecSqAvg (Q : TriadicCube d) (F : Vec d → Vec d) : ℝ :=
  cubeSquareAverage Q (hilbertifyVecField F)

/-- `‖M‖²_{L̲²(Q)}` for a matrix field, in the Frobenius carrier. -/
def matSqAvg (Q : TriadicCube d) (M : Vec d → Mat d) : ℝ :=
  cubeSquareAverage Q (fun x => HilbertMat.ofMat (M x))

theorem continuous_hilbertifyVecField {F : Vec d → Vec d} (hF : Continuous F) :
    Continuous (hilbertifyVecField F) :=
  (HilbertVec.ofVecL d).continuous.comp hF

theorem vecSqAvg_nonneg (Q : TriadicCube d) (F : Vec d → Vec d) :
    0 ≤ vecSqAvg Q F :=
  cubeSquareAverage_nonneg Q (hilbertifyVecField F)

theorem toReal_vecCubeLpENorm_eq_sqrt (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : Continuous F) :
    (vecCubeLpENorm Q 2 F).toReal = Real.sqrt (vecSqAvg Q F) :=
  toReal_cubeLpENorm_two_eq_sqrt Q (continuous_hilbertifyVecField hF)

/-! ## The partition identity, Cauchy-Schwarz and Jensen -/

/-- **Cauchy-Schwarz on one triadic cube**, in the real square-average form. -/
theorem abs_volumeAverage_vecDot_le_sqrt_mul_sqrt (R : TriadicCube d)
    {F G : Vec d → Vec d} (hF : Continuous F) (hG : Continuous G) :
    |volumeAverage (cubeSet R) (fun x => vecDot (F x) (G x))| ≤
      Real.sqrt (vecSqAvg R F) * Real.sqrt (vecSqAvg R G) := by
  have h := SuperdiffusionCLT.Section2.Norms.abs_volumeAverage_vecDot_le_mul
    (Q := R) (a := F) (b := G)
    (memLp_two_normalizedCubeMeasure_of_continuous R (continuous_hilbertifyVecField hF))
    (memLp_two_normalizedCubeMeasure_of_continuous R (continuous_hilbertifyVecField hG))
  rwa [toReal_vecCubeLpENorm_eq_sqrt R hF, toReal_vecCubeLpENorm_eq_sqrt R hG] at h

/-- A constant vector comes out of a normalized average of a pairing. -/
theorem volumeAverage_vecDot_const_left (U : Set (Vec d)) (c : Vec d)
    {F : Vec d → Vec d} (hF : ∀ i, IntegrableOn (fun y => F y i) U volume) :
    volumeAverage U (fun y => vecDot c (F y)) = vecDot c (volumeAverageVec U F) := by
  have hint : ∫ y in U, (∑ i, c i * F y i) ∂volume
      = ∑ i, c i * ∫ y in U, F y i ∂volume := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hF i).const_mul (c i))]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp only [volumeAverage, vecDot, volumeAverageVec]
  rw [hint, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Jensen on one triadic cube**: the length of the cube average of a
continuous field is at most its `L̲²` norm. -/
theorem vecNorm_volumeAverageVec_le_sqrt (R : TriadicCube d) {F : Vec d → Vec d}
    (hF : Continuous F) :
    vecNorm (volumeAverageVec (cubeSet R) F) ≤ Real.sqrt (vecSqAvg R F) := by
  set c : Vec d := volumeAverageVec (cubeSet R) F with hc
  have hint : ∀ i, IntegrableOn (fun y : Vec d => F y i) (cubeSet R) volume :=
    fun i => integrableOn_cubeSet_of_continuous R ((continuous_apply i).comp hF)
  have hconst : Continuous (fun _ : Vec d => c) := continuous_const
  have hkey : vecNormSq c = volumeAverage (cubeSet R) (fun x => vecDot c (F x)) := by
    rw [volumeAverage_vecDot_const_left (cubeSet R) c hint, ← hc]
    rfl
  have hCS := abs_volumeAverage_vecDot_le_sqrt_mul_sqrt R hconst hF
  have hcnorm : Real.sqrt (vecSqAvg R (fun _ : Vec d => c)) ≤ vecNorm c := by
    have hle : vecSqAvg R (fun _ : Vec d => c) ≤ vecNorm c ^ 2 := by
      have hpt : (fun x : Vec d => ‖hilbertifyVecField (fun _ : Vec d => c) x‖ ^ 2)
          = fun _ : Vec d => vecNorm c ^ 2 := rfl
      rw [vecSqAvg, cubeSquareAverage, hpt, volumeAverage, setIntegral_const,
        measureReal_def, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (by
          have := volume_cubeSet_toReal_pos R
          exact ne_of_gt this), one_mul]
    calc Real.sqrt (vecSqAvg R (fun _ : Vec d => c))
        ≤ Real.sqrt (vecNorm c ^ 2) := Real.sqrt_le_sqrt hle
      _ = vecNorm c := Real.sqrt_sq (vecNorm_nonneg c)
  have hsq : vecNorm c ^ 2 ≤ vecNorm c * Real.sqrt (vecSqAvg R F) := by
    have h1 : vecNormSq c ≤ Real.sqrt (vecSqAvg R (fun _ : Vec d => c)) *
        Real.sqrt (vecSqAvg R F) := by
      rw [hkey]
      exact le_trans (le_abs_self _) hCS
    have h2 : Real.sqrt (vecSqAvg R (fun _ : Vec d => c)) * Real.sqrt (vecSqAvg R F) ≤
        vecNorm c * Real.sqrt (vecSqAvg R F) :=
      mul_le_mul_of_nonneg_right hcnorm (Real.sqrt_nonneg _)
    rw [vecNorm_sq_eq_vecNormSq]
    linarith only [h1, h2]
  rcases eq_or_lt_of_le (vecNorm_nonneg c) with h0 | h0
  · rw [← h0]
    exact Real.sqrt_nonneg _
  · have hmul : vecNorm c * vecNorm c ≤ vecNorm c * Real.sqrt (vecSqAvg R F) := by
      rw [← pow_two]
      exact hsq
    exact le_of_mul_le_mul_left hmul h0

/-! ## The Poincare inequality on one triadic cube for a smooth gradient field -/

/-- A normalized cube average of a nonnegative integrand is nonnegative. -/
theorem volumeAverage_cubeSet_nonneg (R : TriadicCube d) {f : Vec d → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ volumeAverage (cubeSet R) f := by
  have hvol : (0 : ℝ) ≤ (volume (cubeSet R)).toReal⁻¹ := by positivity
  exact mul_nonneg hvol
    (setIntegral_nonneg (measurableSet_cubeSet R) fun x _ => hf x)

/-- A finite sum comes out of a normalized cube average of continuous
integrands. -/
theorem volumeAverage_cubeSet_finset_sum (R : TriadicCube d)
    (f : Fin d → Vec d → ℝ) (hf : ∀ i, Continuous (f i)) :
    volumeAverage (cubeSet R) (fun x => ∑ i, f i x) =
      ∑ i, volumeAverage (cubeSet R) (f i) := by
  classical
  simp only [volumeAverage]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => integrableOn_cubeSet_of_continuous R (hf i)), Finset.mul_sum]

/-- The Euclidean gradient of a globally smooth potential is continuous. -/
theorem continuous_euclideanGradient' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (euclideanGradient g) := by
  have hfd : Continuous (fun x : Vec d => fderiv ℝ g x) :=
    hg.continuous_fderiv (by simp)
  exact continuous_pi fun i => hfd.clm_apply continuous_const

/-- The dimension-only Poincare constant of a triadic cube: the coercive
constant of the centred unit cube, upstream
`Homogenization.cubeBesovW12LocalPoincareConstant`. -/
def poincareCubeConst (d : ℕ) : ℝ := cubeBesovW12LocalPoincareConstant d

theorem poincareCubeConst_nonneg (d : ℕ) : 0 ≤ poincareCubeConst d :=
  cubeBesovW12LocalPoincareConstant_nonneg d

/-- Each partial derivative of a globally smooth potential is `C¹`. -/
theorem contDiff_one_euclideanGradient_apply {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    ContDiff ℝ 1 (fun y : Vec d => euclideanGradient g y i) := by
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => fderiv ℝ g y) :=
    hg.fderiv_right (by simp)
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => fderiv ℝ g y (basisVec i)) :=
    hfd.clm_apply contDiff_const
  exact h.of_le (by exact_mod_cast le_top)

/-- The Hessian of a globally smooth potential is continuous. -/
theorem continuous_euclideanGradientJacobian' {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (euclideanGradientJacobian g) := by
  have h : ∀ i j : Fin d,
      Continuous (fun x : Vec d => euclideanGradientJacobian g x i j) := by
    intro i j
    have hfd : Continuous (fun y : Vec d =>
        fderiv ℝ (fun z : Vec d => euclideanGradient g z i) y) :=
      (contDiff_one_euclideanGradient_apply hg i).continuous_fderiv (by simp)
    exact hfd.clm_apply continuous_const
  exact continuous_pi fun i => continuous_pi fun j => h i j

/-- The norm of the `HilbertMat` carrier is the Frobenius norm. -/
theorem norm_sq_hilbertMat_ofMat' (A : Mat d) :
    ‖HilbertMat.ofMat A‖ ^ 2 = ∑ i, ∑ j, A i j * A i j := by
  rw [← real_inner_self_eq_norm_sq, HilbertMat.inner_def]

theorem continuous_euclideanGradientJacobian {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Continuous (fun x : Vec d => HilbertMat.ofMat (euclideanGradientJacobian g x)) :=
  ((HilbertMat.continuousLinearEquivMat d).symm.continuous).comp
    (continuous_euclideanGradientJacobian' hg)

/-- The `i`-th partial derivative of a smooth potential as a `W^{1,2}` function
on an open triadic cube; its weak gradient is the `i`-th row of the Hessian. -/
def gradientRowW1p (R : TriadicCube d) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    W1pFunction (openCubeSet R) (2 : ℝ≥0∞) :=
  W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet R) (contDiff_one_euclideanGradient_apply hg i)

theorem gradientRowW1p_toFun (R : TriadicCube d) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    (gradientRowW1p R hg i).toFun = fun x => euclideanGradient g x i := rfl

theorem gradientRowW1p_grad (R : TriadicCube d) {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) :
    (gradientRowW1p R hg i).grad = fun x => euclideanGradientJacobian g x i := rfl

/-- **The scalar Poincare inequality on a triadic cube**, in the normalized
`L̲²` carrier: upstream
`cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm`
composed with the identification of the normalized `W^{1,2}` seminorm. -/
theorem cubeLpNorm_cubeFluctuation_le [NeZero d] (R : TriadicCube d)
    (u : W1pFunction (openCubeSet R) (2 : ℝ≥0∞)) :
    cubeLpNorm R (2 : ℝ≥0∞) (cubeFluctuation R u.toFun) ≤
      poincareCubeConst d * cubeScaleFactor R *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x)) := by
  have h := cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm R u
  rwa [openCubeSet_normalizedW1pSeminorm_two_eq_cubeLpNorm_euclideanGrad R u,
    cubeBesovOscillation] at h

/-- The normalized cube average is the volume average over the half-open
realization. -/
theorem cubeAverage_eq_volumeAverage (R : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage R f = volumeAverage (cubeSet R) f := by
  rw [cubeAverage, volumeAverage, volume_cubeSet_toReal]

/-- The real square average of a scalar field is the average of its square. -/
theorem cubeSquareAverage_real (R : TriadicCube d) (f : Vec d → ℝ) :
    cubeSquareAverage R f = volumeAverage (cubeSet R) (fun x => f x ^ 2) := by
  refine congrArg (volumeAverage (cubeSet R)) (funext fun x => ?_)
  rw [Real.norm_eq_abs, sq_abs]

/-- **The Poincare inequality for a smooth gradient field on a triadic cube**,
in the real square-average carriers: the centred gradient field is controlled
by `3^{scale} C(d)` times the Hessian. -/
theorem sqrt_vecSqAvg_sub_average_le (hd : 0 < d) (R : TriadicCube d)
    {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Real.sqrt (vecSqAvg R (fun x => euclideanGradient g x -
        volumeAverageVec (cubeSet R) (euclideanGradient g))) ≤
      poincareCubeConst d * (3 : ℝ) ^ R.scale *
        Real.sqrt (matSqAvg R (euclideanGradientJacobian g)) := by
  have : NeZero d := NeZero.of_pos hd
  classical
  set K : ℝ := poincareCubeConst d * (3 : ℝ) ^ R.scale with hK
  have hKnn : 0 ≤ K := mul_nonneg (poincareCubeConst_nonneg d) (by positivity)
  set G : Vec d → Vec d := euclideanGradient g with hGdef
  set H : Vec d → Mat d := euclideanGradientJacobian g with hHdef
  set c : Vec d := volumeAverageVec (cubeSet R) G with hc
  have hGcont : Continuous G := continuous_euclideanGradient' hg
  have hHcont : Continuous (fun x : Vec d => HilbertMat.ofMat (H x)) :=
    continuous_euclideanGradientJacobian hg
  have hHmat : Continuous H := continuous_euclideanGradientJacobian' hg
  have hrow : ∀ i : Fin d, Continuous (fun x : Vec d => vecNormSq (H x i)) := by
    intro i
    have hcs : Continuous (fun x : Vec d => ∑ j : Fin d, H x i j * H x i j) := by
      refine continuous_finsetSum _ fun j _ => ?_
      have hij : Continuous (fun x : Vec d => H x i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp hHmat)
      exact hij.mul hij
    exact hcs
  have hcoord : ∀ i : Fin d,
      volumeAverage (cubeSet R) (fun x => (G x i - c i) ^ 2) ≤
        K ^ 2 * volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)) := by
    intro i
    have hpoin := cubeLpNorm_cubeFluctuation_le R (gradientRowW1p R hg i)
    have hfl : cubeFluctuation R (gradientRowW1p R hg i).toFun
        = fun x => G x i - c i := by
      funext x
      rw [cubeFluctuation, gradientRowW1p_toFun, cubeAverage_eq_volumeAverage]
      rfl
    have hci : Continuous (fun x : Vec d => G x i - c i) :=
      ((continuous_apply i).comp hGcont).sub continuous_const
    have hLHS : cubeLpNorm R (2 : ℝ≥0∞)
        (cubeFluctuation R (gradientRowW1p R hg i).toFun) =
        Real.sqrt (volumeAverage (cubeSet R) (fun x => (G x i - c i) ^ 2)) := by
      rw [show cubeLpNorm R (2 : ℝ≥0∞)
          (cubeFluctuation R (gradientRowW1p R hg i).toFun)
          = (cubeLpENorm R 2
              (cubeFluctuation R (gradientRowW1p R hg i).toFun)).toReal from rfl,
        hfl, toReal_cubeLpENorm_two_eq_sqrt R hci, cubeSquareAverage_real]
    have hRHS : cubeLpNorm R (2 : ℝ≥0∞)
        (fun x => euclideanNorm ((gradientRowW1p R hg i).grad x)) =
        Real.sqrt (volumeAverage (cubeSet R) (fun x => vecNormSq (H x i))) := by
      have hcont : Continuous (fun x : Vec d => euclideanNorm (H x i)) :=
        Real.continuous_sqrt.comp (hrow i)
      rw [show cubeLpNorm R (2 : ℝ≥0∞)
          (fun x => euclideanNorm ((gradientRowW1p R hg i).grad x))
          = (cubeLpENorm R 2
              (fun x => euclideanNorm ((gradientRowW1p R hg i).grad x))).toReal from rfl,
        gradientRowW1p_grad, toReal_cubeLpENorm_two_eq_sqrt R hcont,
        cubeSquareAverage_real]
      refine congrArg Real.sqrt (congrArg (volumeAverage (cubeSet R)) (funext fun x => ?_))
      rw [euclideanNorm, Real.sq_sqrt (vecNormSq_nonneg _)]
    rw [hLHS, hRHS, show cubeScaleFactor R = (3 : ℝ) ^ R.scale from rfl, ← hK] at hpoin
    have hAnn : 0 ≤ volumeAverage (cubeSet R) (fun x => (G x i - c i) ^ 2) :=
      volumeAverage_cubeSet_nonneg R fun x => by positivity
    have hBnn : 0 ≤ volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)) :=
      volumeAverage_cubeSet_nonneg R fun x => vecNormSq_nonneg _
    have hstep := mul_self_le_mul_self (Real.sqrt_nonneg _) hpoin
    rw [Real.mul_self_sqrt hAnn] at hstep
    have hexp : (K * Real.sqrt (volumeAverage (cubeSet R)
          (fun x => vecNormSq (H x i)))) *
        (K * Real.sqrt (volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)))) =
        K ^ 2 * volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)) := by
      have hs := Real.mul_self_sqrt hBnn
      calc (K * Real.sqrt (volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)))) *
            (K * Real.sqrt (volumeAverage (cubeSet R) (fun x => vecNormSq (H x i))))
          = K ^ 2 * (Real.sqrt (volumeAverage (cubeSet R)
              (fun x => vecNormSq (H x i))) *
              Real.sqrt (volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)))) := by
            ring
        _ = K ^ 2 * volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)) := by
            rw [hs]
    rw [hexp] at hstep
    exact hstep
  -- sum the coordinates
  have hLsum : vecSqAvg R (fun x => G x - c) =
      ∑ i, volumeAverage (cubeSet R) (fun x => (G x i - c i) ^ 2) := by
    have hpt : (fun x : Vec d => ‖hilbertifyVecField (fun y => G y - c) x‖ ^ 2)
        = fun x : Vec d => ∑ i, (G x i - c i) ^ 2 := by
      funext x
      rw [norm_hilbertifyVecField_apply, vecNorm_sq_eq_vecNormSq, vecNormSq, vecDot]
      exact Finset.sum_congr rfl fun i _ => (sq _).symm
    rw [vecSqAvg, cubeSquareAverage, hpt]
    exact volumeAverage_cubeSet_finset_sum R _ fun i =>
      (((continuous_apply i).comp hGcont).sub continuous_const).pow 2
  have hRsum : matSqAvg R H =
      ∑ i, volumeAverage (cubeSet R) (fun x => vecNormSq (H x i)) := by
    have hpt : (fun x : Vec d => ‖HilbertMat.ofMat (H x)‖ ^ 2)
        = fun x : Vec d => ∑ i, vecNormSq (H x i) := by
      funext x
      rw [norm_sq_hilbertMat_ofMat']
      rfl
    rw [matSqAvg, cubeSquareAverage, hpt]
    exact volumeAverage_cubeSet_finset_sum R _ hrow
  have hsum : vecSqAvg R (fun x => G x - c) ≤ K ^ 2 * matSqAvg R H := by
    rw [hLsum, hRsum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hcoord i
  have hMnn : 0 ≤ matSqAvg R H := cubeSquareAverage_nonneg R _
  calc Real.sqrt (vecSqAvg R (fun x => G x - c))
      ≤ Real.sqrt (K ^ 2 * matSqAvg R H) := Real.sqrt_le_sqrt hsum
    _ = K * Real.sqrt (matSqAvg R H) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hKnn]

/-! ## Depth averages -/

/-- **Cauchy-Schwarz for a descendant average.** -/
theorem descendantsAverage_mul_le_sqrt_mul_sqrt (Q : TriadicCube d) (j : ℕ)
    (a b : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => a R * b R) ≤
      Real.sqrt (descendantsAverage Q j (fun R => a R ^ 2)) *
        Real.sqrt (descendantsAverage Q j (fun R => b R ^ 2)) := by
  classical
  set c : ℝ := ((descendantsAtDepth Q j).card : ℝ)⁻¹ with hc
  have hcnn : (0 : ℝ) ≤ c := by rw [hc]; positivity
  have h := Real.sum_mul_le_sqrt_mul_sqrt (descendantsAtDepth Q j) a b
  have hmul := mul_le_mul_of_nonneg_left h hcnn
  refine le_trans hmul (le_of_eq ?_)
  calc c * (Real.sqrt (∑ R ∈ descendantsAtDepth Q j, a R ^ 2) *
        Real.sqrt (∑ R ∈ descendantsAtDepth Q j, b R ^ 2))
      = (Real.sqrt c * Real.sqrt c) *
          (Real.sqrt (∑ R ∈ descendantsAtDepth Q j, a R ^ 2) *
            Real.sqrt (∑ R ∈ descendantsAtDepth Q j, b R ^ 2)) := by
        rw [Real.mul_self_sqrt hcnn]
    _ = (Real.sqrt c * Real.sqrt (∑ R ∈ descendantsAtDepth Q j, a R ^ 2)) *
          (Real.sqrt c * Real.sqrt (∑ R ∈ descendantsAtDepth Q j, b R ^ 2)) := by
        ring
    _ = Real.sqrt (descendantsAverage Q j (fun R => a R ^ 2)) *
          Real.sqrt (descendantsAverage Q j (fun R => b R ^ 2)) := by
        rw [← Real.sqrt_mul hcnn, ← Real.sqrt_mul hcnn]
        rfl

/-- The partition identity, in the descendant-average carrier. -/
theorem volumeAverage_eq_descendantsAverage (Q : TriadicCube d) (j : ℕ)
    {f : Vec d → ℝ} (hf : Continuous f) :
    volumeAverage (cubeSet Q) f =
      descendantsAverage Q j (fun R => volumeAverage (cubeSet R) f) :=
  volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants Q j
    (fun R _ => integrableOn_cubeSet_of_continuous R hf)

theorem cubeSquareAverage_eq_descendantsAverage {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (j : ℕ) {f : Vec d → E} (hf : Continuous f) :
    cubeSquareAverage Q f =
      descendantsAverage Q j (fun R => cubeSquareAverage R f) :=
  volumeAverage_eq_descendantsAverage Q j (hf.norm.pow 2)

theorem vecSqAvg_eq_descendantsAverage (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : Continuous F) :
    vecSqAvg Q F = descendantsAverage Q j (fun R => vecSqAvg R F) :=
  cubeSquareAverage_eq_descendantsAverage Q j (continuous_hilbertifyVecField hF)

theorem volumeAverageVec_eq_descendantsAverage (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : Continuous F) (i : Fin d) :
    volumeAverageVec (cubeSet Q) F i =
      descendantsAverage Q j (fun R => volumeAverageVec (cubeSet R) F i) :=
  volumeAverage_eq_descendantsAverage Q j ((continuous_apply i).comp hF)

/-! ## The printed depth moment -/

/-- `avsum_{y ∈ 3^{l-j}ℤ^d ∩ Q} |(F)_{y+cu_{l-j}}|²`, the printed depth moment
of `e.apply.multiscale.Poincare` at `p = 2`, indexed by the depth `j`. -/
def vecDepthSqMoment (Q : TriadicCube d) (j : ℕ) (F : Vec d → Vec d) : ℝ :=
  descendantsAverage Q j (fun R => vecNormSq (volumeAverageVec (cubeSet R) F))

/-- The rooted depth moment, the summand of the printed `ℓ¹` sum. -/
def vecDepthMoment (Q : TriadicCube d) (j : ℕ) (F : Vec d → Vec d) : ℝ :=
  Real.sqrt (vecDepthSqMoment Q j F)

theorem vecDepthSqMoment_nonneg (Q : TriadicCube d) (j : ℕ) (F : Vec d → Vec d) :
    0 ≤ vecDepthSqMoment Q j F :=
  descendantsAverage_nonneg Q j _ fun _R _ => vecNormSq_nonneg _

theorem vecDepthMoment_nonneg (Q : TriadicCube d) (j : ℕ) (F : Vec d → Vec d) :
    0 ≤ vecDepthMoment Q j F := Real.sqrt_nonneg _

theorem vecDepthSqMoment_zero (Q : TriadicCube d) (F : Vec d → Vec d) :
    vecDepthSqMoment Q 0 F = vecNormSq (volumeAverageVec (cubeSet Q) F) := by
  rw [vecDepthSqMoment, descendantsAverage, descendantsAtDepth_zero]
  simp

/-! ## Descendant-average algebra and cube-average identities -/

theorem descendantsAverage_sub (Q : TriadicCube d) (j : ℕ)
    (A B : TriadicCube d → ℝ) :
    descendantsAverage Q j A - descendantsAverage Q j B =
      descendantsAverage Q j (fun R => A R - B R) := by
  classical
  simp only [descendantsAverage, Finset.sum_sub_distrib]
  ring

theorem abs_descendantsAverage_le (Q : TriadicCube d) (j : ℕ)
    (A : TriadicCube d → ℝ) :
    |descendantsAverage Q j A| ≤ descendantsAverage Q j (fun R => |A R|) := by
  classical
  have hc : (0 : ℝ) ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ := by positivity
  simp only [descendantsAverage, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hc

/-- From `√A ≤ K √B` to the squared inequality. -/
theorem le_sq_mul_of_sqrt_le {A B K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : Real.sqrt A ≤ K * Real.sqrt B) : A ≤ K ^ 2 * B := by
  have hstep := mul_self_le_mul_self (Real.sqrt_nonneg _) h
  rw [Real.mul_self_sqrt hA] at hstep
  have hexp : (K * Real.sqrt B) * (K * Real.sqrt B) = K ^ 2 * B := by
    calc (K * Real.sqrt B) * (K * Real.sqrt B)
        = K ^ 2 * (Real.sqrt B * Real.sqrt B) := by ring
      _ = K ^ 2 * B := by rw [Real.mul_self_sqrt hB]
  rw [hexp] at hstep
  exact hstep

theorem vecDot_sub_right (a b c : Vec d) :
    vecDot a (b - c) = vecDot a b - vecDot a c := by
  simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem vecDot_comm' (a b : Vec d) : vecDot a b = vecDot b a :=
  Finset.sum_congr rfl fun i _ => mul_comm (a i) (b i)

theorem continuous_vecDot {F G : Vec d → Vec d} (hF : Continuous F)
    (hG : Continuous G) : Continuous (fun x => vecDot (F x) (G x)) := by
  have h : Continuous (fun x : Vec d => ∑ i : Fin d, F x i * G x i) :=
    continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp hF).mul ((continuous_apply i).comp hG)
  exact h

theorem volumeAverage_cubeSet_sub (R : TriadicCube d) {f h : Vec d → ℝ}
    (hf : Continuous f) (hh : Continuous h) :
    volumeAverage (cubeSet R) (fun x => f x - h x) =
      volumeAverage (cubeSet R) f - volumeAverage (cubeSet R) h := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_sub (integrableOn_cubeSet_of_continuous R hf)
    (integrableOn_cubeSet_of_continuous R hh)]
  ring

theorem volumeAverage_vecDot_const_right (R : TriadicCube d) {F : Vec d → Vec d}
    (hF : Continuous F) (c : Vec d) :
    volumeAverage (cubeSet R) (fun x => vecDot (F x) c) =
      vecDot (volumeAverageVec (cubeSet R) F) c := by
  have h := volumeAverage_vecDot_const_left (cubeSet R) c (F := F)
    (fun i => integrableOn_cubeSet_of_continuous R ((continuous_apply i).comp hF))
  rw [vecDot_comm' (volumeAverageVec (cubeSet R) F) c, ← h]
  exact congrArg (volumeAverage (cubeSet R)) (funext fun x => vecDot_comm' (F x) c)

/-- The centring identity on one cube: the pairing minus its constant-average
truncation is the pairing against the centred field. -/
theorem volumeAverage_vecDot_sub_average (R : TriadicCube d) {F G : Vec d → Vec d}
    (hF : Continuous F) (hG : Continuous G) :
    volumeAverage (cubeSet R) (fun x => vecDot (F x) (G x)) -
        vecDot (volumeAverageVec (cubeSet R) F)
          (volumeAverageVec (cubeSet R) G) =
      volumeAverage (cubeSet R)
        (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G)) := by
  have hsplit : (fun x => vecDot (F x) (G x - volumeAverageVec (cubeSet R) G))
      = fun x => vecDot (F x) (G x) -
          vecDot (F x) (volumeAverageVec (cubeSet R) G) :=
    funext fun x => vecDot_sub_right _ _ _
  rw [hsplit, volumeAverage_cubeSet_sub R (continuous_vecDot hF hG)
    (continuous_vecDot hF continuous_const),
    volumeAverage_vecDot_const_right R hF]

theorem volumeAverage_cubeSet_const (R : TriadicCube d) (a : ℝ) :
    volumeAverage (cubeSet R) (fun _ : Vec d => a) = a := by
  have hvol : (volume (cubeSet R)).toReal ≠ 0 := ne_of_gt (volume_cubeSet_toReal_pos R)
  rw [volumeAverage, setIntegral_const, measureReal_def, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hvol, one_mul]

theorem volumeAverageVec_sub_const (R : TriadicCube d) {G : Vec d → Vec d}
    (hG : Continuous G) (c : Vec d) :
    volumeAverageVec (cubeSet R) (fun x => G x - c) =
      volumeAverageVec (cubeSet R) G - c := by
  funext i
  show volumeAverage (cubeSet R) (fun x => G x i - c i) =
    volumeAverage (cubeSet R) (fun x => G x i) - c i
  have hi : Continuous (fun x : Vec d => G x i) := (continuous_apply i).comp hG
  rw [volumeAverage_cubeSet_sub R hi (continuous_const (y := c i)),
    volumeAverage_cubeSet_const]

theorem descendantsAverage_mul_right (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (A : TriadicCube d → ℝ) :
    descendantsAverage Q j (fun R => A R * c) =
      descendantsAverage Q j A * c := by
  have h : (fun R : TriadicCube d => A R * c) = fun R => c * A R :=
    funext fun R => mul_comm _ _
  rw [h, descendantsAverage_mul_left, mul_comm]

/-- **The tower property of the cube averages**, in the pairing form. -/
theorem vecDot_volumeAverageVec_eq_descendantsAverage (R : TriadicCube d) (j : ℕ)
    {F : Vec d → Vec d} (hF : Continuous F) (c : Vec d) :
    vecDot (volumeAverageVec (cubeSet R) F) c =
      descendantsAverage R j
        (fun R' => vecDot (volumeAverageVec (cubeSet R') F) c) := by
  classical
  have hsum : descendantsAverage R j
      (fun R' => vecDot (volumeAverageVec (cubeSet R') F) c) =
      ∑ i : Fin d, descendantsAverage R j
        (fun R' => volumeAverageVec (cubeSet R') F i * c i) :=
    descendantsAverage_sum R j Finset.univ
      (fun R' i => volumeAverageVec (cubeSet R') F i * c i)
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [descendantsAverage_mul_right,
    ← volumeAverageVec_eq_descendantsAverage R j hF i]

/-- Jensen on one cube, in the squared form. -/
theorem vecNormSq_volumeAverageVec_le (R : TriadicCube d) {F : Vec d → Vec d}
    (hF : Continuous F) :
    vecNormSq (volumeAverageVec (cubeSet R) F) ≤ vecSqAvg R F := by
  have h := vecNorm_volumeAverageVec_le_sqrt R hF
  have hsq := mul_self_le_mul_self (vecNorm_nonneg _) h
  rw [Real.mul_self_sqrt (vecSqAvg_nonneg R F)] at hsq
  rw [← vecNorm_sq_eq_vecNormSq, pow_two]
  exact hsq

theorem descendantsAverage_zero (Q : TriadicCube d) (A : TriadicCube d → ℝ) :
    descendantsAverage Q 0 A = A Q := by
  rw [descendantsAverage, descendantsAtDepth_zero]
  simp

theorem vecDepthMoment_zero (Q : TriadicCube d) (F : Vec d → Vec d) :
    vecDepthMoment Q 0 F = vecNorm (volumeAverageVec (cubeSet Q) F) := by
  rw [vecDepthMoment, vecDepthSqMoment_zero, ← vecNorm_sq_eq_vecNormSq,
    Real.sqrt_sq (vecNorm_nonneg _)]

/-- The first half of the order-one test constraint, in real form. -/
theorem sqrt_vecSqAvg_euclideanGradient_le_one {Q : TriadicCube d} {g : Vec d → ℝ}
    (hg : IsVecHatTestFieldOrderOne Q g) :
    Real.sqrt (vecSqAvg Q (euclideanGradient g)) ≤ 1 := by
  have hle : vecCubeLpENorm Q 2 (euclideanGradient g) ≤ 1 :=
    le_trans (vecCubeLpENorm_euclideanGradient_le_vecHatTestH1ENorm Q g) hg.h1_le_one
  have hR := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [toReal_vecCubeLpENorm_eq_sqrt Q (continuous_euclideanGradient' hg.contDiff)]
    at hR
  simpa using hR

/-- The second half of the order-one test constraint, in real form. -/
theorem threePow_mul_sqrt_matSqAvg_le_one {Q : TriadicCube d} {g : Vec d → ℝ}
    (hg : IsVecHatTestFieldOrderOne Q g) :
    (3 : ℝ) ^ Q.scale *
      Real.sqrt (matSqAvg Q (euclideanGradientJacobian g)) ≤ 1 := by
  have hle : ENNReal.ofReal ((3 : ℝ) ^ ((Q.scale : ℝ))) *
      cubeLpENorm Q 2 (fun x => HilbertMat.ofMat (euclideanGradientJacobian g x))
      ≤ 1 := by
    refine le_trans ?_ hg.h1_le_one
    rw [vecHatTestH1ENorm]
    exact le_add_self
  have hR := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    toReal_cubeLpENorm_two_eq_sqrt Q (continuous_euclideanGradientJacobian hg.contDiff),
    Real.rpow_intCast] at hR
  unfold matSqAvg
  simpa using hR

/-- The dimension-only constant of the truncated multiscale bound. -/
def multiscaleOrderOneConst (d : ℕ) : ℝ := 1 + 3 * poincareCubeConst d

theorem one_le_multiscaleOrderOneConst (d : ℕ) : 1 ≤ multiscaleOrderOneConst d := by
  have h := poincareCubeConst_nonneg d
  rw [multiscaleOrderOneConst]
  linarith only [h]

theorem poincareCubeConst_le_multiscaleOrderOneConst (d : ℕ) :
    poincareCubeConst d ≤ multiscaleOrderOneConst d := by
  have h := poincareCubeConst_nonneg d
  rw [multiscaleOrderOneConst]
  linarith only [h]

/-! ## Centring -/

/-- **Subtracting a constant costs its length.** -/
theorem vecHatNegENormOrderOne_sub_const_le (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : Continuous F) (v : Vec d) :
    vecHatNegENormOrderOne Q (fun x => F x - v) ≤
      vecHatNegENormOrderOne Q F + ENNReal.ofReal (vecNorm v) := by
  refine vecHatNegENormOrderOne_le fun g hg => ?_
  have hGcont : Continuous (euclideanGradient g) :=
    continuous_euclideanGradient' hg.contDiff
  have hleft : ∀ a b w : Vec d, vecDot (a - b) w = vecDot a w - vecDot b w := by
    intro a b w
    rw [vecDot_comm' (a - b) w, vecDot_sub_right, vecDot_comm' w a, vecDot_comm' w b]
  have hpt : vecGradientPairingDensity (fun x => F x - v) g =
      fun x => vecDot (F x) (euclideanGradient g x) -
        vecDot v (euclideanGradient g x) := by
    funext x
    rw [SuperdiffusionCLT.Section2.Norms.vecGradientPairingDensity_eq_vecDot]
    exact hleft (F x) v (euclideanGradient g x)
  have hdensF : vecGradientPairingDensity F g =
      fun x => vecDot (F x) (euclideanGradient g x) :=
    funext fun x =>
      SuperdiffusionCLT.Section2.Norms.vecGradientPairingDensity_eq_vecDot F g x
  have hsplit : volumeAverage (cubeSet Q)
      (vecGradientPairingDensity (fun x => F x - v) g) =
      volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) -
        vecDot v (volumeAverageVec (cubeSet Q) (euclideanGradient g)) := by
    rw [hpt, volumeAverage_cubeSet_sub Q (continuous_vecDot hF hGcont)
      (continuous_vecDot continuous_const hGcont), hdensF,
      volumeAverage_vecDot_const_left (cubeSet Q) v (F := euclideanGradient g)
        (fun i => integrableOn_cubeSet_of_continuous Q ((continuous_apply i).comp hGcont))]
  have hbound : |vecDot v (volumeAverageVec (cubeSet Q) (euclideanGradient g))| ≤
      vecNorm v := by
    refine le_trans (abs_vecDot_le_vecNorm_mul_vecNorm _ _) ?_
    have h1 : vecNorm (volumeAverageVec (cubeSet Q) (euclideanGradient g)) ≤ 1 :=
      le_trans (vecNorm_volumeAverageVec_le_sqrt Q hGcont)
        (sqrt_vecSqAvg_euclideanGradient_le_one hg)
    calc vecNorm v * vecNorm (volumeAverageVec (cubeSet Q) (euclideanGradient g))
        ≤ vecNorm v * 1 := mul_le_mul_of_nonneg_left h1 (vecNorm_nonneg v)
      _ = vecNorm v := mul_one _
  rw [hsplit]
  calc ENNReal.ofReal (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g) -
        vecDot v (volumeAverageVec (cubeSet Q) (euclideanGradient g)))
      ≤ ENNReal.ofReal (volumeAverage (cubeSet Q)
          (vecGradientPairingDensity F g) + vecNorm v) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hneg := neg_abs_le
          (vecDot v (volumeAverageVec (cubeSet Q) (euclideanGradient g)))
        linarith only [hbound, hneg]
    _ ≤ ENNReal.ofReal (volumeAverage (cubeSet Q) (vecGradientPairingDensity F g)) +
          ENNReal.ofReal (vecNorm v) := ENNReal.ofReal_add_le
    _ ≤ vecHatNegENormOrderOne Q F + ENNReal.ofReal (vecNorm v) :=
        add_le_add (le_vecHatNegENormOrderOne F hg) le_rfl

/-! ## The Poincare input, aggregated over one depth -/

/-! ## The Poincare input, aggregated over one depth -/

/-- The scale factor of a depth-`j` descendant. -/
theorem threePow_scale_of_mem_descendantsAtDepth {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    (3 : ℝ) ^ R.scale = (3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹ := by
  rw [scale_eq_sub_of_mem_descendantsAtDepth hR,
    zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, div_eq_mul_inv]

/-- **The Poincare inequality aggregated over the depth-`j` descendants.** The
depth average of the centred `L̲²` energies of an admissible test gradient is at
most `(C(d) 3^{l-j})²` times the `L̲²` energy of its Hessian on the whole
cube. -/
theorem descendantsAverage_vecSqAvg_sub_average_le (hd : 0 < d)
    (Q : TriadicCube d) (j : ℕ) {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    descendantsAverage Q j (fun R => vecSqAvg R (fun x =>
        euclideanGradient g x -
          volumeAverageVec (cubeSet R) (euclideanGradient g))) ≤
      (poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹)) ^ 2 *
        matSqAvg Q (euclideanGradientJacobian g) := by
  set K : ℝ := poincareCubeConst d * ((3 : ℝ) ^ Q.scale * ((3 : ℝ) ^ j)⁻¹) with hKdef
  have hKnn : 0 ≤ K :=
    mul_nonneg (poincareCubeConst_nonneg d) (by positivity)
  have hstep : ∀ R ∈ descendantsAtDepth Q j,
      vecSqAvg R (fun x => euclideanGradient g x -
          volumeAverageVec (cubeSet R) (euclideanGradient g)) ≤
        K ^ 2 * matSqAvg R (euclideanGradientJacobian g) := by
    intro R hR
    have hpoin := sqrt_vecSqAvg_sub_average_le hd R hg
    rw [threePow_scale_of_mem_descendantsAtDepth hR] at hpoin
    refine le_sq_mul_of_sqrt_le (vecSqAvg_nonneg R _)
      (cubeSquareAverage_nonneg R _) ?_
    rw [hKdef]
    exact hpoin
  calc descendantsAverage Q j (fun R => vecSqAvg R (fun x =>
        euclideanGradient g x - volumeAverageVec (cubeSet R) (euclideanGradient g)))
      ≤ descendantsAverage Q j
          (fun R => K ^ 2 * matSqAvg R (euclideanGradientJacobian g)) :=
        descendantsAverage_le_descendantsAverage Q j hstep
    _ = K ^ 2 * descendantsAverage Q j
          (fun R => matSqAvg R (euclideanGradientJacobian g)) :=
        descendantsAverage_mul_left Q j _ _
    _ = K ^ 2 * matSqAvg Q (euclideanGradientJacobian g) := by
        refine congrArg (fun t => K ^ 2 * t) ?_
        exact (cubeSquareAverage_eq_descendantsAverage Q j
          (continuous_euclideanGradientJacobian hg)).symm

end

end SuperdiffusionCLT.Section2.Estimates.Stream
