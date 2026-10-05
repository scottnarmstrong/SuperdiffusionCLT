/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxDirichlet
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxBridge
public import SuperdiffusionCLT.Section2.Norms.CubeLp
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Casts
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue

/-!
# Harmonic approximation on a cube

This is Lemma `l.sharp.scale.inputs`, the bullet on harmonic approximation
(display `e.Dir.new.harmonic.approx`). The theorem `harmonic_approximation_deterministic` is
the deterministic form: if the homogenization error `𝓔_{1/9,2}(cu_n; a, σ Id)` of a field `a`
with symmetric part `ν Id` is at most `δ`, then every `a`-harmonic function on `cu_n` is
`L²`-close, on `cu_{n-1}`, to a harmonic function, at the rate
`3^{-n} ‖u - w‖ ≤ C δ σ^{-1/2} ν^{1/2} ‖∇u‖`, the norms being the volume-normalized `L²` norms.

The proof composes the deterministic coarse-graining theory of `CoarseGraining`
(`Book.Ch03.homogenizationBlackBoxesTheory`, its two-exponent general coarse-graining estimate with
zero forcing) with the zero-trace Riesz representation on the cube and the zero-boundary estimate of
`Book.Ch03`. The raw field is transported to a public coefficient family in
`HarmonicApproxBridge`.

## Main results

* `negBesov_bound`: the negative Besov size of `σ ∇w` for the zero-trace remainder `w`.
* `l2_bound`: the normalized `L²` size of `w` on the cube.
* `harmonic_approximation_cube`: the statement on a pair of nested triadic cubes.
* `harmonic_approximation_deterministic`: the statement on `cu_{n-1} ⊆ cu_n`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6.HarmonicApprox

open Homogenization

noncomputable section

variable {d : ℕ}

/-- The constant coefficient `sigma • Id` as a public constant coefficient matrix. -/
def constMat (d : ℕ) {sigma : ℝ} (hs : 0 < sigma) : Book.Ch03.ConstantCoeffMatrix d where
  matrix := sigma • (1 : Mat d)
  isSymm := scalarMatrix_isSymm sigma
  lam := sigma
  Lam := sigma
  lam_pos := hs
  lam_le_Lam := le_rfl
  elliptic := isEllipticMatrix_scalarMatrix hs

theorem vecDot_sub_left' (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]

/-- The comparison datum between the `a`-harmonic `u` and its constant-coefficient replacement
`u - w`, where `w` is the zero-trace remainder. -/
def comparisonDatum [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {sigma : ℝ} (hs : 0 < sigma) (u : AHarmonicFunction a (openCubeSet Q))
    (w : H10Function (openCubeSet Q))
    (hw : ∀ ψ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
        ∫ x in openCubeSet Q, vecDot (u.toH1.grad x) (ψ.toH1Function.grad x)) :
    Book.Ch03.CoarseGrainingComparisonDatum Q (paddedFamily Q hEll h0 hle) (constMat d hs)
      (0 : Vec d → Vec d) where
  u := u.toH1
  v := u.toH1 - w.toH1Function
  uWeakSolution := by
    intro φ
    have h1 := u.isHarmonic.2 φ
    simp only [Pi.zero_apply, vecDot_zero_left, MeasureTheory.integral_zero]
    rw [← h1]
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) fun x hx => ?_
    simp only [paddedFamily_coeffOn_toCoeffField,
      padField_apply_of_mem (openCubeSet_subset_cubeSet Q hx)]
  vWeakSolution := by
    intro φ
    simp only [Pi.zero_apply, vecDot_zero_left, MeasureTheory.integral_zero]
    have hint1 : MeasureTheory.IntegrableOn
        (fun x => vecDot (u.toH1.grad x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 u.toH1.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
    have hint2 : MeasureTheory.IntegrableOn
        (fun x => vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2
        φ.toH1Function.grad_memVectorL2
    show ∫ x in openCubeSet Q, vecDot (matVecMul (sigma • (1 : Mat d))
      ((u.toH1 - w.toH1Function).grad x)) (φ.toH1Function.grad x) = 0
    simp only [H1Function.sub_grad, matVecMul_scalarMatrix, vecDot_smul_left, vecDot_sub_left']
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hint1 hint2, hw φ]
    ring
  zeroTraceDifference := by
    refine ⟨w, Filter.Eventually.of_forall fun x => ?_⟩
    simp only [H1Function.sub_toFun]
    ring

theorem partialSeminormTwo_zero (Q : TriadicCube d) (r : ℝ) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo Q r N (0 : Vec d → Vec d) = 0 := by
  simp [cubeBesovPositiveVectorPartialSeminormTwo, cubeBesovPositiveVectorDepthSeminorm,
    cubeBesovPositiveVectorDepthAverage, cubeLpNorm]

theorem forceBesovRegularity_zero [NeZero d] (Q : TriadicCube d) (r : ℝ) :
    Book.Ch03.ForceBesovRegularity Q r (0 : Vec d → Vec d) := by
  refine ⟨MeasureTheory.MemLp.zero, ⟨0, ?_⟩⟩
  rintro _ ⟨N, rfl⟩
  exact (partialSeminormTwo_zero Q r N).le

theorem rhs_zero_force [NeZero d] (C : ℝ) (Q : TriadicCube d) (F : Book.Ch03.CoeffFamily d)
    (a0 : Book.Ch03.ConstantCoeffMatrix d) (s r r₂ : ℝ)
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    Book.Ch03.generalCoarseGrainingL2TwoExponentRHS C Q F a0 s r r₂ 0 0 u =
      s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
        (C * (r⁻¹ * Book.Ch03.constantCoeffMatrixNormHalf a0 *
          Book.Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r 0 *
          Book.Ch03.h1EnergyNormOnCube Q F u)) := by
  unfold Book.Ch03.generalCoarseGrainingL2TwoExponentRHS
    Book.Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS
  simp [Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo]

theorem sqrt_vecNormSq_le_sum_abs (g : Vec d) : Real.sqrt (vecNormSq g) ≤ ∑ i, |g i| := by
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |g i|)
    (fun i _ => abs_nonneg _)
  simpa [vecNormSq, vecDot, sq_abs, sq] using h

theorem memLp_sqrt_vecNormSq_grad {Q : TriadicCube d} (u : H1Function (openCubeSet Q)) :
    MeasureTheory.MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure Q) := by
  have hm : ∀ i, MeasureTheory.AEStronglyMeasurable (fun x => u.grad x i)
      (normalizedCubeMeasure Q) := fun i =>
    (u.grad_memL2_normalizedCubeMeasure i).aestronglyMeasurable
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun x => vecNormSq (u.grad x))
      (normalizedCubeMeasure Q) := by
    unfold vecNormSq vecDot
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hm i).mul (hm i)
  have hsum : MeasureTheory.MemLp (fun x => ∑ i, |u.grad x i|) 2 (normalizedCubeMeasure Q) := by
    have := MeasureTheory.memLp_finsetSum' (s := Finset.univ) (p := 2)
      (μ := normalizedCubeMeasure Q)
      (f := fun i x => |u.grad x i|) fun i _ => by
        simpa [Real.norm_eq_abs] using (u.grad_memL2_normalizedCubeMeasure i).norm
    rw [show (fun x => ∑ i, |u.grad x i|) = ∑ i, fun x => |u.grad x i| from by
      funext x
      simp [Finset.sum_apply]]
    exact this
  refine hsum.mono' (Real.continuous_sqrt.comp_aestronglyMeasurable hmeas)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_vecNormSq_le_sum_abs _

/-- The coefficient energy of `u` for a field with symmetric part `nu • Id`. -/
theorem h1EnergyNormOnCube_paddedFamily [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam)
    (hle : lam ≤ Lam) {nu : ℝ} (hnu : 0 < nu)
    (hsym : ∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d))
    (u : H1Function (openCubeSet Q)) :
    Book.Ch03.h1EnergyNormOnCube Q (paddedFamily Q hEll h0 hle) u =
      Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.grad x))) := by
  have hsq : (cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.grad x)))) ^ 2 =
      Book.Ch03.normalizedL2SqOnSet (openCubeSet Q)
        (fun x => Real.sqrt (vecNormSq (u.grad x))) :=
    (Book.Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _
      (memLp_sqrt_vecNormSq_grad u)).symm
  unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
  have hpt : ∀ x ∈ openCubeSet Q,
      vecDot (u.grad x) (matVecMul (symmPart (((paddedFamily Q hEll h0 hle).coeffOn Q).toCoeffField x))
        (u.grad x)) = nu * (Real.sqrt (vecNormSq (u.grad x))) ^ 2 := by
    intro x hx
    have hxc := openCubeSet_subset_cubeSet Q hx
    rw [paddedFamily_coeffOn_toCoeffField, padField_apply_of_mem hxc, hsym x hxc,
      Real.sq_sqrt (vecNormSq_nonneg _)]
    show vecDot (u.grad x) (matVecMul (scalarMatrix nu) (u.grad x)) = nu * vecNormSq (u.grad x)
    rw [matVecMul_scalarMatrix, vecDot_smul_right]
    rfl
  have hset : Book.Ch03.normalizedSetAverage (openCubeSet Q) (fun x =>
      vecDot (u.grad x) (matVecMul (symmPart (((paddedFamily Q hEll h0 hle).coeffOn Q).toCoeffField x))
        (u.grad x))) =
      nu * Book.Ch03.normalizedL2SqOnSet (openCubeSet Q)
        (fun x => Real.sqrt (vecNormSq (u.grad x))) := by
    unfold Book.Ch03.normalizedSetAverage Book.Ch03.normalizedL2SqOnSet
      Book.Ch03.normalizedSetAverage volumeAverage
    rw [MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q) hpt,
      MeasureTheory.integral_const_mul]
    ring
  rw [hset, ← hsq, Real.sqrt_mul hnu.le, Real.sqrt_sq (cubeLpNorm_nonneg _ _ _)]

theorem errorAtDepth_zero [NeZero d] (Q : TriadicCube d) (F : Book.Ch03.CoeffFamily d)
    (a0 : Book.Ch03.ConstantCoeffMatrix d) (r : ℝ) :
    Book.Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r 0 =
      Book.Ch02.HomogenizationErrorOnCube Q r Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 1) F a0.matrix := by
  unfold Book.Ch03.coarseGrainingHomogenizationErrorAtDepth Book.Ch02.finsetSupReal
  simp [descendantsAtDepth_zero]

theorem matrixNorm_scalar_le [NeZero d] {sigma : ℝ} (hs : 0 ≤ sigma) :
    Book.Ch02.matrixNorm (sigma • (1 : Mat d)) ≤ sigma := by
  unfold Book.Ch02.matrixNorm
  rw [map_smul, map_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  calc sigma * ‖(1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖
      ≤ sigma * 1 := mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) hs
    _ = sigma := mul_one _

theorem cubeBesovNegativeVectorSeminormTwo_nonneg' (Q : TriadicCube d) (s : ℝ)
    (f : Vec d → Vec d) : 0 ≤ cubeBesovNegativeVectorSeminormTwo Q s f := by
  unfold cubeBesovNegativeVectorSeminormTwo
  refine Real.sSup_nonneg ?_
  rintro _ ⟨N, rfl⟩
  exact Real.sqrt_nonneg _

theorem negBesov_le_comparison_lhs [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {sigma : ℝ} (hs : 0 < sigma) (u : AHarmonicFunction a (openCubeSet Q))
    (w : H10Function (openCubeSet Q))
    (hw : ∀ ψ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
        ∫ x in openCubeSet Q, vecDot (u.toH1.grad x) (ψ.toH1Function.grad x)) (s : ℝ) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => sigma • w.toH1Function.grad x) ≤
      Book.Ch03.homogenizationComparisonNegativeBesovLHS Q (paddedFamily Q hEll h0 hle)
        (constMat d hs) s (comparisonDatum Q hEll h0 hle hs u w hw).u
        (comparisonDatum Q hEll h0 hle hs u w hw).v := by
  unfold Book.Ch03.homogenizationComparisonNegativeBesovLHS
  have hfield : Book.Ch03.homogenizationComparisonConstantGradientField (constMat d hs)
      (comparisonDatum Q hEll h0 hle hs u w hw).u (comparisonDatum Q hEll h0 hle hs u w hw).v =
      fun x => sigma • w.toH1Function.grad x := by
    funext x
    show matVecMul (sigma • (1 : Mat d)) (u.toH1.grad x - (u.toH1 - w.toH1Function).grad x) = _
    rw [H1Function.sub_grad, matVecMul_scalarMatrix]
    simp
  rw [hfield]
  exact le_add_of_nonneg_right (cubeBesovNegativeVectorSeminormTwo_nonneg' _ _ _)

/-- The negative Besov size of `sigma ∇w`, in terms of the homogenization error. -/
theorem negBesov_bound (d : ℕ) [NeZero d] :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
      (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
      {sigma nu : ℝ}, 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      ∀ (u : AHarmonicFunction a (openCubeSet Q)) (w : H10Function (openCubeSet Q)),
      (∀ ψ : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
          ∫ x in openCubeSet Q, vecDot (u.toH1.grad x) (ψ.toH1Function.grad x)) →
      cubeBesovNegativeVectorSeminormTwo Q (2 * (1 / 4)) (fun x => sigma • w.toH1Function.grad x) ≤
        C₂ * Real.sqrt sigma * Real.sqrt nu *
          Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
            (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
          cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C₁, hC₁, hth⟩ :=
    (Book.Ch03.homogenizationBlackBoxesTheory d).generalCoarseGrainingL2TwoExponent.exists_constant
  refine ⟨(2 * (1 / 4 : ℝ))⁻¹ * ((2 / 9 : ℝ)⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - 2 / 9)⁻¹ *
    (C₁ * (2 / 9 : ℝ)⁻¹), by positivity, ?_⟩
  intro Q lam Lam a hEll h0 hle sigma nu hs hnu hsym u w hw
  have h1 := hth (Q := Q) (a := paddedFamily Q hEll h0 hle) (a0 := constMat d hs)
    (s := 2 * (1 / 4)) (r := 2 / 9) (r₂ := 2 / 9) (j := 0) (g := 0) ⟨sigma, hs, rfl⟩
    (comparisonDatum Q hEll h0 hle hs u w hw) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl (forceBesovRegularity_zero Q _)
  have hen : Book.Ch03.h1EnergyNormOnCube Q (paddedFamily Q hEll h0 hle)
      (comparisonDatum Q hEll h0 hle hs u w hw).u =
      Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    h1EnergyNormOnCube_paddedFamily Q hEll h0 hle hnu hsym u.toH1
  rw [rhs_zero_force, errorAtDepth_zero, hen] at h1
  have h2 := (negBesov_le_comparison_lhs Q hEll h0 hle hs u w hw (2 * (1 / 4))).trans h1
  refine h2.trans ?_
  have hq : Book.Ch02.HomogenizationErrorOnCube Q (2 / 9) Book.Ch02.MultiscaleExponent.infinity
      (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle) (constMat d hs).matrix ≤
      Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) := by
    have := ch02_error_infinity_one_le_infinity_two_half Q (paddedFamily Q hEll h0 hle)
      (sigma • (1 : Mat d)) (s := 2 / 9) (by norm_num)
    have e : (2 / 9 : ℝ) / 2 = 1 / 9 := by norm_num
    rw [e] at this
    exact this
  have hnorm : Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) ≤ Real.sqrt sigma := by
    unfold Book.Ch03.constantCoeffMatrixNormHalf
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (norm_nonneg _) (matrixNorm_scalar_le hs.le) (by norm_num)
  have hM0 : 0 ≤ Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hE1 : 0 ≤ Book.Ch02.HomogenizationErrorOnCube Q (2 / 9)
      Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 1)
      (paddedFamily Q hEll h0 hle) (constMat d hs).matrix :=
    Book.Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q _ _ (by norm_num)
  have hG : 0 ≤ cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    cubeLpNorm_nonneg _ _ _
  have hsqnu : 0 ≤ Real.sqrt nu := Real.sqrt_nonneg _
  have key : (2 / 9 : ℝ)⁻¹ * Book.Ch03.constantCoeffMatrixNormHalf (constMat d hs) *
      Book.Ch02.HomogenizationErrorOnCube Q (2 / 9) Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle)
        (constMat d hs).matrix * (Real.sqrt nu *
          cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) ≤
      (2 / 9 : ℝ)⁻¹ * Real.sqrt sigma *
        Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
        (Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
    have hq' : Book.Ch02.HomogenizationErrorOnCube Q (2 / 9) Book.Ch02.MultiscaleExponent.infinity
        (Book.Ch02.MultiscaleExponent.finite 1) (paddedFamily Q hEll h0 hle)
        (constMat d hs).matrix ≤
        Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
          (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) := hq
    have hE2 := hE1.trans hq'
    have hmul : 0 ≤ Real.sqrt nu *
        cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := mul_nonneg hsqnu hG
    refine mul_le_mul_of_nonneg_right ?_ hmul
    refine mul_le_mul (mul_le_mul_of_nonneg_left hnorm (by norm_num)) hq' hE1
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hA : 0 ≤ (2 * (1 / 4 : ℝ))⁻¹ * ((2 / 9 : ℝ)⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - 2 / 9)⁻¹ * C₁ :=
    by norm_num; exact hC₁.le
  calc _ ≤ (2 * (1 / 4 : ℝ))⁻¹ * ((2 / 9 : ℝ)⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - 2 / 9)⁻¹ *
        (C₁ * ((2 / 9 : ℝ)⁻¹ * Real.sqrt sigma *
          Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
            (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
          (Real.sqrt nu * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hC₁.le) (by norm_num)
    _ = _ := by ring

theorem cubeLpNorm_const_mul (Q : TriadicCube d) (c : ℝ) (f : Vec d → ℝ) :
    cubeLpNorm Q 2 (fun x => c * f x) = |c| * cubeLpNorm Q 2 f := by
  unfold cubeLpNorm
  have : (fun x => c * f x) = c • f := by
    funext x
    simp
  rw [this, MeasureTheory.eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

/-- The `L²` size of the zero-trace remainder. -/
theorem l2_bound (d : ℕ) [NeZero d] :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
      (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
      {sigma nu : ℝ}, 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      ∀ (u : AHarmonicFunction a (openCubeSet Q)) (w : H10Function (openCubeSet Q)),
      (∀ ψ : H10Function (openCubeSet Q),
        ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
          ∫ x in openCubeSet Q, vecDot (u.toH1.grad x) (ψ.toH1Function.grad x)) →
      cubeBesovScaleWeight (1 : ℝ) Q * cubeLpNorm Q 2 (fun x => w.toH1Function.toFun x) ≤
        C₃ * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
          Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
            (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
          cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C₂, hC₂, hbound⟩ := negBesov_bound d
  obtain ⟨Kh, hKh⟩ : ∃ K : ℝ, ∀ (Q : TriadicCube d) (v : H10Function (cubeSet Q)),
      cubeBesovScaleWeight (1 : ℝ) Q * cubeLpNorm Q 2 (fun x => v.toH1Function.toFun x) ≤
        K * cubeBesovNegativeVectorSeminormTwo Q (2 * (1 / 4)) (fun x => v.toH1Function.grad x) :=
    ⟨_, fun Q v => Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
      Q (t := 1 / 4) v (by norm_num) (by norm_num)⟩
  refine ⟨max Kh 1 * C₂, by positivity, ?_⟩
  intro Q lam Lam a hEll h0 hle sigma nu hs hnu hsym u w hw
  have hb := hbound Q hEll h0 hle hs hnu hsym u w hw
  have hh := hKh Q (sigma • w).toCubeSet
  have hgrad : (sigma • w).toCubeSet.toH1Function.grad = fun x => sigma • w.toH1Function.grad x :=
    H10Function.toCubeSet_toH1Function_grad _
  have hfun : (sigma • w).toCubeSet.toH1Function.toFun = fun x => sigma * w.toH1Function.toFun x :=
    H10Function.toCubeSet_toH1Function_toFun _
  rw [hgrad, hfun, cubeLpNorm_const_mul, abs_of_pos hs] at hh
  beta_reduce at hh
  have hN0 := cubeBesovNegativeVectorSeminormTwo_nonneg' Q (2 * (1 / 4))
    (fun x => sigma • w.toH1Function.grad x)
  have hKK : Kh ≤ max Kh 1 := le_max_left _ _
  have hsq : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hs
  refine le_of_mul_le_mul_left ?_ hs
  calc sigma * (cubeBesovScaleWeight (1 : ℝ) Q * cubeLpNorm Q 2 fun x => w.toH1Function.toFun x)
      = cubeBesovScaleWeight (1 : ℝ) Q * (sigma * cubeLpNorm Q 2 fun x => w.toH1Function.toFun x) := by
        ring
    _ ≤ Kh * cubeBesovNegativeVectorSeminormTwo Q (2 * (1 / 4))
        (fun x => sigma • w.toH1Function.grad x) := hh
    _ ≤ max Kh 1 * cubeBesovNegativeVectorSeminormTwo Q (2 * (1 / 4))
        (fun x => sigma • w.toH1Function.grad x) := mul_le_mul_of_nonneg_right hKK hN0
    _ ≤ max Kh 1 * (C₂ * Real.sqrt sigma * Real.sqrt nu *
          Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
            (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
          cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) :=
        mul_le_mul_of_nonneg_left hb (le_trans zero_le_one (le_max_right _ _))
    _ = sigma * (max Kh 1 * C₂ * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
          Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
            (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
          cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
        have e : sigma * (Real.sqrt sigma)⁻¹ = Real.sqrt sigma := by
          field_simp
          exact (Real.sq_sqrt hs.le).symm
        rw [show sigma * (max Kh 1 * C₂ * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
            Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
              (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
            cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) =
          (sigma * (Real.sqrt sigma)⁻¹) * (max Kh 1 * C₂ * Real.sqrt nu *
            Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
              (Book.Ch02.MultiscaleExponent.finite 2) (paddedFamily Q hEll h0 hle) (sigma • 1) *
            cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) by ring, e]
        ring

theorem matVecMul_one' (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  have := matVecMul_scalarMatrix (d := d) 1 x
  simpa using this

/-- The identity-coefficient harmonic function `u - w` with the boundary values of `u`. -/
def harmonicRemainder {a : CoeffField d} (Q : TriadicCube d)
    (u : AHarmonicFunction a (openCubeSet Q)) (w : H10Function (openCubeSet Q))
    (hw : ∀ ψ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
        ∫ x in openCubeSet Q, vecDot (u.toH1.grad x) (ψ.toH1Function.grad x)) :
    AHarmonicFunction (fun _ => (1 : Mat d)) (openCubeSet Q) where
  toH1 := u.toH1 - w.toH1Function
  isHarmonic := by
    refine ⟨H1Function.isPotentialOn _, ?_⟩
    intro φ
    have hint1 : MeasureTheory.IntegrableOn
        (fun x => vecDot (u.toH1.grad x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 u.toH1.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
    have hint2 : MeasureTheory.IntegrableOn
        (fun x => vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
      integrableOn_vecDot_of_memVectorL2 w.toH1Function.grad_memVectorL2
        φ.toH1Function.grad_memVectorL2
    simp only [H1Function.sub_grad, matVecMul_one', vecDot_sub_left']
    rw [MeasureTheory.integral_sub hint1 hint2, hw φ, sub_self]

theorem eLpNorm_normalizedCubeMeasure_le {Q' Q : TriadicCube d} (h : cubeSet Q' ⊆ cubeSet Q)
    (f : Vec d → ℝ) (hf : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q') ≤
      ENNReal.ofReal (cubeVolume Q / cubeVolume Q') ^ (1 / 2 : ℝ) *
        MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q) := by
  have hQ : 0 < cubeVolume Q := cubeVolume_pos Q
  have hQ' : 0 < cubeVolume Q' := cubeVolume_pos Q'
  have hrest : cubeMeasure Q' ≤ cubeMeasure Q := MeasureTheory.Measure.restrict_mono h le_rfl
  have hμ : normalizedCubeMeasure Q' ≤
      ENNReal.ofReal (cubeVolume Q / cubeVolume Q') • normalizedCubeMeasure Q := by
    unfold normalizedCubeMeasure
    rw [smul_smul, ← ENNReal.ofReal_mul (by positivity)]
    have : cubeVolume Q / cubeVolume Q' * (cubeVolume Q)⁻¹ = (cubeVolume Q')⁻¹ := by
      field_simp
    rw [this]
    intro t
    simp only [MeasureTheory.Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (hrest t) _
  calc MeasureTheory.eLpNorm f 2 (normalizedCubeMeasure Q')
      ≤ MeasureTheory.eLpNorm f 2 (ENNReal.ofReal (cubeVolume Q / cubeVolume Q') •
          normalizedCubeMeasure Q) := MeasureTheory.eLpNorm_mono_measure f hμ
    _ = _ := by
        rw [MeasureTheory.eLpNorm_smul_measure_of_ne_top (by norm_num)]
        simp
        exact hf

theorem cubeVolume_originCube_ratio (n : ℤ) :
    cubeVolume (originCube d n) / cubeVolume (originCube d (n - 1)) = (3 : ℝ) ^ d := by
  unfold cubeVolume
  simp only [cubeScaleFactor_originCube]
  rw [zpow_sub_one₀ (by norm_num), mul_pow, inv_pow]
  have : ((3 : ℝ) ^ n) ^ d ≠ 0 := by positivity
  field_simp

theorem originCube_pred_cubeSet_subset (n : ℤ) :
    cubeSet (originCube d (n - 1)) ⊆ cubeSet (originCube d n) := by
  intro x hx i
  obtain ⟨h1, h2⟩ := hx i
  have hle : (3 : ℝ) ^ (n - 1) ≤ (3 : ℝ) ^ n :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hi : ∀ (m : ℤ) (i : Fin d), (((originCube d m).index i : ℤ) : ℝ) = 0 := by
    intro m i
    simp [originCube]
  simp only [hi, cubeScaleFactor_originCube] at h1 h2 ⊢
  constructor <;> nlinarith only [h1, h2, hle]

theorem originCube_pred_openCubeSet_subset (n : ℤ) :
    openCubeSet (originCube d (n - 1)) ⊆ openCubeSet (originCube d n) := by
  intro x hx i
  obtain ⟨h1, h2⟩ := hx i
  have hle : (3 : ℝ) ^ (n - 1) ≤ (3 : ℝ) ^ n :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hi : ∀ (m : ℤ) (i : Fin d), (((originCube d m).index i : ℤ) : ℝ) = 0 := by
    intro m i
    simp [originCube]
  simp only [hi, cubeScaleFactor_originCube] at h1 h2 ⊢
  constructor <;> nlinarith only [h1, h2, hle]

/-- Harmonic approximation on a pair of nested triadic cubes of volume ratio `3^d`. -/
theorem harmonic_approximation_cube (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q Q' : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
      {sigma nu delta : ℝ}, cubeSet Q' ⊆ cubeSet Q → openCubeSet Q' ⊆ openCubeSet Q →
      cubeVolume Q / cubeVolume Q' = (3 : ℝ) ^ d →
      IsEllipticFieldOn lam Lam (cubeSet Q) a → 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet Q, symmPart (a x) = nu • (1 : Mat d)) →
      HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta →
      ∀ u : AHarmonicFunction a (openCubeSet Q),
        ∃ w : AHarmonicFunction (fun _ => (1 : Mat d)) (openCubeSet Q'),
          ENNReal.ofReal (cubeBesovScaleWeight (1 : ℝ) Q) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q' 2
                (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
            ENNReal.ofReal (C * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
                (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C₃, hC₃, hl2⟩ := l2_bound d
  refine ⟨Real.sqrt ((3 : ℝ) ^ d) * C₃, by positivity, ?_⟩
  intro Q Q' lam Lam a sigma nu delta hsubC hsub hratio hEll hs hnu hsym hE u
  obtain ⟨x0, hx0⟩ := Book.Ch02.openCubeSet_nonempty Q
  have hell0 := hEll.2 x0 (openCubeSet_subset_cubeSet _ hx0)
  have h0 : 0 < lam := hell0.1
  have hle : lam ≤ Lam := hell0.2.1
  obtain ⟨w, hw⟩ := exists_zeroTrace_remainder Q one_pos u.toH1
  have hfin : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q')) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q').isFiniteMeasure_restrict_volume
  let v := harmonicRemainder Q u w hw
  let vr : H1Function (openCubeSet Q') := v.toH1.restrict (isOpen_openCubeSet Q') hsub
  have hvr : IsAHarmonicGradient (fun _ => (1 : Mat d)) (openCubeSet Q') vr.grad := by
    refine IsAHarmonicGradient.restrict_of_isOpen_of_memVectorL2 v.isHarmonic
      (isOpen_openCubeSet Q) (isOpen_openCubeSet Q') hsub ?_
    simpa [matVecMul_one'] using vr.grad_memVectorL2
  refine ⟨⟨vr, hvr⟩, ?_⟩
  have hf : (fun x => u.toH1.toFun x - (⟨vr, hvr⟩ : AHarmonicFunction (fun _ => (1 : Mat d))
      (openCubeSet Q')).toH1.toFun x) = fun x => w.toH1Function.toFun x := by
    funext x
    show u.toH1.toFun x - (u.toH1 - w.toH1Function).toFun x = w.toH1Function.toFun x
    rw [H1Function.sub_toFun]
    ring
  rw [hf]
  -- the `L²` norms
  have hwL2 : MeasureTheory.MemLp (fun x => w.toH1Function.toFun x) 2 (normalizedCubeMeasure Q) :=
    w.toH1Function.memL2_normalizedCubeMeasure
  have hGL2 := memLp_sqrt_vecNormSq_grad u.toH1
  have hwE : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => w.toH1Function.toFun x) = ENNReal.ofReal (cubeLpNorm Q 2
        (fun x => w.toH1Function.toFun x)) := by
    unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm cubeLpNorm
    rw [ENNReal.ofReal_toReal hwL2.eLpNorm_lt_top.ne]
  have hGE : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 2
      (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) = ENNReal.ofReal (cubeLpNorm Q 2
        (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
    unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm cubeLpNorm
    rw [ENNReal.ofReal_toReal hGL2.eLpNorm_lt_top.ne]
  have hsmall : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q' 2
      (fun x => w.toH1Function.toFun x) ≤
      ENNReal.ofReal (Real.sqrt ((3 : ℝ) ^ d)) *
        ENNReal.ofReal (cubeLpNorm Q 2 (fun x => w.toH1Function.toFun x)) := by
    have := eLpNorm_normalizedCubeMeasure_le hsubC (fun x => w.toH1Function.toFun x)
      hwL2.aestronglyMeasurable
    rw [hratio, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← Real.sqrt_eq_rpow] at this
    rw [← hwE]
    exact this
  -- the real estimate
  have hreal := hl2 Q hEll h0 hle hs hnu hsym u w hw
  rw [← homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2 (sigma • (1 : Mat d))] at hreal
  have hW : 0 ≤ cubeBesovScaleWeight (1 : ℝ) Q := cubeBesovScaleWeight_nonneg 1 Q
  have hG0 : 0 ≤ cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    cubeLpNorm_nonneg _ _ _
  have hw0 : 0 ≤ cubeLpNorm Q 2 (fun x => w.toH1Function.toFun x) := cubeLpNorm_nonneg _ _ _
  have hK0 : 0 ≤ Real.sqrt ((3 : ℝ) ^ d) := Real.sqrt_nonneg _
  have hcoef : 0 ≤ C₃ * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
      cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC₃.le (inv_nonneg.2 (Real.sqrt_nonneg _)))
      (Real.sqrt_nonneg _)) hG0
  have hE' : C₃ * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
      HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) *
      cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) ≤
      C₃ * (Real.sqrt sigma)⁻¹ * Real.sqrt nu * delta *
      cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
    refine mul_le_mul_of_nonneg_right ?_ hG0
    exact mul_le_mul_of_nonneg_left hE
      (mul_nonneg (mul_nonneg hC₃.le (inv_nonneg.2 (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _))
  calc ENNReal.ofReal (cubeBesovScaleWeight (1 : ℝ) Q) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q' 2 (fun x => w.toH1Function.toFun x)
      ≤ ENNReal.ofReal (cubeBesovScaleWeight (1 : ℝ) Q) *
        (ENNReal.ofReal (Real.sqrt ((3 : ℝ) ^ d)) *
          ENNReal.ofReal (cubeLpNorm Q 2 (fun x => w.toH1Function.toFun x))) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt ((3 : ℝ) ^ d) * (cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q 2 (fun x => w.toH1Function.toFun x))) := by
        rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul hW, mul_left_comm]
    _ ≤ ENNReal.ofReal (Real.sqrt ((3 : ℝ) ^ d) * (C₃ * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
          delta * cubeLpNorm Q 2 (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))))) := by
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hreal.trans hE') hK0)
    _ = ENNReal.ofReal (Real.sqrt ((3 : ℝ) ^ d) * C₃ * delta * (Real.sqrt sigma)⁻¹ *
          Real.sqrt nu) * ENNReal.ofReal (cubeLpNorm Q 2
            (fun x => Real.sqrt (vecNormSq (u.toH1.grad x)))) := by
        rw [← ENNReal.ofReal_mul' hG0]
        congr 1
        ring
    _ = _ := by rw [hGE]

/-- **Harmonic approximation, deterministic form.** If the homogenization error
`𝓔_{1/9,2}(cu_n; a, σ Id)` is at most `δ`, and `a` has symmetric part `ν Id` and is elliptic on
`cu_n`, then every `a`-harmonic function on `cu_n` is `L²`-close to a harmonic function on
`cu_{n-1}`, with the rate `δ σ^{-1/2} ν^{1/2} ‖∇u‖`. -/
theorem harmonic_approximation_deterministic (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu delta : ℝ},
      IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a → 0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet (originCube d n), symmPart (a x) = nu • (1 : Mat d)) →
      HomogenizationErrorOnCube (originCube d n) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta →
      ∀ u : AHarmonicFunction a (openCubeSet (originCube d n)),
        ∃ w : AHarmonicFunction (fun _ => (1 : Mat d)) (openCubeSet (originCube d (n - 1))),
          ENNReal.ofReal ((3 : ℝ) ^ (-n)) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n - 1)) 2
                (fun x => u.toH1.toFun x - w.toH1.toFun x) ≤
            ENNReal.ofReal (C * delta * (Real.sqrt sigma)⁻¹ * Real.sqrt nu) *
              SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d n) 2
                (fun x => Real.sqrt (vecNormSq (u.toH1.grad x))) := by
  obtain ⟨C, hC, h⟩ := harmonic_approximation_cube d
  refine ⟨C, hC, ?_⟩
  intro n lam Lam a sigma nu delta hEll hs hnu hsym hE u
  obtain ⟨w, hw⟩ := h (originCube d n) (originCube d (n - 1)) (originCube_pred_cubeSet_subset n)
    (originCube_pred_openCubeSet_subset n) (cubeVolume_originCube_ratio n) hEll hs hnu hsym hE u
  refine ⟨w, ?_⟩
  have hW : cubeBesovScaleWeight (1 : ℝ) (originCube d n) = (3 : ℝ) ^ (-n) := by
    unfold cubeBesovScaleWeight
    rw [cubeScaleFactor_originCube, Real.rpow_neg_one, zpow_neg]
  rwa [hW] at hw

/-- Witness (satisfiability): all non-law hypotheses of `harmonic_approximation_deterministic`
are satisfiable together (constant identity field, `σ = ν = 1`, `δ` the error itself, `u = 0`). -/
example (d : ℕ) [NeZero d] (n : ℤ) :
    ∃ (a : CoeffField d) (lam Lam sigma nu delta : ℝ),
      IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a ∧ 0 < sigma ∧ 0 < nu ∧
      (∀ x ∈ cubeSet (originCube d n), symmPart (a x) = nu • (1 : Mat d)) ∧
      HomogenizationErrorOnCube (originCube d n) (1 / 9) MultiscaleExponent.infinity
        (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta ∧
      Nonempty (AHarmonicFunction a (openCubeSet (originCube d n))) := by
  classical
  refine ⟨fun _ => (1 : Mat d), 1, 1, 1, 1, _, ?_, one_pos, one_pos, ?_, le_rfl, ?_⟩
  · refine ⟨?_, fun x _ => ?_⟩
    · exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
        Measurable.ite (measurableSet_cubeSet _) measurable_const measurable_const
    · simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) one_pos
  · intro x _
    ext i j
    by_cases h : i = j
    · subst h
      simp [symmPart]
    · simp [symmPart, h, Ne.symm h]
  · exact ⟨⟨0, isAHarmonicGradient_zero⟩⟩

end
end SuperdiffusionCLT.Section6.HarmonicApprox
