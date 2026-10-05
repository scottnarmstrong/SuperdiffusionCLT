/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxBridge
public import SuperdiffusionCLT.Section6.Lemma.WeakFluxB
public import Homogenization.Besov.Duality.CaccioppoliBridge
public import Homogenization.Internal.Ch02.SymmetricDirichletNeumann.Dirichlet

/-!
# Corrected affines on one cube: the analytic estimates

For one basis direction `p` (with `|p| ≤ 1`) the affine Dirichlet problem on `□_n` gives a solution
`u = ℓ_p + w` with `w` of zero trace. This file proves the energy identity for `u`, the bound
`ν^{1/2} ‖∇u‖ ≤ (C + 1) σ^{1/2}` through the constant test function of the dual negative Besov
norm, and the flatness bound `cubeFlat n (u - ℓ_p) ≤ C δ` (`ea3_basis`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6
open Homogenization MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem ea3_abs_avg_le (Q : TriadicCube d) (s : ℝ) (hs : 0 < s) (F : Vec d → ℝ)
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    |cubeAverage Q F| ≤ cubeBesovScaleWeight s Q * cubeBesovDualFullNorm Q s 2 2 F := by
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hg : CubeBesovDualFullTest Q s 2 2 (fun _ => cubeBesovScaleWeight (-s) Q) := by
    refine ⟨fun N => (cubeBesovDualTest_const_scaleWeight_neg Q s 2 2 N
      (by rw [hconj]; norm_num) (by rw [hconj]; simp)).1, ?_⟩
    intro j R hR
    rw [hconj]
    exact (memLp_const _).sub (memLp_const _)
  have h := abs_cubeBesovPairing_le_cubeBesovDualFullNorm_of_full_test_of_memLp Q s 2 2 F
    (fun _ => cubeBesovScaleWeight (-s) Q) hs hF (by norm_num) (by simp)
    (by rw [hconj]; simp) (by norm_num) hg
  rw [cubeBesovPairing_const_right, abs_mul, abs_of_nonneg (cubeBesovScaleWeight_nonneg _ Q)] at h
  have hm : cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q = 1 :=
    cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight Q s
  have hp : 0 < cubeBesovScaleWeight s Q := by
    unfold cubeBesovScaleWeight; exact Real.rpow_pos_of_pos (by unfold cubeScaleFactor; positivity) _
  calc |cubeAverage Q F| = cubeBesovScaleWeight s Q * (cubeBesovScaleWeight (-s) Q * |cubeAverage Q F|) := by
        rw [← mul_assoc, mul_comm (cubeBesovScaleWeight s Q), hm, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hp.le

theorem ea3_ellipticOn_congr {U : Set (Vec d)} {lam Lam : ℝ} {a b : CoeffField d}
    (h : IsEllipticFieldOn lam Lam U a) (hab : ∀ x ∈ U, a x = b x) :
    IsEllipticFieldOn lam Lam U b := by
  classical
  unfold IsEllipticFieldOn at h ⊢
  refine ⟨?_, fun x hx => hab x hx ▸ h.2 x hx⟩
  have : (fun x i j => if x ∈ U then b x i j else 0) = fun x i j => if x ∈ U then a x i j else 0 := by
    funext x i j
    by_cases hx : x ∈ U
    · simp [hx, hab x hx]
    · simp [hx]
  rw [this]; exact h.1

theorem ea3_dirichlet [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    (p : Vec d) :
    ∃ w : H10Function (openCubeSet Q),
      IsAHarmonicGradient a (openCubeSet Q) (fun x => p + w.toH1Function.grad x) := by
  let A := HarmonicApprox.paddedCoeffOn Q hEll h0 hle (Book.Ch02.cubeDomain Q)
  have hsub : openCubeSet Q ⊆ cubeSet Q := openCubeSet_subset_cubeSet Q
  have hmeas : MeasurableSet (openCubeSet Q) := (Book.Ch02.cubeDomain Q).measurableSet
  have hA : IsEllipticFieldOn A.lam A.Lam ((Book.Ch02.cubeDomain Q : Book.Ch02.Domain d) : Set (Vec d))
      A.toCoeffField := by
    rw [Book.Ch02.cubeDomain_coe]
    exact ea3_ellipticOn_congr (hEll.mono hmeas hsub)
      (fun x hx => (HarmonicApprox.padField_apply_of_mem (hsub hx)).symm)
  obtain ⟨u, hu⟩ := Homogenization.Internal.Ch02.BookCh02.exists_isAffineDirichletSolution_of_isEllipticFieldOn
    (Book.Ch02.cubeDomain Q) A hA p
  obtain ⟨w, hw⟩ := hu.2
  refine ⟨w, ?_⟩
  have hg : (fun x => p + w.toH1Function.grad x) = u.grad := by
    funext x
    have := congrFun hw x
    rw [this]; abel
  rw [hg]
  refine IsAHarmonicGradient.of_ae_eq_coeff ?_ hu.1
  unfold volumeMeasureOn
  filter_upwards [MeasureTheory.ae_restrict_mem hmeas] with x hx
  exact HarmonicApprox.padField_apply_of_mem (hsub hx)

theorem ea3_prob (Q : TriadicCube d) : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
  ⟨by simp [normalizedCubeMeasure_apply_univ]⟩

theorem ea3_sq (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (cubeLpNorm Q 2 f) ^ 2 = cubeAverage Q (fun x => (f x) ^ 2) := by
  have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2 f (by norm_num) (by norm_num) hf
  simp only [ENNReal.toReal_ofNat] at h
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  rw [h]
  unfold cubeAverage
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, Real.rpow_natCast, sq_abs]

theorem ea3_flat_le (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 2 (fun x => f x - cubeAverage Q f) ≤ cubeLpNorm Q 2 f := by
  have := ea3_prob Q
  set m := cubeAverage Q f with hm
  have hc : MemLp (fun x => f x - m) 2 (normalizedCubeMeasure Q) := hf.sub (memLp_const m)
  have h1 := ea3_sq Q hc
  have h2 := ea3_sq Q hf
  have hi1 : Integrable f (normalizedCubeMeasure Q) := hf.integrable (by norm_num)
  have hi2 : Integrable (fun x => (f x) ^ 2) (normalizedCubeMeasure Q) := hf.integrable_sq
  have key : cubeAverage Q (fun x => (f x - m) ^ 2) = cubeAverage Q (fun x => (f x) ^ 2) - m ^ 2 := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure]
    have : (fun x => (f x - m) ^ 2) = fun x => (f x) ^ 2 - 2 * m * f x + m ^ 2 := by
      funext x; ring
    have hint : Integrable (fun x => (f x) ^ 2 - 2 * m * f x) (normalizedCubeMeasure Q) :=
      hi2.sub (hi1.const_mul _)
    rw [this, integral_add hint (integrable_const _),
      integral_sub hi2 (hi1.const_mul _), integral_const_mul]
    have : ∫ x, f x ∂normalizedCubeMeasure Q = m := (cubeAverage_eq_integral_normalizedCubeMeasure Q f).symm
    rw [this]
    simp
    ring
  have hle : (cubeLpNorm Q 2 (fun x => f x - m)) ^ 2 ≤ (cubeLpNorm Q 2 f) ^ 2 := by
    rw [h1, h2, key]; linarith only [sq_nonneg m]
  exact le_of_sq_le_sq hle (cubeLpNorm_nonneg _ _ _)

theorem ea3_fin (n : ℕ) : IsFiniteMeasure (volumeMeasureOn (engCube d n)) :=
  ⟨by simpa [volumeMeasureOn, Measure.restrict_apply_univ] using
    (volume_openCubeSet_lt_top (originCube d (n : ℤ)))⟩

theorem ea3_matVecMul_scalar_dot (A : Mat d) {nu : ℝ} (h : symmPart A = nu • (1 : Mat d))
    (ξ : Vec d) : vecDot ξ (matVecMul A ξ) = nu * vecNormSq ξ := by
  rw [← vecDot_matVecMul_symmPart, h, smul_matVecMul]
  have : matVecMul (1 : Mat d) ξ = ξ := by
    funext i
    simp [matVecMul, Matrix.one_apply]
  rw [this, vecDot_smul_right]
  rfl

theorem ea3_integral_energy [NeZero d] (n : ℕ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a)
    (hsym : ∀ x ∈ cubeSet (originCube d (n : ℤ)), symmPart (a x) = nu • (1 : Mat d))
    (p : Vec d) (w : H10Function (engCube d n)) (v : AHarmonicFunction a (engCube d n))
    (hv : v.toH1.grad = fun x => p + w.toH1Function.grad x) :
    nu * cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (v.toH1.grad x)) =
      sigma * vecNormSq p +
        ∑ j : Fin d, p j * cubeAverage (originCube d (n : ℤ))
          (fun x => matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) j) := by
  have := ea3_fin (d := d) n
  have hGm : MemVectorL2 (engCube d n) v.toH1.grad := MemLp.of_eval fun i => v.toH1.gradMemL2 i
  have hell : IsEllipticFieldOn lam Lam (engCube d n) a := hEll.mono (measurableSet_openCubeSet (originCube d (n : ℤ))) (openCubeSet_subset_cubeSet (originCube d (n : ℤ)))
  have haG : MemVectorL2 (engCube d n) (fun x => matVecMul (a x) (v.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hell hGm
  have hsG : MemVectorL2 (engCube d n) (fun x => sigma • v.toH1.grad x) := hGm.const_smul sigma
  have hF : MemVectorL2 (engCube d n) (fun x => matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) := by
    have : (fun x => matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) =
        fun x => matVecMul (a x) (v.toH1.grad x) - sigma • v.toH1.grad x := by
      funext x
      rw [sub_matVecMul, smul_matVecMul]
      have : matVecMul (1 : Mat d) (v.toH1.grad x) = v.toH1.grad x := by
        funext i; simp [matVecMul, Matrix.one_apply]
      rw [this]
    rw [this]; exact haG.sub hsG
  have hwm : MemVectorL2 (engCube d n) w.toH1Function.grad := MemLp.of_eval fun i => w.toH1Function.gradMemL2 i
  have hpm : MemVectorL2 (engCube d n) (fun _ => p) := memLp_const p
  have hdec : ∀ x, vecDot (v.toH1.grad x) (matVecMul (a x) (v.toH1.grad x)) =
      sigma * vecNormSq p + sigma * vecDot p (w.toH1Function.grad x) +
        vecDot p (matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) +
        vecDot (w.toH1Function.grad x) (matVecMul (a x) (v.toH1.grad x)) := by
    intro x
    have h1 : matVecMul (a x) (v.toH1.grad x) = sigma • v.toH1.grad x +
        matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) := by
      rw [sub_matVecMul, smul_matVecMul]
      have : matVecMul (1 : Mat d) (v.toH1.grad x) = v.toH1.grad x := by
        funext i; simp [matVecMul, Matrix.one_apply]
      rw [this]; abel
    have h2 : v.toH1.grad x = p + w.toH1Function.grad x := congrFun hv x
    set F := matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)
    set A := matVecMul (a x) (v.toH1.grad x)
    set W := w.toH1Function.grad x
    calc vecDot (v.toH1.grad x) A = vecDot (p + W) A := by rw [h2]
      _ = vecDot p A + vecDot W A := vecDot_add_left _ _ _
      _ = _ := by
        rw [h1, vecDot_add_right, vecDot_smul_right, h2, vecDot_add_right]
        simp only [vecNormSq]
        ring
  have i1 : IntegrableOn (fun _ => sigma * vecNormSq p) (engCube d n) := integrableOn_const (by
    simpa using (volume_openCubeSet_lt_top (originCube d (n : ℤ))).ne)
  have i2 := (integrableOn_vecDot_of_memVectorL2 hpm hwm).const_mul sigma
  have i3 := integrableOn_vecDot_of_memVectorL2 hpm hF
  have i4 := integrableOn_vecDot_of_memVectorL2 hwm haG
  have z1 : ∫ x in (engCube d n), vecDot p (w.toH1Function.grad x) ∂volume = 0 :=
    CorrectionFieldData.integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords p hwm
      (IsPotentialZeroTraceOn.integral_eq_zero w.isPotentialZeroTraceOn)
  have z2 : ∫ x in (engCube d n), vecDot (w.toH1Function.grad x) (matVecMul (a x) (v.toH1.grad x)) ∂volume = 0 := by
    have := v.isHarmonic.2 w
    simpa [vecDot_comm] using this
  have hI2 : ∫ x in (engCube d n), vecDot (v.toH1.grad x) (matVecMul (a x) (v.toH1.grad x)) ∂volume =
      sigma * vecNormSq p * cubeVolume (originCube d (n : ℤ)) +
        ∫ x in (engCube d n), vecDot p (matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) ∂volume := by
    simp_rw [hdec]
    have k2 : Integrable (fun x => sigma * vecNormSq p + sigma * vecDot p (w.toH1Function.grad x))
        (volume.restrict (engCube d n)) := i1.add i2
    have k3 : Integrable (fun x => sigma * vecNormSq p + sigma * vecDot p (w.toH1Function.grad x) +
        vecDot p (matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)))
        (volume.restrict (engCube d n)) := k2.add i3
    rw [integral_add k3 i4, integral_add k2 i3, integral_add i1 i2,
      integral_const_mul sigma (fun x => vecDot p (w.toH1Function.grad x)), z1, z2,
      setIntegral_const]
    have hv : (volume (engCube d n)).toReal = cubeVolume (originCube d (n : ℤ)) :=
      volume_openCubeSet_toReal _
    simp only [Measure.real, hv, smul_eq_mul, mul_zero, add_zero]
    ring
  have hF2 : ∫ x in (engCube d n), vecDot p (matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) ∂volume =
      ∑ j : Fin d, p j * ∫ x in (engCube d n), matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) j ∂volume := by
    simp_rw [show ∀ x, vecDot p (matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) =
      ∑ j : Fin d, p j * matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) j from fun x => rfl]
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
    · intro j _
      exact ((hF.eval j).integrable (by norm_num)).const_mul _
  have hI1 : ∫ x in (engCube d n), vecDot (v.toH1.grad x) (matVecMul (a x) (v.toH1.grad x)) ∂volume =
      nu * ∫ x in (engCube d n), vecNormSq (v.toH1.grad x) ∂volume := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_openCubeSet (originCube d (n : ℤ))) fun x hx => ?_
    exact ea3_matVecMul_scalar_dot _ (hsym x (openCubeSet_subset_cubeSet (originCube d (n : ℤ)) hx)) _
  have hvol : 0 < cubeVolume (originCube d (n : ℤ)) := cubeVolume_pos (originCube d (n : ℤ))
  simp_rw [cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet]
  rw [hF2] at hI2
  rw [hI1] at hI2
  have : ∀ j, p j * ((cubeVolume (originCube d (n : ℤ)))⁻¹ *
        ∫ x in (engCube d n), matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) j ∂volume)
      = (cubeVolume (originCube d (n : ℤ)))⁻¹ * (p j *
        ∫ x in (engCube d n), matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) j ∂volume) :=
    fun j => by ring
  simp_rw [this, ← Finset.mul_sum]
  field_simp
  linarith only [hI2]

theorem ea3_weight (n : ℕ) (s : ℝ) :
    cubeBesovScaleWeight s (originCube d (n : ℤ)) = Real.rpow 3 (-s * ((n : ℤ) : ℝ)) := by
  show _ = (3 : ℝ) ^ (-s * ((n : ℤ) : ℝ))
  unfold cubeBesovScaleWeight cubeScaleFactor
  simp only [originCube]
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
  ring_nf

theorem ea3_flux_memLp (n : ℕ) {lam Lam : ℝ} {a : CoeffField d} {sigma : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a)
    (v : AHarmonicFunction a (engCube d n)) (j : Fin d) :
    MemLp (fun x => matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) j) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  have hell : IsEllipticFieldOn lam Lam (engCube d n) a :=
    hEll.mono (measurableSet_openCubeSet _) (openCubeSet_subset_cubeSet _)
  have hGm : MemVectorL2 (engCube d n) v.toH1.grad := MemLp.of_eval fun i => v.toH1.gradMemL2 i
  have haG := memVectorL2_matVecMul_of_isEllipticFieldOn hell hGm
  have hsG : MemVectorL2 (engCube d n) (fun x => sigma • v.toH1.grad x) := hGm.const_smul sigma
  have hF : MemVectorL2 (engCube d n) (fun x => matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) := by
    have : (fun x => matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x)) =
        fun x => matVecMul (a x) (v.toH1.grad x) - sigma • v.toH1.grad x := by
      funext x
      rw [sub_matVecMul, smul_matVecMul]
      have : matVecMul (1 : Mat d) (v.toH1.grad x) = v.toH1.grad x := by
        funext i; simp [matVecMul, Matrix.one_apply]
      rw [this]
    rw [this]; exact haG.sub hsG
  exact memL2On_openCubeSet_normalizedCubeMeasure (hF.eval j)

theorem ea3_basis (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu delta : ℝ},
      IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a → 0 < lam → lam ≤ Lam →
      0 < sigma → 0 < nu →
      (∀ x ∈ cubeSet (originCube d (n : ℤ)), symmPart (a x) = nu • (1 : Mat d)) →
      HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9) MultiscaleExponent.infinity
          (MultiscaleExponent.finite 2) a (sigma • (1 : Mat d)) ≤ delta →
      delta ≤ 1 → ∀ p : Vec d, vecNormSq p ≤ 1 →
        ∃ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d n) u g ∧
          MemLp (fun x => u x - vecDot p x) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) ∧
          cubeFlat n (fun x => u x - vecDot p x) ≤ C * delta := by
  obtain ⟨C3, hC3, hl2⟩ := HarmonicApprox.l2_bound d
  obtain ⟨Cw, hCw, hwf⟩ := WeakFlux.weak_flux_cube d
  refine ⟨C3 * (Cw + 1), by positivity, ?_⟩
  intro n lam Lam a sigma nu delta hEll h0 hle hs hnu hsym hE hd1 p hp
  have hfin := ea3_fin (d := d) n
  obtain ⟨w, hw⟩ := ea3_dirichlet (originCube d (n : ℤ)) hEll h0 hle p
  have hSob : IsSobolevRegularDomain (engCube d n) :=
    (Book.Ch02.cubeDomain (originCube d (n : ℤ))).isDomain.isSobolevRegularDomain
  let ℓ := H1Function.affineOnIsSobolevRegularDomain hSob p
  have hvg : (ℓ + w.toH1Function).grad = fun x => p + w.toH1Function.grad x := by
    funext x; simp [ℓ]
  let v : AHarmonicFunction a (engCube d n) := ⟨ℓ + w.toH1Function, hvg ▸ hw⟩
  have hvgrad : v.toH1.grad = fun x => p + w.toH1Function.grad x := hvg
  have hvfun : (fun x => v.toH1.toFun x - vecDot p x) = w.toH1Function.toFun := by
    funext x
    show (ℓ x + w.toH1Function.toFun x) - vecDot p x = _
    simp [ℓ, vecDot]
  have hsol : IsSolOn a (engCube d n) v.toH1.toFun v.toH1.grad :=
    ⟨v, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  have hwmem : MemLp w.toH1Function.toFun 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    memL2On_openCubeSet_normalizedCubeMeasure w.toH1Function.memL2
  refine ⟨v.toH1.toFun, v.toH1.grad, hsol, hvfun ▸ hwmem, ?_⟩
  rw [hvfun]
  have hwm : MemVectorL2 (engCube d n) w.toH1Function.grad :=
    MemLp.of_eval fun i => w.toH1Function.gradMemL2 i
  have hpm : MemVectorL2 (engCube d n) (fun _ => p) := memLp_const p
  -- the weak equation
  have hwe : ∀ ψ : H10Function (openCubeSet (originCube d (n : ℤ))),
      ∫ x in openCubeSet (originCube d (n : ℤ)),
        vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x) =
      ∫ x in openCubeSet (originCube d (n : ℤ)),
        vecDot (v.toH1.grad x) (ψ.toH1Function.grad x) := by
    intro ψ
    have hψ : MemVectorL2 (engCube d n) ψ.toH1Function.grad :=
      MemLp.of_eval fun i => ψ.toH1Function.gradMemL2 i
    have i1 := integrableOn_vecDot_of_memVectorL2 hpm hψ
    have i2 := integrableOn_vecDot_of_memVectorL2 hwm hψ
    have z1 : ∫ x in engCube d n, vecDot p (ψ.toH1Function.grad x) ∂volume = 0 :=
      CorrectionFieldData.integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords p hψ
        (IsPotentialZeroTraceOn.integral_eq_zero ψ.isPotentialZeroTraceOn)
    rw [hvgrad]
    simp only [vecDot_add_left]
    rw [integral_add i1 i2, z1, zero_add]
  have hE' := hE
  rw [HarmonicApprox.homogenizationErrorOnCube_eq_ch02 hEll h0 hle (1 / 9) 2 (sigma • (1 : Mat d))]
    at hE'
  have hdel : 0 ≤ delta := (WeakFlux.l6_error_two_nonneg _ (HarmonicApprox.paddedFamily _ hEll h0 hle)
    (sigma • 1) (by norm_num)).trans hE'
  have hl := hl2 (originCube d (n : ℤ)) hEll h0 hle hs hnu hsym v w hwe
  have hmemG := hsol.memLp.2
  have hX0 : 0 ≤ cubeLpNorm (originCube d (n : ℤ)) 2
      (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) := cubeLpNorm_nonneg _ _ _
  set X := cubeLpNorm (originCube d (n : ℤ)) 2
      (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) with hX
  have hXsq : X ^ 2 = cubeAverage (originCube d (n : ℤ)) (fun x => vecNormSq (v.toH1.grad x)) := by
    have h := ea3_sq (originCube d (n : ℤ)) hmemG
    rw [hX]
    refine h.trans ?_
    unfold cubeAverage
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [engNorm]
    exact Real.sq_sqrt (vecNormSq_nonneg _)
  have hen := ea3_integral_energy (sigma := sigma) n hEll hsym p w v hvgrad
  -- dual norm of the flux defect
  set Fv : Vec d → Vec d := fun x => matVecMul (a x - sigma • (1 : Mat d)) (v.toH1.grad x) with hFv
  have hAj : ∀ j : Fin d, |cubeAverage (originCube d (n : ℤ)) (fun x => Fv x j)| ≤
      cubeBesovScaleWeight (1 / 4) (originCube d (n : ℤ)) *
        cubeBesovDualFullNorm (originCube d (n : ℤ)) (1 / 4) 2 2 (fun x => Fv x j) :=
    fun j => ea3_abs_avg_le _ _ (by norm_num) _ (ea3_flux_memLp n hEll v j)
  have hvecnorm : Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ)) (1 / 4) Fv =
      cubeBesovScaleWeight (1 / 4) (originCube d (n : ℤ)) *
        ∑ j : Fin d, cubeBesovDualFullNorm (originCube d (n : ℤ)) (1 / 4) 2 2 (fun x => Fv x j) := by
    unfold Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo
    rw [ea3_weight]
    rfl
  have hsumA : ∑ j : Fin d, |cubeAverage (originCube d (n : ℤ)) (fun x => Fv x j)| ≤
      Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo (originCube d (n : ℤ)) (1 / 4) Fv := by
    rw [hvecnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hAj j
  have hflux := hwf (originCube d (n : ℤ)) hEll hs hnu hsym hE v
  have hGE : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (n : ℤ)) 2
      (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) = ENNReal.ofReal X := by
    unfold SuperdiffusionCLT.Section2.Norms.cubeLpENorm
    rw [hX]; unfold cubeLpNorm
    exact (ENNReal.ofReal_toReal (show eLpNorm (fun x => Real.sqrt (vecNormSq (v.toH1.grad x))) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) ≠ ⊤ from hmemG.eLpNorm_lt_top.ne)).symm
  have hs0 := Real.sqrt_nonneg sigma
  have hn0 := Real.sqrt_nonneg nu
  have hc0 : 0 ≤ Cw * Real.sqrt sigma * delta * Real.sqrt nu :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hCw]) hs0) hdel) hn0
  rw [hGE, ← ENNReal.ofReal_mul hc0] at hflux
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc0 hX0)).1 hflux
  have hpj : ∀ j, |p j| ≤ 1 := by
    intro j
    have h1 : p j * p j ≤ vecNormSq p :=
      Finset.single_le_sum (f := fun i => p i * p i) (fun i _ => mul_self_nonneg _)
        (Finset.mem_univ j)
    exact abs_le_one_iff_mul_self_le_one.2 (h1.trans hp)
  have hdot : ∑ j : Fin d, p j * cubeAverage (originCube d (n : ℤ)) (fun x => Fv x j) ≤
      ∑ j : Fin d, |cubeAverage (originCube d (n : ℤ)) (fun x => Fv x j)| := by
    refine Finset.sum_le_sum fun j _ => ?_
    calc _ ≤ |p j * cubeAverage (originCube d (n : ℤ)) (fun x => Fv x j)| := le_abs_self _
      _ = |p j| * |cubeAverage (originCube d (n : ℤ)) (fun x => Fv x j)| := abs_mul _ _
      _ ≤ 1 * |cubeAverage (originCube d (n : ℤ)) (fun x => Fv x j)| :=
          mul_le_mul_of_nonneg_right (hpj j) (abs_nonneg _)
      _ = _ := one_mul _
  have hsp : sigma * vecNormSq p ≤ sigma := by
    nlinarith only [hs, hp]
  have hnuX : nu * X ^ 2 ≤ sigma + Cw * Real.sqrt sigma * delta * Real.sqrt nu * X := by
    rw [hXsq]
    linarith only [hen, hsp, hdot, hsumA, hreal]
  have hs2 : Real.sqrt sigma ^ 2 = sigma := Real.sq_sqrt hs.le
  have hr2 : Real.sqrt nu ^ 2 = nu := Real.sq_sqrt hnu.le
  have hspos : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hs
  have hY : Real.sqrt nu * X ≤ (Cw + 1) * Real.sqrt sigma := by
    by_contra hcon
    rw [not_le] at hcon
    set t := Real.sqrt nu * X with ht
    set sg := Real.sqrt sigma with hsg
    have ht2 : t ^ 2 ≤ sg ^ 2 + Cw * sg * t := by
      have h1 : t ^ 2 = nu * X ^ 2 := by rw [ht, mul_pow, hr2]
      have h2 : Cw * Real.sqrt sigma * delta * Real.sqrt nu * X = Cw * sg * delta * t := by
        rw [ht, hsg]; ring
      have h3 : Cw * sg * delta * t ≤ Cw * sg * t := by
        have : 0 ≤ Cw * sg * t := by
          have : 0 ≤ t := by rw [ht]; exact mul_nonneg (Real.sqrt_nonneg _) hX0
          positivity
        nlinarith only [this, hd1, hdel, hCw, hspos]
      rw [h2] at hnuX
      rw [h1]
      linarith only [hnuX, h3, hs2]
    have htpos : 0 < t := by
      have : 0 < (Cw + 1) * sg := by positivity
      linarith only [hcon, this]
    nlinarith only [ht2, hcon, htpos, hspos, hCw]
  have hw1 : cubeBesovScaleWeight 1 (originCube d (n : ℤ)) = ((3 : ℝ)⁻¹) ^ n := by
    rw [ea3_weight]
    show (3 : ℝ) ^ (-1 * ((n : ℤ) : ℝ)) = _
    rw [show (-1 * ((n : ℤ) : ℝ)) = -((n : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (by norm_num),
      Real.rpow_natCast, inv_pow]
  have hflat : cubeFlat n w.toH1Function.toFun ≤ ((3 : ℝ)⁻¹) ^ n *
      cubeLpNorm (originCube d (n : ℤ)) 2 (fun x => w.toH1Function.toFun x) := by
    unfold cubeFlat cubeL2
    exact mul_le_mul_of_nonneg_left (ea3_flat_le _ hwmem) (by positivity)
  refine hflat.trans ?_
  rw [← hw1]
  refine hl.trans ?_
  have hnn : 0 ≤ C3 * (Real.sqrt sigma)⁻¹ * Real.sqrt nu * X := by positivity
  calc C3 * (Real.sqrt sigma)⁻¹ * Real.sqrt nu *
        Book.Ch02.HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9)
          Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
          (HarmonicApprox.paddedFamily (originCube d (n : ℤ)) hEll h0 hle) (sigma • 1) * X
      = (C3 * (Real.sqrt sigma)⁻¹ * Real.sqrt nu * X) *
        Book.Ch02.HomogenizationErrorOnCube (originCube d (n : ℤ)) (1 / 9)
          Book.Ch02.MultiscaleExponent.infinity (Book.Ch02.MultiscaleExponent.finite 2)
          (HarmonicApprox.paddedFamily (originCube d (n : ℤ)) hEll h0 hle) (sigma • 1) := by ring
    _ ≤ (C3 * (Real.sqrt sigma)⁻¹ * Real.sqrt nu * X) * delta :=
        mul_le_mul_of_nonneg_left hE' hnn
    _ = C3 * (Real.sqrt sigma)⁻¹ * delta * (Real.sqrt nu * X) := by ring
    _ ≤ C3 * (Real.sqrt sigma)⁻¹ * delta * ((Cw + 1) * Real.sqrt sigma) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
    _ = C3 * (Cw + 1) * delta := by field_simp

end SuperdiffusionCLT.Section6
