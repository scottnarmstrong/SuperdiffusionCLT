/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Engine.Solutions
public import SuperdiffusionCLT.Section6.Lemma.RegEllipticityB
public import SuperdiffusionCLT.Section6.Lemma.WeakGrad
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.OneCubeBounds
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliDilationTransport

/-!
# Coarse-grained Caccioppoli inequality on an origin cube, two scales down

For a field elliptic on `□_n` with symmetric part `ν Id` and regularized ellipticity
`σ⁻¹ Λ_{1/4,1} + σ λ_{1/4,1}⁻¹ ≤ B`, every solution on `□_n` satisfies
`‖∇u‖_{L̲²(□_{n-2})} ≤ C (σ/ν)^{1/2} 3^{-n} ‖u - (u)_{□_n}‖_{L̲²(□_n)}`.

The route is the interior clause of the coarse Caccioppoli theorem of `CoarseGraining` for the
padded public family, at `s = t = 1/4`. The exponent of the public `Λ_s`, `λ_s` and of
`Θ_{s,t}` is `q = 1`, which is the exponent of the hypothesis. The public quantities are
bounded by the raw ones (`LambdaSq_one_rpow_half_le_old_pointwiseCoeffField` and its lower
analogue), so the raw hypothesis bounds `Λ_{1/4,1} ≤ Bσ` and `Θ ≤ B²`. If the raw `λ` were
`0`, the public bound `λ^{-1/2} ≤ λ_raw^{-1/2} = 0` would be false, so the hypothesis
forces `λ_raw > 0`: the junk value of the inverse is excluded.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem ea1_rpow_half_nonpos {x : ℝ} (hx : x ≤ 0) : Real.rpow x (1 / 2 : ℝ) = 0 := by
  rcases hx.lt_or_eq with h | h
  · rw [Real.rpow_eq_pow, Real.rpow_def_of_neg h]
    have : (1 / 2 : ℝ) * Real.pi = Real.pi / 2 := by ring
    rw [this, Real.cos_pi_div_two, mul_zero]
  · subst h
    simp

theorem ea1_rpow_neg_half_nonpos {x : ℝ} (hx : x ≤ 0) : Real.rpow x (-1 / 2 : ℝ) = 0 := by
  rcases hx.lt_or_eq with h | h
  · rw [Real.rpow_eq_pow, Real.rpow_def_of_neg h]
    have : (-1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) := by ring
    rw [this, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · subst h
    simp

theorem ea1_ch02_bounds [NeZero d] (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {sigma B : ℝ} (hs : 0 < sigma)
    (hB : sigma⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a +
        sigma * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤ B) :
    Book.Ch02.LambdaS Q (1 / 4) (HarmonicApprox.paddedFamily Q hEll h0 hle) ≤ B * sigma ∧
    Book.Ch02.ThetaRatio Q (1 / 4) (1 / 4) (HarmonicApprox.paddedFamily Q hEll h0 hle) ≤ B ^ 2 := by
  set F := HarmonicApprox.paddedFamily Q hEll h0 hle with hF
  have hq4 : (0 : ℝ) < 1 / 4 := by norm_num
  have hg : Book.Ch03.publicCoeffField Q F =ᵐ[volumeMeasureOn (cubeSet Q)] a :=
    HarmonicApprox.publicCoeffField_paddedFamily_ae_eq hEll h0 hle (subset_refl _)
  have eL : LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (Book.Ch03.publicCoeffField Q F) =
      LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a := l5_LambdaSq_congr_ae Q _ _ hg
  have el : lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (Book.Ch03.publicCoeffField Q F) =
      lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a := l5_lambdaSq_congr_ae Q _ _ hg
  have hU := Book.Ch02.LambdaSq_one_rpow_half_le_old_pointwiseCoeffField Q F hq4
  have hL := Book.Ch02.lambdaSq_one_rpow_neg_half_le_old_pointwiseCoeffField Q F hq4
  change _ ≤ Real.rpow (LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1)
    (Book.Ch03.publicCoeffField Q F)) _ at hU
  change _ ≤ Real.rpow (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1)
    (Book.Ch03.publicCoeffField Q F)) _ at hL
  rw [eL] at hU
  rw [el] at hL
  have hUc : 0 ≤ Book.Ch02.LambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F :=
    Book.Ch02.LambdaSq_nonneg Q F hq4 (by simp)
  have hLc : 0 < Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F :=
    Book.Ch02.lambdaSq_pos Q F hq4 (by simp)
  have hUp := Book.Ch02.LambdaSq_pos Q F hq4 (q := Book.Ch02.MultiscaleExponent.finite 1) (by simp)
  have hUr : 0 < LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a := by
    by_contra hneg
    have h0' := ea1_rpow_half_nonpos (not_lt.mp hneg)
    have : 0 < Real.rpow (Book.Ch02.LambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)
        (1 / 2 : ℝ) := Real.rpow_pos_of_pos hUp _
    linarith only [hU, h0', this]
  have hLr : 0 < lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a := by
    by_contra hneg
    have h0' := ea1_rpow_neg_half_nonpos (not_lt.mp hneg)
    have : 0 < Real.rpow (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)
        (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hLc _
    linarith only [hL, h0', this]
  have hUle : Book.Ch02.LambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F ≤
      LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a := by
    have := (Real.rpow_le_rpow_iff hUc hUr.le (by norm_num : (0 : ℝ) < 1 / 2)).mp hU
    exact this
  have hLle : (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹ ≤
      (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ := by
    have e1 : Real.rpow (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)
        (-1 / 2 : ℝ) = ((Book.Ch02.lambdaSq Q (1 / 4)
          (Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_eq_pow, Real.inv_rpow hLc.le, ← Real.rpow_neg hLc.le]
      congr 1
      ring
    have e2 : Real.rpow (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a) (-1 / 2 : ℝ) =
        ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_eq_pow, Real.inv_rpow hLr.le, ← Real.rpow_neg hLr.le]
      congr 1
      ring
    rw [e1, e2] at hL
    exact (Real.rpow_le_rpow_iff (inv_nonneg.mpr hLc.le) (inv_nonneg.mpr hLr.le)
      (by norm_num : (0 : ℝ) < 1 / 2)).mp hL
  have hσ' : 0 < sigma⁻¹ := inv_pos.mpr hs
  have hi1 : 0 ≤ sigma * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ :=
    mul_nonneg hs.le (inv_nonneg.mpr hLr.le)
  have hi2 : 0 ≤ sigma⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a :=
    mul_nonneg hσ'.le hUr.le
  have hA : LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a ≤ B * sigma := by
    have h1 : sigma⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a ≤ B :=
      by linarith only [hB, hi1]
    have := mul_le_mul_of_nonneg_left h1 hs.le
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at this
    linarith only [this]
  have hLB : (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤ B * sigma⁻¹ := by
    have h1 : sigma * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤ B :=
      by linarith only [hB, hi2]
    have := mul_le_mul_of_nonneg_left h1 hσ'.le
    rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul] at this
    linarith only [this]
  have hBnn : 0 ≤ B := by
    have : 0 ≤ sigma⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a +
        sigma * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ := add_nonneg hi2 hi1
    linarith only [hB, this]
  refine ⟨hUle.trans hA, ?_⟩
  unfold Book.Ch02.ThetaRatio Book.Ch02.LambdaS Book.Ch02.lambdaS
  rw [div_eq_mul_inv]
  calc _ ≤ (B * sigma) * (B * sigma⁻¹) :=
        mul_le_mul (hUle.trans hA) (hLle.trans hLB) (inv_nonneg.mpr hLc.le) (by positivity)
    _ = B ^ 2 := by field_simp


theorem ea1_cubeCenter_origin (m : ℤ) : cubeCenter (originCube d m) = 0 := by
  funext i
  simp [cubeCenter, originCube]

theorem ea1_core_eq (n : ℕ) (hn : 2 ≤ n) :
    Book.Ch03.caccioppoliCoreSet (originCube d (n : ℤ)) (cubeCenter (originCube d (n : ℤ))) =
      engCube d (n - 2) := by
  rw [ea1_cubeCenter_origin, Book.Ch03.caccioppoliCoreSet,
    Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube]
  have hs : (originCube d (n : ℤ)).scale - 2 = ((n - 2 : ℕ) : ℤ) := by
    simp [originCube]
    omega
  rw [hs]
  refine Set.inter_eq_right.mpr fun y hy => ?_
  rw [← Book.Ch03.openCubeAtScale_zero_eq_openCubeSet_originCube] at hy ⊢
  intro i
  refine lt_of_lt_of_le (hy i) ?_
  have : (3 : ℝ) ^ (((n - 2 : ℕ) : ℤ) : ℝ) ≤ (3 : ℝ) ^ (((n : ℕ) : ℤ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast Nat.sub_le n 2)
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
  linarith only [this]

theorem ea1_normalizedAverage_eq (Q : TriadicCube d) (f : Vec d → ℝ) :
    Book.Ch01.Legacy.normalizedAverage Q f = cubeAverage Q f := by
  rw [Book.Ch01.Legacy.normalizedAverage]


theorem ea1_engCube_subset (n : ℕ) (hn : 2 ≤ n) : engCube d (n - 2) ⊆ engCube d n := by
  rw [← ea1_core_eq n hn]
  exact Set.inter_subset_left

theorem ea1_cubeAverage_congr (Q : TriadicCube d) {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict (openCubeSet Q)] g) : cubeAverage Q f = cubeAverage Q g := by
  rw [← volumeAverage_cubeSet_eq_cubeAverage, ← volumeAverage_cubeSet_eq_cubeAverage,
    ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube,
    ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube]
  unfold volumeAverage
  rw [integral_congr_ae h]

theorem ea1_osc [NeZero d] {n : ℕ} {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a) (h0 : 0 < lam)
    (hle : lam ≤ Lam) {u : Vec d → ℝ}
    (hu2 : MemLp u 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (v : AHarmonicFunction a (engCube d n))
    (hv1 : v.toH1.toFun =ᵐ[volume.restrict (engCube d n)] u)
    (w : Book.Ch03.CubeSolution (originCube d (n : ℤ)) (HarmonicApprox.paddedFamily
      (originCube d (n : ℤ)) hEll h0 hle))
    (hw : w.toH1 = v.toH1) :
    Book.Ch03.interiorCaccioppoliParentOscillationL2Sq (originCube d (n : ℤ))
        (HarmonicApprox.paddedFamily (originCube d (n : ℤ)) hEll h0 hle) w =
      (cubeL2 n (fun x => u x - cubeAverage (originCube d (n : ℤ)) u)) ^ 2 := by
  have hwu : w.toH1.toFun =ᵐ[volume.restrict (engCube d n)] u := by rw [hw]; exact hv1
  unfold Book.Ch03.interiorCaccioppoliParentOscillationL2Sq
  rw [ea1_normalizedAverage_eq, ea1_cubeAverage_congr _ hwu]
  have hmem : MemLp (fun x => u x - cubeAverage (originCube d (n : ℤ)) u) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := hu2.sub (memLp_const _)
  rw [cubeL2, ← Book.Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq _ _ hmem]
  unfold Book.Ch03.normalizedL2SqOnSet Book.Ch03.normalizedSetAverage volumeAverage
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hwu] with x hx
  rw [hx]

theorem ea1_energy [NeZero d] {n : ℕ} {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a) (h0 : 0 < lam)
    (hle : lam ≤ Lam) {nu : ℝ}
    (hsym : ∀ x ∈ cubeSet (originCube d (n : ℤ)), symmPart (a x) = nu • (1 : Mat d))
    (hn : 2 ≤ n) {g : Vec d → Vec d}
    (v : AHarmonicFunction a (engCube d n))
    (hv2 : v.toH1.grad =ᵐ[volume.restrict (engCube d n)] g)
    (w : Book.Ch03.CubeSolution (originCube d (n : ℤ)) (HarmonicApprox.paddedFamily
      (originCube d (n : ℤ)) hEll h0 hle))
    (hw : w.toH1 = v.toH1)
    (hg2 : MemLp (fun x => engNorm (g x)) 2
      (normalizedCubeMeasure (originCube d ((n - 2 : ℕ) : ℤ)))) :
    Book.Ch03.interiorCaccioppoliCoreEnergy (originCube d (n : ℤ))
        (HarmonicApprox.paddedFamily (originCube d (n : ℤ)) hEll h0 hle)
        (cubeCenter (originCube d (n : ℤ))) w = nu * (cubeGradL2 (n - 2) g) ^ 2 := by
  have hwg : w.toH1.grad =ᵐ[volume.restrict (engCube d n)] g := by rw [hw]; exact hv2
  have hwg' : w.toH1.grad =ᵐ[volume.restrict (engCube d (n - 2))] g :=
    ae_restrict_of_ae_restrict_of_subset (ea1_engCube_subset n hn) hwg
  unfold Book.Ch03.interiorCaccioppoliCoreEnergy Book.Ch03.localizedCoeffEnergyValue
  rw [ea1_core_eq n hn]
  have hsq : (cubeGradL2 (n - 2) g) ^ 2 =
      Book.Ch03.normalizedL2SqOnSet (engCube d (n - 2)) (fun x => engNorm (g x)) := by
    rw [Book.Ch03.normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq _ _ hg2]
    rfl
  rw [hsq]
  unfold Book.Ch03.normalizedL2SqOnSet Book.Ch03.normalizedSetAverage volumeAverage
  have hint : ∫ x in engCube d (n - 2), vecDot (w.toH1.grad x) (matVecMul (symmPart
      (((HarmonicApprox.paddedFamily (originCube d (n : ℤ)) hEll h0 hle).coeffOn
        (originCube d (n : ℤ))).toCoeffField x)) (w.toH1.grad x)) ∂volume =
      ∫ x in engCube d (n - 2), nu * engNorm (g x) ^ 2 ∂volume := by
    have hmem : ∀ᵐ x ∂ volume.restrict (engCube d (n - 2)), x ∈ engCube d (n - 2) :=
      ae_restrict_mem (measurableSet_openCubeSet _)
    refine integral_congr_ae ?_
    filter_upwards [hwg', hmem] with x hx hxm
    have hxc : x ∈ cubeSet (originCube d (n : ℤ)) :=
      openCubeSet_subset_cubeSet _ (ea1_engCube_subset n hn hxm)
    change vecDot (w.toH1.grad x) (matVecMul (symmPart (HarmonicApprox.padField
      (originCube d (n : ℤ)) lam a x)) (w.toH1.grad x)) = _
    rw [HarmonicApprox.padField_apply_of_mem hxc, hsym x hxc, hx]
    show vecDot (g x) (matVecMul (scalarMatrix nu) (g x)) = _
    rw [matVecMul_scalarMatrix, vecDot_smul_right]
    unfold engNorm
    rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    rfl
  rw [hint, integral_const_mul]
  ring

/-- **E-A1 (coarse-grained Caccioppoli on an origin cube, two scales down)**,
`e.sharp.Cone.caccioppoli`. -/
theorem eng_cacc_cube (d : ℕ) [NeZero d] (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n : ℕ) {lam Lam : ℝ} {a : CoeffField d} {sigma nu : ℝ}, 2 ≤ n →
        IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ))) a → 0 < lam → lam ≤ Lam →
        0 < sigma → 0 < nu →
        (∀ x ∈ cubeSet (originCube d (n : ℤ)), symmPart (a x) = nu • (1 : Mat d)) →
        sigma⁻¹ * LambdaSq (originCube d (n : ℤ)) (1 / 4) (MultiscaleExponent.finite 1) a +
            sigma * (lambdaSq (originCube d (n : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1) a)⁻¹ ≤ B →
        ∀ (u : Vec d → ℝ) (g : Vec d → Vec d), IsSolOn a (engCube d n) u g →
          cubeGradL2 (n - 2) g ≤ C * Real.sqrt (sigma / nu) * cubeFlat n u := by
  obtain ⟨C0, hC0, -, hint⟩ := (Book.Ch03.coarseCaccioppoliTheory d).exists_constant
  set Kc : ℝ := Real.rpow (C0 / (1 - 1 / 4 - 1 / 4)) (2 + 4 * (1 / 4) / (1 - 1 / 4 - 1 / 4)) *
    Real.rpow (1 / 4) (-(2 * (1 / 4) / (1 - 1 / 4 - 1 / 4))) with hKc
  have hKnn : 0 ≤ Kc := by
    have h1 : 0 < C0 / (1 - 1 / 4 - 1 / 4) := div_pos hC0 (by norm_num)
    exact mul_nonneg (Real.rpow_nonneg h1.le _) (Real.rpow_nonneg (by norm_num) _)
  have hB0 : 0 ≤ B := by linarith only [hB]
  refine ⟨max 1 (Real.sqrt Kc * B), le_max_left _ _, ?_⟩
  intro n lam Lam a sigma nu hn hEll h0 hle hs hnu hsym hBd u g hsol
  have hEll' := hEll
  set Q := originCube d (n : ℤ) with hQ
  obtain ⟨hLam, hTheta⟩ := ea1_ch02_bounds Q hEll h0 hle hs hBd
  obtain ⟨hu2, hg2⟩ := hsol.memLp
  have hsol' : IsSolOn a (engCube d (n - 2)) u g :=
    hsol.mono (isOpen_openCubeSet _) (isOpen_openCubeSet _) (ea1_engCube_subset n hn)
      (volume_openCubeSet_lt_top _).ne
      ⟨lam, Lam, hEll.mono (measurableSet_openCubeSet _)
        ((ea1_engCube_subset n hn).trans (openCubeSet_subset_cubeSet Q))⟩
  obtain ⟨-, hg2'⟩ := hsol'.memLp
  obtain ⟨v, hv1, hv2⟩ := hsol
  set F := HarmonicApprox.paddedFamily Q hEll h0 hle with hF
  obtain ⟨w, hw⟩ := WeakGrad.weakGrad_exists_solution Q hEll h0 hle v
  have key := hint (Q := Q) (a := F) (s := 1 / 4) (t := 1 / 4) w (by norm_num) (by norm_num)
    (by norm_num)
  have hE := ea1_energy hEll h0 hle hsym hn v hv2 w hw hg2'
  have hO := ea1_osc hEll h0 hle hu2 v hv1 w hw
  unfold Book.Ch03.interiorCaccioppoliRHS at key
  rw [hE, hO] at key
  have hq4 : (0 : ℝ) < 1 / 4 := by norm_num
  have hLnn : 0 ≤ Book.Ch02.LambdaS Q (1 / 4) F :=
    Book.Ch02.LambdaSq_nonneg Q F hq4 (by simp)
  have hlpos : 0 < Book.Ch02.lambdaS Q (1 / 4) F := Book.Ch02.lambdaSq_pos Q F hq4 (by simp)
  have hThnn : 0 ≤ Book.Ch02.ThetaRatio Q (1 / 4) (1 / 4) F := div_nonneg hLnn hlpos.le
  have hThr : Real.rpow (Book.Ch02.ThetaRatio Q (1 / 4) (1 / 4) F) (1 / 4 / (1 - 1 / 4 - 1 / 4)) ≤
      B := by
    have he : (1 / 4 / (1 - 1 / 4 - 1 / 4) : ℝ) = 1 / 2 := by norm_num
    rw [he, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
    calc Real.sqrt _ ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt hTheta
      _ = B := Real.sqrt_sq hB0
  have h3 : Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) = ((3 : ℝ)⁻¹ ^ n) ^ 2 := by
    have hQs : (((Q.scale : ℤ)) : ℝ) = (n : ℝ) := by simp [hQ, originCube]
    rw [hQs, Real.rpow_eq_pow, show (-2 * (n : ℝ)) = -((2 * n : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [inv_pow, inv_pow, ← pow_mul, mul_comm n 2]
  have hpref : Book.Ch03.caccioppoliPrefactor C0 Q F (1 / 4) (1 / 4) ≤
      Kc * B * (B * sigma) * ((3 : ℝ)⁻¹ ^ n) ^ 2 := by
    unfold Book.Ch03.caccioppoliPrefactor
    rw [h3, ← hKc]
    have hB' : 0 ≤ Real.rpow (Book.Ch02.ThetaRatio Q (1 / 4) (1 / 4) F)
        (1 / 4 / (1 - 1 / 4 - 1 / 4)) := Real.rpow_nonneg hThnn _
    have e1 : Kc * Real.rpow (Book.Ch02.ThetaRatio Q (1 / 4) (1 / 4) F)
        (1 / 4 / (1 - 1 / 4 - 1 / 4)) * Book.Ch02.LambdaS Q (1 / 4) F ≤
        Kc * B * (B * sigma) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hThr hKnn) hLam hLnn (by positivity)
    have := mul_le_mul_of_nonneg_right e1 (sq_nonneg ((3 : ℝ)⁻¹ ^ n))
    rw [hKc] at this ⊢
    linarith only [this]
  have hL0 : 0 ≤ cubeL2 n (fun x => u x - cubeAverage Q u) := by
    unfold cubeL2 cubeLpNorm
    exact ENNReal.toReal_nonneg
  have hG0 : 0 ≤ cubeGradL2 (n - 2) g := by
    unfold cubeGradL2 cubeL2 cubeLpNorm
    exact ENNReal.toReal_nonneg
  have hfl : cubeFlat n u = (3 : ℝ)⁻¹ ^ n * cubeL2 n (fun x => u x - cubeAverage Q u) := rfl
  have hfl0 : 0 ≤ cubeFlat n u := by rw [hfl]; positivity
  have h1 : nu * cubeGradL2 (n - 2) g ^ 2 ≤ Kc * B ^ 2 * sigma * cubeFlat n u ^ 2 := by
    have := key.trans (mul_le_mul_of_nonneg_right hpref (sq_nonneg _))
    rw [hfl]
    calc _ ≤ _ := this
      _ = _ := by ring
  have h2 : cubeGradL2 (n - 2) g ^ 2 ≤ Kc * B ^ 2 * (sigma / nu) * cubeFlat n u ^ 2 := by
    have : cubeGradL2 (n - 2) g ^ 2 ≤ Kc * B ^ 2 * sigma * cubeFlat n u ^ 2 / nu := by
      rw [le_div_iff₀ hnu]
      linarith only [h1, mul_comm nu (cubeGradL2 (n - 2) g ^ 2)]
    calc _ ≤ _ := this
      _ = _ := by ring
  set M := Real.sqrt Kc * B * Real.sqrt (sigma / nu) * cubeFlat n u with hM
  have hM2 : M ^ 2 = Kc * B ^ 2 * (sigma / nu) * cubeFlat n u ^ 2 := by
    rw [hM]
    have hsn : 0 ≤ sigma / nu := div_nonneg hs.le hnu.le
    calc _ = (Real.sqrt Kc) ^ 2 * B ^ 2 * (Real.sqrt (sigma / nu)) ^ 2 * cubeFlat n u ^ 2 := by
          ring
      _ = _ := by rw [Real.sq_sqrt hKnn, Real.sq_sqrt hsn]
  have hM0 : 0 ≤ M := by positivity
  have hGM : cubeGradL2 (n - 2) g ≤ M :=
    (pow_le_pow_iff_left₀ hG0 hM0 (by norm_num : (2 : ℕ) ≠ 0)).mp (by rw [hM2]; exact h2)
  calc cubeGradL2 (n - 2) g ≤ M := hGM
    _ ≤ max 1 (Real.sqrt Kc * B) * Real.sqrt (sigma / nu) * cubeFlat n u := by
        rw [hM]
        gcongr
        exact le_max_right _ _

/-- Witness: for the identity field on `□_2` the hypotheses of `eng_cacc_cube` hold, for a
suitable `B`, with the zero solution. -/
example (d : ℕ) [NeZero d] : ∃ B : ℝ, 1 ≤ B ∧
    IsEllipticFieldOn 1 1 (cubeSet (originCube d ((2 : ℕ) : ℤ))) (constantCoeffField (1 : Mat d)) ∧
    (∀ x ∈ cubeSet (originCube d ((2 : ℕ) : ℤ)),
      symmPart (constantCoeffField (1 : Mat d) x) = (1 : ℝ) • (1 : Mat d)) ∧
    (1 : ℝ)⁻¹ * LambdaSq (originCube d ((2 : ℕ) : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
        (constantCoeffField (1 : Mat d)) +
      1 * (lambdaSq (originCube d ((2 : ℕ) : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
        (constantCoeffField (1 : Mat d)))⁻¹ ≤ B ∧
    IsSolOn (constantCoeffField (1 : Mat d)) (engCube d 2) (fun _ => 0) (fun _ => 0) := by
  refine ⟨max 1 ((1 : ℝ)⁻¹ * LambdaSq (originCube d ((2 : ℕ) : ℤ)) (1 / 4)
      (MultiscaleExponent.finite 1) (constantCoeffField (1 : Mat d)) +
    1 * (lambdaSq (originCube d ((2 : ℕ) : ℤ)) (1 / 4) (MultiscaleExponent.finite 1)
      (constantCoeffField (1 : Mat d)))⁻¹), le_max_left _ _, regEllipticity_witness _, ?_,
    le_max_right _ _, ⟨⟨0, isAHarmonicGradient_zero⟩, Filter.EventuallyEq.rfl,
      Filter.EventuallyEq.rfl⟩⟩
  intro x _
  show symmPart (1 : Mat d) = _
  ext i j
  by_cases h : i = j
  · subst h
    simp [symmPart]
  · simp [symmPart, h, Ne.symm h]

end SuperdiffusionCLT.Section6

