/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepSchauderInteriorHess
public import SuperdiffusionCLT.Section8.Common.Support.NormalizedL2

/-!
# Harmonic functions on a cube: Hessian bound and Taylor expansion at the centre

For a function `v` whose Euclidean avatar is harmonic on the open cube `□_k`, the interior
second-derivative estimate of the Schauder development, applied on balls inscribed in `□_k`
around the points of `□_{k-1}`, bounds `D²v` on the closed cube of half-side `3^{k-1}/2` by
`C 3^{-2k} ‖v - c‖_{L̲²(□_k)}` with `C` dimensional.  Taylor's formula at the origin then gives
the affine approximation with a quadratic remainder.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open MeasureTheory Homogenization InnerProductSpace
open SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder
open SuperdiffusionCLT.Section8.Common.Support (normalizedL2On)
open Homogenization.Book.Ch01 (meanSquareDeviationOn)

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Taylor's formula to second order along a convex set, from a bound on the Hessian. -/
theorem eh_taylor {u : 𝔼 → ℝ} {S : Set 𝔼} {H : ℝ} (hS : Convex ℝ S) (h0 : (0 : 𝔼) ∈ S)
    (hC : ∀ q ∈ S, ContDiffAt ℝ 2 u q)
    (hH : ∀ q ∈ S, ‖fderiv ℝ (fderiv ℝ u) q‖ ≤ H) :
    ∀ y ∈ S, |u y - u 0 - fderiv ℝ u 0 y| ≤ H * ‖y‖ ^ 2 := by
  intro y hy
  have hH0 : 0 ≤ H := (norm_nonneg (fderiv ℝ (fderiv ℝ u) 0)).trans (hH 0 h0)
  have hdu : ∀ q ∈ S, DifferentiableAt ℝ u q :=
    fun q hq => (hC q hq).differentiableAt (by norm_num)
  have hddu : ∀ q ∈ S, DifferentiableAt ℝ (fderiv ℝ u) q := by
    intro q hq
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) q := by
      simpa using (hC q hq).fderiv_right (m := 1) (by norm_num)
    exact h1.differentiableAt (by simp)
  have hstep : ∀ z ∈ S, ‖fderiv ℝ u z - fderiv ℝ u 0‖ ≤ H * ‖z‖ := by
    intro z hz
    simpa using hS.norm_image_sub_le_of_norm_fderiv_le hddu hH h0 hz
  set T : Set 𝔼 := S ∩ Metric.closedBall 0 ‖y‖ with hT
  have hTc : Convex ℝ T := hS.inter (convex_closedBall _ _)
  have h0T : (0 : 𝔼) ∈ T := ⟨h0, by simp⟩
  have hyT : y ∈ T := ⟨hy, by simp⟩
  have hder : ∀ z ∈ T, HasFDerivWithinAt (fun w => u w - fderiv ℝ u 0 w)
      (fderiv ℝ u z - fderiv ℝ u 0) T z := fun z hz =>
    ((hdu z hz.1).hasFDerivAt.sub (fderiv ℝ u 0).hasFDerivAt).hasFDerivWithinAt
  have hbd : ∀ z ∈ T, ‖fderiv ℝ u z - fderiv ℝ u 0‖ ≤ H * ‖y‖ := by
    intro z hz
    have hzn : ‖z‖ ≤ ‖y‖ := by simpa using hz.2
    exact (hstep z hz.1).trans (mul_le_mul_of_nonneg_left hzn hH0)
  have h := hTc.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd h0T hyT
  simp only [map_zero, sub_zero, Real.norm_eq_abs] at h
  calc |u y - u 0 - fderiv ℝ u 0 y| = |u y - fderiv ℝ u 0 y - u 0| := by ring_nf
    _ ≤ H * ‖y‖ * ‖y‖ := h
    _ = H * ‖y‖ ^ 2 := by ring

/-- A ball of radius `3^{k-1}` around a point of the closed cube of half-side `3^{k-1}/2`
lies in `□_k`. -/
theorem eh_ball_subset (k : ℕ) (hk : 1 ≤ k) (q : Vec d) (hq : ∀ i, |q i| ≤ (3 : ℝ) ^ (k - 1) / 2) :
    Metric.ball (toEuc q) ((3 : ℝ) ^ (k - 1)) ⊆ toEuc '' engCube d k := by
  intro z hz
  refine ⟨toEuc.symm z, ?_, by simp⟩
  have h3 : (3 : ℝ) ^ (k : ℤ) = 3 * (3 : ℝ) ^ (k - 1) := by
    rw [zpow_natCast, ← pow_succ']
    congr 1
    omega
  show toEuc.symm z ∈ openCubeSet (originCube d (k : ℤ))
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hdist : |z i - q i| < (3 : ℝ) ^ (k - 1) := by
    have h1 : ‖z i - toEuc q i‖ ≤ ‖z - toEuc q‖ := by
      have := PiLp.norm_apply_le (z - toEuc q) i
      simpa using this
    have h2 : ‖z - toEuc q‖ < (3 : ℝ) ^ (k - 1) := by simpa [dist_eq_norm] using hz
    have h3' : |z i - q i| ≤ ‖z - toEuc q‖ := by simpa [Real.norm_eq_abs] using h1
    exact lt_of_le_of_lt h3' h2
  have hqi := abs_le.1 (hq i)
  have hdi := abs_lt.1 hdist
  rw [h3]
  have hzi : (toEuc.symm z) i = z i := rfl
  rw [hzi]
  constructor <;> linarith only [hqi.1, hqi.2, hdi.1, hdi.2]

/-- Volume of a Euclidean ball in the coordinate carrier. -/
theorem eh_volume_euclideanBall [NeZero d] (q : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall q r)).toReal
      = r ^ d * (volume (Metric.ball (0 : 𝔼) 1)).toReal := by
  have hpre : toEuc ⁻¹' (Metric.ball (toEuc q) r) = euclideanBall q r := by
    simpa using preimage_ball_toEuc (toEuc q) hr
  have hvol : volume (euclideanBall q r) = volume (Metric.ball (toEuc q) r) := by
    rw [← hpre, (measurePreserving_toEuc d).measure_preimage
      measurableSet_ball.nullMeasurableSet]
  rw [hvol, Measure.addHaar_ball (volume : Measure 𝔼) (toEuc q) hr.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _), finrank_euclideanSpace_fin]

theorem eh_unitBall_pos [NeZero d] : 0 < (volume (Metric.ball (0 : 𝔼) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne

/-- The cube `□_k` has volume `(3^k)^d`. -/
theorem eh_volume_engCube (k : ℕ) : (volume (engCube d k)).toReal = ((3 : ℝ) ^ k) ^ d := by
  show (volume (openCubeSet (originCube d (k : ℤ)))).toReal = _
  rw [volume_openCubeSet_toReal]
  simp [cubeVolume, cubeScaleFactor, originCube, zpow_natCast]

theorem eh_euclideanBall_subset (k : ℕ) (hk : 1 ≤ k) (q : Vec d)
    (hq : ∀ i, |q i| ≤ (3 : ℝ) ^ (k - 1) / 2) {r : ℝ} (hr : 0 < r)
    (hrR : r ≤ (3 : ℝ) ^ (k - 1)) : euclideanBall q r ⊆ engCube d k := by
  intro y hy
  have hy' : toEuc y ∈ Metric.ball (toEuc q) r := (mem_euclideanBall_toEuc_iff y q hr).2 hy
  obtain ⟨x, hx, hxy⟩ := eh_ball_subset k hk q hq (Metric.ball_subset_ball hrR hy')
  have : x = y := toEuc.injective hxy
  rwa [← this]

/-- The pointwise bound for the Hessian of a harmonic function on the closed cube of half-side
`3^{k-1}/2`, in terms of the normalized `L²` deviation on `□_k`. -/
theorem eh_hessian_inner (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (v : Vec d → ℝ) (c : ℝ),
      HarmonicOnNhd (v ∘ toEuc.symm) (toEuc '' engCube d k) →
      IntegrableOn (fun y => (v y - c) ^ 2) (engCube d k) volume →
      ∀ q : Vec d, (∀ i, |q i| ≤ (3 : ℝ) ^ (k - 1) / 2) →
        ‖fderiv ℝ (fderiv ℝ (v ∘ toEuc.symm)) (toEuc q)‖ ≤
          C * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ *
            normalizedL2On (engCube d k) (fun y => v y - c) := by
  obtain ⟨C0, hC0, hC⟩ := interiorSecondDerivEstimateL2_ball d
  set ω : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal with hω
  have hω0 : 0 < ω := eh_unitBall_pos
  refine ⟨36 * C0 * Real.sqrt (6 ^ d / ω), by positivity, ?_⟩
  intro k hk v c hh hint q hq
  set R : ℝ := (3 : ℝ) ^ (k - 1) with hRdef
  have hR : 0 < R := by positivity
  have hk3 : (3 : ℝ) ^ k = 3 * R := by
    rw [hRdef, ← pow_succ']
    congr 1
    omega
  have hhalf : 0 < R / 2 := by positivity
  have hball := eh_ball_subset k hk q hq
  have hharm : HarmonicOnNhd (v ∘ toEuc.symm) (Metric.ball (toEuc q) R) := hh.mono hball
  have hcore := hC (v ∘ toEuc.symm) (toEuc q) (R := R) (r := R / 2) c hhalf
    (by linarith only [hR]) hharm (toEuc q) (Metric.mem_ball_self (by positivity))
  rw [comp_toEuc_symm_toEuc, ContinuousLinearEquiv.symm_apply_apply] at hcore
  set B : Set (Vec d) := euclideanBall q (R / 2) with hB
  have hBsub : B ⊆ engCube d k :=
    eh_euclideanBall_subset k hk q hq hhalf (by linarith only [hR])
  have hVb : (volume B).toReal = (R / 2) ^ d * ω := eh_volume_euclideanBall q hhalf
  have hVc : (volume (engCube d k)).toReal = (3 * R) ^ d := by
    rw [eh_volume_engCube, hk3]
  have hVbpos : 0 < (volume B).toReal := by rw [hVb]; positivity
  have hVcpos : 0 < (volume (engCube d k)).toReal := by rw [hVc]; positivity
  have hmono : ∫ y in B, (v y - c) ^ 2 ≤ ∫ y in engCube d k, (v y - c) ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => sq_nonneg _)
      (LE.le.eventuallySubset hBsub)
  have hmsd : meanSquareDeviationOn B v c
      ≤ ((3 * R) ^ d / ((R / 2) ^ d * ω)) *
          volumeAverage (engCube d k) (fun y => (v y - c) ^ 2) := by
    unfold meanSquareDeviationOn volumeAverage
    rw [hVb, hVc]
    have hpos1 : (0 : ℝ) < (R / 2) ^ d * ω := by positivity
    have hpos2 : (0 : ℝ) < (3 * R) ^ d := by positivity
    calc ((R / 2) ^ d * ω)⁻¹ * ∫ y in B, (v y - c) ^ 2
        ≤ ((R / 2) ^ d * ω)⁻¹ * ∫ y in engCube d k, (v y - c) ^ 2 :=
          mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hpos1.le)
      _ = ((3 * R) ^ d / ((R / 2) ^ d * ω)) *
            (((3 * R) ^ d)⁻¹ * ∫ y in engCube d k, (v y - c) ^ 2) := by
          field_simp
  have hratio : (3 * R) ^ d / ((R / 2) ^ d * ω) = 6 ^ d / ω := by
    have h6 : (3 * R) ^ d = 6 ^ d * (R / 2) ^ d := by
      rw [← mul_pow]
      congr 1
      ring
    rw [h6]
    have : (R / 2) ^ d ≠ 0 := by positivity
    field_simp
  rw [hratio] at hmsd
  have hsq : Real.sqrt (meanSquareDeviationOn B v c)
      ≤ Real.sqrt (6 ^ d / ω) * normalizedL2On (engCube d k) (fun y => v y - c) := by
    refine (Real.sqrt_le_sqrt hmsd).trans ?_
    rw [Real.sqrt_mul (by positivity)]
    rfl
  have hcoef : (R / 2)⁻¹ * (R / 2)⁻¹ = 36 * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ := by
    rw [hk3]
    field_simp
    ring
  have hC0' : 0 ≤ C0 * (R / 2)⁻¹ * (R / 2)⁻¹ := by positivity
  calc _ ≤ C0 * (R / 2)⁻¹ * (R / 2)⁻¹ * Real.sqrt (meanSquareDeviationOn B v c) := hcore
    _ ≤ C0 * (R / 2)⁻¹ * (R / 2)⁻¹ *
          (Real.sqrt (6 ^ d / ω) * normalizedL2On (engCube d k) (fun y => v y - c)) :=
        mul_le_mul_of_nonneg_left hsq hC0'
    _ = _ := by
        rw [mul_assoc C0, hcoef]
        ring

theorem eh_norm_sq_toEuc (y : Vec d) : ‖(toEuc y : 𝔼)‖ ^ 2 = vecNormSq y := by
  rw [EuclideanSpace.norm_sq_eq, vecNormSq, vecDot]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ‖(toEuc y : 𝔼) i‖ = |y i| := rfl
  rw [this, sq_abs, sq]

theorem eh_sum_smul_basisVec (y : Vec d) : ∑ i : Fin d, y i • (basisVec i : Vec d) = y := by
  funext j
  simp [basisVec_apply, Finset.sum_apply]

/-- The derivative at the origin of the Euclidean avatar, as a coordinate vector. -/
noncomputable def ehSlope (u : 𝔼 → ℝ) : Vec d :=
  fun i => fderiv ℝ u 0 (toEuc (basisVec i))

theorem eh_fderiv_apply (u : 𝔼 → ℝ) (y : Vec d) :
    fderiv ℝ u 0 (toEuc y) = vecDot (ehSlope u) y := by
  have hy : toEuc y = ∑ i, y i • toEuc (basisVec i) := by
    conv_lhs => rw [← eh_sum_smul_basisVec y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [hy, map_sum, vecDot]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, ehSlope, mul_comm]

/-- Taylor expansion of a harmonic function on the cube at the origin. -/
theorem eh_taylor_vec (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (v : Vec d → ℝ) (c : ℝ),
      HarmonicOnNhd (v ∘ toEuc.symm) (toEuc '' engCube d k) →
      IntegrableOn (fun y => (v y - c) ^ 2) (engCube d k) volume →
      ∃ p : Vec d, ∀ y : Vec d, (∀ i, |y i| ≤ (3 : ℝ) ^ (k - 1) / 2) →
        |v y - v 0 - vecDot p y| ≤
          C * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ *
            normalizedL2On (engCube d k) (fun y => v y - c) * vecNormSq y := by
  obtain ⟨C, hC0, hC⟩ := eh_hessian_inner d
  refine ⟨C, hC0, ?_⟩
  intro k hk v c hh hint
  have hC' := hC k hk v c hh hint
  obtain ⟨u, hu⟩ : ∃ u : (EuclideanSpace ℝ (Fin d)) → ℝ, u = v ∘ toEuc.symm := ⟨_, rfl⟩
  rw [← hu] at hh hC'
  set s : ℝ := (3 : ℝ) ^ (k - 1) / 2 with hs
  set T : Set (Vec d) := Set.pi Set.univ (fun _ => Set.Icc (-s) s) with hT
  have hTmem : ∀ y, y ∈ T ↔ ∀ i, |y i| ≤ s := by
    intro y
    simp only [hT, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
  have hTc : Convex ℝ T := convex_pi fun _ _ => convex_Icc _ _
  set S : Set (EuclideanSpace ℝ (Fin d)) := toEuc '' T with hS
  have hSc : Convex ℝ S := by
    have : S = toEuc.symm ⁻¹' T := ContinuousLinearEquiv.image_eq_preimage_symm _ _
    rw [this]
    exact hTc.linear_preimage (toEuc (d := d)).symm.toLinearEquiv.toLinearMap
  have h0 : (0 : (EuclideanSpace ℝ (Fin d))) ∈ S := ⟨0, (hTmem 0).2 (fun i => by
    simp only [Pi.zero_apply, abs_zero]; positivity), by simp⟩
  have hmemS : ∀ y ∈ T, toEuc y ∈ toEuc '' engCube d k := fun y hy =>
    eh_ball_subset k hk y ((hTmem y).1 hy) (Metric.mem_ball_self (by positivity))
  set N : ℝ := normalizedL2On (engCube d k) (fun y => v y - c) with hN
  have hcd : ∀ q ∈ S, ContDiffAt ℝ 2 u q := by
    intro q hq
    obtain ⟨y, hy, hyq⟩ := hq
    rw [← hyq]
    exact (hh _ (hmemS y hy)).1
  have hbd : ∀ q ∈ S, ‖fderiv ℝ (fderiv ℝ u) q‖ ≤
      C * ((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹ * N := by
    intro q hq
    obtain ⟨y, hy, hyq⟩ := hq
    rw [← hyq]
    exact hC' y ((hTmem y).1 hy)
  have htay := eh_taylor hSc h0 hcd hbd
  refine ⟨ehSlope u, fun y hy => ?_⟩
  have h := htay (toEuc y) ⟨y, (hTmem y).2 hy, rfl⟩
  have e1 : u (toEuc y) = v y := by simp [hu]
  have e0 : u 0 = v 0 := by simp [hu]
  rw [e1, e0, eh_fderiv_apply, eh_norm_sq_toEuc] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end SuperdiffusionCLT.Section6
