/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.AffineSlopeB
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine functions, slopes and the Euclidean length

The Euclidean length `engNorm` satisfies the triangle inequality and Cauchy-Schwarz; the origin
cube `□_n` has the moments `⨍ xᵢ = 0`, `⨍ xᵢ xⱼ = δᵢⱼ 3^{2n}/12`, so that `affSlope n` recovers the
gradient of an affine function, is additive, and gives the best affine approximation of an
`L²(□_n)` function.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem abs_vecDot_le_engNorm (x y : Vec d) : |vecDot x y| ≤ engNorm x * engNorm y := by
  unfold engNorm
  rw [← Real.sqrt_mul (vecNormSq_nonneg x)]
  exact Real.abs_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq x y)

theorem engNorm_nonneg (x : Vec d) : 0 ≤ engNorm x := Real.sqrt_nonneg _

theorem engNorm_sq (x : Vec d) : engNorm x ^ 2 = vecNormSq x :=
  Real.sq_sqrt (vecNormSq_nonneg x)

theorem engNorm_smul (c : ℝ) (x : Vec d) : engNorm (c • x) = |c| * engNorm x := by
  unfold engNorm
  rw [vecNormSq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem e0c_vecNormSq_add (x y : Vec d) :
    vecNormSq (x + y) = vecNormSq x + 2 * vecDot x y + vecNormSq y := by
  have h : ∀ i, (x + y) i * (x + y) i = x i * x i + 2 * (x i * y i) + y i * y i := by
    intro i
    simp only [Pi.add_apply]
    ring
  simp only [vecNormSq, vecDot, h, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem engNorm_add_le (x y : Vec d) : engNorm (x + y) ≤ engNorm x + engNorm y := by
  have h1 := abs_vecDot_le_engNorm x y
  have h2 := le_abs_self (vecDot x y)
  apply le_of_sq_le_sq _ (add_nonneg (engNorm_nonneg x) (engNorm_nonneg y))
  rw [engNorm_sq, e0c_vecNormSq_add, add_sq, engNorm_sq, engNorm_sq]
  nlinarith only [h1, h2]

theorem e0c_engNorm_eq_zero {x : Vec d} (h : engNorm x = 0) : x = 0 := by
  have : vecNormSq x = 0 := by rw [← engNorm_sq, h]; norm_num
  exact vecNormSq_eq_zero this

theorem engNorm_bijective_of_close (T : Vec d →ₗ[ℝ] Vec d)
    (hT : ∀ e : Vec d, engNorm (T e - e) ≤ 1 / 2 * engNorm e) :
    Function.Bijective T ∧ ∀ e : Vec d, engNorm e ≤ 2 * engNorm (T e) := by
  have hlow : ∀ e : Vec d, engNorm e ≤ 2 * engNorm (T e) := by
    intro e
    have h1 : e = T e + (-1 : ℝ) • (T e - e) := by
      simp only [neg_smul, one_smul, sub_eq_add_neg, neg_add_rev, neg_neg]
      abel
    have h2 := engNorm_add_le (T e) ((-1 : ℝ) • (T e - e))
    rw [← h1, engNorm_smul] at h2
    have h3 := hT e
    simp only [abs_neg, abs_one, one_mul] at h2
    linarith only [h2, h3]
  refine ⟨?_, hlow⟩
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    have := hlow e
    rw [he] at this
    have h0 : engNorm (0 : Vec d) = 0 := by simp [engNorm, vecNormSq, vecDot]
    rw [h0] at this
    exact e0c_engNorm_eq_zero (le_antisymm (by linarith only [this]) (engNorm_nonneg e))
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

theorem engNorm_bijective_of_lower (T : Vec d →ₗ[ℝ] Vec d) {c : ℝ} (hc : 0 < c)
    (hT : ∀ e : Vec d, c * engNorm e ≤ engNorm (T e)) : Function.Bijective T := by
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    have := hT e
    rw [he] at this
    have h0 : engNorm (0 : Vec d) = 0 := by simp [engNorm, vecNormSq, vecDot]
    rw [h0] at this
    have : engNorm e ≤ 0 := by nlinarith only [this, hc]
    exact e0c_engNorm_eq_zero (le_antisymm this (engNorm_nonneg e))
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩


theorem e0c_dist_nonneg (s p : Vec d) :
    0 ≤ vecNormSq s - 2 * vecDot s p + vecNormSq p := by
  unfold vecNormSq vecDot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_nonneg fun i _ => by nlinarith only [sq_nonneg (s i - p i)]

theorem e0c_inv_mul (n : ℕ) : (3 : ℝ) ^ n * ((3 : ℝ)⁻¹) ^ n = 1 := by
  rw [← mul_pow]
  simp

theorem cubeFlat_vecDot [NeZero d] (n : ℕ) (p : Vec d) :
    cubeFlat n (fun x => vecDot p x) = engNorm p / (2 * Real.sqrt 3) := by
  have hl := e0c_memLp n (e0c_continuous_vecDot p)
  have havg : cubeAverage (originCube d (n : ℤ)) (fun x => vecDot p x) = 0 := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, e0c_int_ell]
  have hsq := e0c_cubeL2_sq n hl
  have hint : ∫ x, vecDot p x ^ 2 ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ((3 : ℝ) ^ n) ^ 2 / 12 * vecNormSq p := by
    have h := e0c_int_ell_ell n p p
    simp only [← sq] at h
    exact h
  have hX : 0 ≤ cubeL2 n (fun x => vecDot p x) := ENNReal.toReal_nonneg
  have hflat : cubeFlat n (fun x => vecDot p x) =
      ((3 : ℝ)⁻¹) ^ n * cubeL2 n (fun x => vecDot p x) := by
    unfold cubeFlat
    rw [havg]
    simp only [sub_zero]
  rw [hflat]
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hu := e0c_inv_mul n
  have hT : 0 ≤ ((3 : ℝ)⁻¹) ^ n * cubeL2 n (fun x => vecDot p x) := by positivity
  have hR : 0 ≤ engNorm p / (2 * Real.sqrt 3) := div_nonneg (engNorm_nonneg p) (by positivity)
  refine (sq_eq_sq₀ hT hR).1 ?_
  rw [mul_pow, hsq, hint, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    engNorm_sq]
  calc (((3 : ℝ)⁻¹) ^ n) ^ 2 * (((3 : ℝ) ^ n) ^ 2 / 12 * vecNormSq p)
      = ((3 : ℝ) ^ n * ((3 : ℝ)⁻¹) ^ n) ^ 2 * vecNormSq p / 12 := by ring
    _ = vecNormSq p / (2 ^ 2 * 3) := by rw [hu]; ring

theorem affSlope_affine [NeZero d] (n : ℕ) (c : ℝ) (p : Vec d) :
    affSlope n (fun x => c + vecDot p x) = p := by
  funext i
  have h := e0c_slope_apply n (fun x => c + vecDot p x) i
  have hA : ((3 : ℝ) ^ n) ^ 2 / 12 ≠ 0 := by positivity
  refine mul_left_cancel₀ hA ?_
  rw [h]
  have hpt : ∀ x : Vec d, (c + vecDot p x) * x i = c * x i + vecDot p x * x i := fun x => by ring
  simp only [hpt]
  rw [integral_add (f := fun x => c * x i) (g := fun x => vecDot p x * x i)
    ((e0c_integrable n (continuous_apply i)).const_mul c)
    (e0c_integrable n ((e0c_continuous_vecDot p).mul (continuous_apply i))),
    integral_const_mul, e0c_int_coord, e0c_int_ell_x]
  ring

theorem affSlope_add [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    affSlope n (fun x => f x + g x) = affSlope n f + affSlope n g := by
  funext i
  have hA : ((3 : ℝ) ^ n) ^ 2 / 12 ≠ 0 := by positivity
  refine mul_left_cancel₀ hA ?_
  have hxi := e0c_memLp n ((continuous_apply i : Continuous fun x : Vec d => x i))
  have h1 : Integrable (fun x => f x * x i) (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hf.integrable_mul hxi
  have h2 : Integrable (fun x => g x * x i) (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hg.integrable_mul hxi
  rw [e0c_slope_apply, Pi.add_apply, mul_add, e0c_slope_apply, e0c_slope_apply]
  simp only [add_mul]
  exact integral_add h1 h2

theorem affSlope_const_mul [NeZero d] (n : ℕ) (c : ℝ) (f : Vec d → ℝ) :
    affSlope n (fun x => c * f x) = c • affSlope n f := by
  funext i
  have hA : ((3 : ℝ) ^ n) ^ 2 / 12 ≠ 0 := by positivity
  refine mul_left_cancel₀ hA ?_
  rw [e0c_slope_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm, e0c_slope_apply]
  simp only [mul_assoc]
  exact integral_const_mul c _

theorem e0c_core [NeZero d] {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (p : Vec d) :
    cubeL2 n (fun x => (f x - cubeAverage (originCube d (n : ℤ)) f) - vecDot p x) ^ 2 =
      cubeL2 n (fun x => f x - cubeAverage (originCube d (n : ℤ)) f) ^ 2
        - 2 * (((3 : ℝ) ^ n) ^ 2 / 12) * vecDot (affSlope n f) p
        + ((3 : ℝ) ^ n) ^ 2 / 12 * vecNormSq p := by
  set c := cubeAverage (originCube d (n : ℤ)) f with hc
  have hh : MemLp (fun x => f x - c) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hf.sub (memLp_const c)
  have hl := e0c_memLp n (e0c_continuous_vecDot p)
  have hd : MemLp (fun x => (f x - c) - vecDot p x) 2
      (normalizedCubeMeasure (originCube d (n : ℤ))) := hh.sub hl
  rw [e0c_cubeL2_sq n hd, e0c_cubeL2_sq n hh]
  have hhl : Integrable (fun x => (f x - c) * vecDot p x)
      (normalizedCubeMeasure (originCube d (n : ℤ))) := hh.integrable_mul hl
  have hexp : ∫ x, ((f x - c) - vecDot p x) ^ 2 ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ∫ x, (f x - c) ^ 2 ∂normalizedCubeMeasure (originCube d (n : ℤ))
        - 2 * ∫ x, (f x - c) * vecDot p x ∂normalizedCubeMeasure (originCube d (n : ℤ))
        + ∫ x, vecDot p x ^ 2 ∂normalizedCubeMeasure (originCube d (n : ℤ)) := by
    have hpt : ∀ x : Vec d, ((f x - c) - vecDot p x) ^ 2 =
        (f x - c) ^ 2 - 2 * ((f x - c) * vecDot p x) + vecDot p x ^ 2 := fun x => by ring
    simp only [hpt]
    have i1 : Integrable (fun x => (f x - c) ^ 2)
        (normalizedCubeMeasure (originCube d (n : ℤ))) := hh.integrable_sq
    have i2 : Integrable (fun x => 2 * ((f x - c) * vecDot p x))
        (normalizedCubeMeasure (originCube d (n : ℤ))) := hhl.const_mul 2
    have i3 : Integrable (fun x => vecDot p x ^ 2)
        (normalizedCubeMeasure (originCube d (n : ℤ))) := hl.integrable_sq
    have i4 : Integrable (fun x => (f x - c) ^ 2 - 2 * ((f x - c) * vecDot p x))
        (normalizedCubeMeasure (originCube d (n : ℤ))) := i1.sub i2
    rw [integral_add i4 i3, integral_sub i1 i2, integral_const_mul]
  have hfl : ∫ x, f x * vecDot p x ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ((3 : ℝ) ^ n) ^ 2 / 12 * vecDot (affSlope n f) p := by
    rw [e0c_int_mul_ell n (fun i => hf.integrable_mul (e0c_memLp n (continuous_apply i)))]
    simp only [← e0c_slope_apply]
    unfold vecDot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmix : ∫ x, (f x - c) * vecDot p x ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ((3 : ℝ) ^ n) ^ 2 / 12 * vecDot (affSlope n f) p := by
    have hpt : ∀ x : Vec d, (f x - c) * vecDot p x = f x * vecDot p x - c * vecDot p x :=
      fun x => by ring
    simp only [hpt]
    have i1 : Integrable (fun x => f x * vecDot p x)
        (normalizedCubeMeasure (originCube d (n : ℤ))) := hf.integrable_mul hl
    have i2 : Integrable (fun x => c * vecDot p x)
        (normalizedCubeMeasure (originCube d (n : ℤ))) :=
      (hl.integrable (by norm_num)).const_mul c
    rw [integral_sub i1 i2, integral_const_mul, e0c_int_ell, hfl]
    ring
  have hll : ∫ x, vecDot p x ^ 2 ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ((3 : ℝ) ^ n) ^ 2 / 12 * vecNormSq p := by
    have h := e0c_int_ell_ell n p p
    simp only [← sq] at h
    exact h
  rw [hexp, hmix, hll]
  ring

theorem engNorm_affSlope_le [NeZero d] {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    engNorm (affSlope n f) ≤ 2 * Real.sqrt 3 * cubeFlat n f := by
  have h := e0c_core hf (affSlope n f)
  have h0 := sq_nonneg (cubeL2 n (fun x => (f x - cubeAverage (originCube d (n : ℤ)) f) -
    vecDot (affSlope n f) x))
  rw [h] at h0
  have hN : vecDot (affSlope n f) (affSlope n f) = vecNormSq (affSlope n f) := rfl
  rw [hN] at h0
  have hu := e0c_inv_mul n
  set F := cubeL2 n (fun x => f x - cubeAverage (originCube d (n : ℤ)) f) with hF
  set N := vecNormSq (affSlope n f) with hNdef
  have hflat : cubeFlat n f = ((3 : ℝ)⁻¹) ^ n * F := rfl
  have hFn : 0 ≤ F := ENNReal.toReal_nonneg
  have ht : 0 ≤ ((3 : ℝ)⁻¹) ^ n := by positivity
  rw [hflat]
  have hR : 0 ≤ 2 * Real.sqrt 3 * (((3 : ℝ)⁻¹) ^ n * F) := by positivity
  apply le_of_sq_le_sq _ hR
  rw [engNorm_sq, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), mul_pow]
  have h12 := mul_nonneg (by positivity : (0 : ℝ) ≤ 12 * (((3 : ℝ)⁻¹) ^ n) ^ 2) h0
  have e : 12 * (((3 : ℝ)⁻¹) ^ n) ^ 2 * (F ^ 2 - 2 * (((3 : ℝ) ^ n) ^ 2 / 12) * N +
      ((3 : ℝ) ^ n) ^ 2 / 12 * N) =
      12 * (((3 : ℝ)⁻¹) ^ n) ^ 2 * F ^ 2 - ((3 : ℝ) ^ n * ((3 : ℝ)⁻¹) ^ n) ^ 2 * N := by
    ring
  rw [e, hu] at h12
  nlinarith only [h12]

theorem cubeFlat_sub_affSlope_le [NeZero d] {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) (p : Vec d) :
    cubeFlat n (fun x => f x - vecDot (affSlope n f) x) ≤
      cubeFlat n (fun x => f x - vecDot p x) := by
  have key : ∀ q : Vec d, cubeFlat n (fun x => f x - vecDot q x) =
      ((3 : ℝ)⁻¹) ^ n * cubeL2 n (fun x =>
        (f x - cubeAverage (originCube d (n : ℤ)) f) - vecDot q x) := by
    intro q
    have hav : cubeAverage (originCube d (n : ℤ)) (fun x => f x - vecDot q x) =
        cubeAverage (originCube d (n : ℤ)) f := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure,
        cubeAverage_eq_integral_normalizedCubeMeasure,
        integral_sub (hf.integrable (by norm_num)) (e0c_integrable n (e0c_continuous_vecDot q)),
        e0c_int_ell, sub_zero]
    unfold cubeFlat
    rw [hav]
    congr 2
    funext x
    ring
  rw [key, key]
  have ht : 0 ≤ ((3 : ℝ)⁻¹) ^ n := by positivity
  refine mul_le_mul_of_nonneg_left ?_ ht
  have hs := e0c_core hf (affSlope n f)
  have hp := e0c_core hf p
  have hd := e0c_dist_nonneg (affSlope n f) p
  have hA : 0 ≤ ((3 : ℝ) ^ n) ^ 2 / 12 := by positivity
  have hdA := mul_nonneg hA hd
  have hnn : 0 ≤ cubeL2 n (fun x =>
      (f x - cubeAverage (originCube d (n : ℤ)) f) - vecDot p x) := ENNReal.toReal_nonneg
  apply le_of_sq_le_sq _ hnn
  rw [hs, hp]
  have hN : vecDot (affSlope n f) (affSlope n f) = vecNormSq (affSlope n f) := rfl
  rw [hN]
  nlinarith only [hdA]

/-- Witness: for `f = p · x` the slope is `p`, and the flatness bound reads `|p| ≤ 2√3 · |p|/(2√3)`. -/
example [NeZero d] (n : ℕ) (p : Vec d) :
    affSlope n (fun x => vecDot p x) = p ∧
      engNorm (affSlope n (fun x => vecDot p x)) ≤
        2 * Real.sqrt 3 * cubeFlat n (fun x => vecDot p x) :=
  ⟨by simpa using affSlope_affine n 0 p, engNorm_affSlope_le (e0c_memLp n (e0c_continuous_vecDot p))⟩

end SuperdiffusionCLT.Section6
