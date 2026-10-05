/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryO

/-!
# The crude bound and the inner gradient in normalized form
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ca2_Z_gen [NeZero d] (m : ℤ) {W : Set (Vec d)} (hWo : IsOpen W)
    (u : H1Function (openCubeSet (originCube d m) ∩ W)) {b : ℝ} (hb : 0 < b)
    {S : Set (Vec d)} (hSm : MeasurableSet S) (hSD : S ⊆ openCubeSet (originCube d m) ∩ W)
    (hS : ∀ x ∈ S, ∀ k, |x k| ≤ 2 / 3 * b) :
    ∫ x in S, vecNormSq (u.grad x) ≤ (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 *
      ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi b x * vecNormSq (u.grad x) := by
  classical
  have hDo : IsOpen (openCubeSet (originCube d m) ∩ W) := (isOpen_openCubeSet _).inter hWo
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have hX := ca2_integrable_energy u (ca2_contDiff_Phi (d := d) b) (ca1_hasCompactSupport_Phi hb)
  have hnn : ∀ x : Vec d, 0 ≤ vecNormSq (u.grad x) := fun x => by
    unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hint : Integrable (fun x => vecNormSq (u.grad x))
      (volume.restrict (openCubeSet (originCube d m) ∩ W)) := by
    have h1 : Integrable (fun x => eucNorm (u.grad x) ^ 2)
        (volume.restrict (openCubeSet (originCube d m) ∩ W)) := (memLp_eucNorm_grad u).integrable_sq
    have h2 : (fun x => eucNorm (u.grad x) ^ 2) = fun x => vecNormSq (u.grad x) := by
      funext x
      unfold eucNorm
      exact Real.sq_sqrt (hnn x)
    rw [h2] at h1
    exact h1
  have h1 : ∫ x in S, vecNormSq (u.grad x) ≤
      ∫ x in S, (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * (ca1_Phi b x * vecNormSq (u.grad x)) := by
    refine setIntegral_mono_on (hint.mono_measure (Measure.restrict_mono hSD le_rfl))
      ((hX.mono_set hSD).const_mul _) hSm ?_
    intro x hx
    have hl := ca1_phi_lower hb (hS x hx)
    have hΦ : ((125 / 729 : ℝ) ^ d) ^ 2 ≤ ca1_Phi b x := by
      rw [ca1_Phi_eq]; exact pow_le_pow_left₀ hc0.le hl 2
    have h3 : 1 ≤ (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ca1_Phi b x := by
      have e : (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ((125 / 729 : ℝ) ^ d) ^ 2 = 1 := by field_simp
      calc (1 : ℝ) = (((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ((125 / 729 : ℝ) ^ d) ^ 2 := e.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hΦ (sq_nonneg _)
    calc vecNormSq (u.grad x) = 1 * vecNormSq (u.grad x) := (one_mul _).symm
      _ ≤ ((((125 / 729 : ℝ) ^ d)⁻¹) ^ 2 * ca1_Phi b x) * vecNormSq (u.grad x) :=
          mul_le_mul_of_nonneg_right h3 (hnn x)
      _ = _ := by ring
  refine h1.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  refine setIntegral_mono_set hX ?_ (Filter.Eventually.of_forall hSD)
  exact Filter.Eventually.of_forall fun x => mul_nonneg (by rw [ca1_Phi_eq]; exact sq_nonneg _) (hnn x)

/-- The constant of the crude bound. -/
noncomputable def ca2_c8 : ℝ := 288 * (50 / 23) ^ 2 + 2

theorem ca2_crude_norm [NeZero d] (m : ℤ) {W : Set (Vec d)} (hWo : IsOpen W)
    {lam Lam ν Λ : ℝ} {A : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m) ∩ W) A) (hν : 0 < ν) (hΛ : 0 ≤ Λ)
    (hsym : ∀ x ∈ openCubeSet (originCube d m) ∩ W, symmPart (A x) = ν • (1 : Mat d))
    (hop : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ∀ v : Vec d,
      eucNorm (matVecMul (A x) v) ≤ Λ * eucNorm v)
    (u : H1Function (openCubeSet (originCube d m) ∩ W)) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m) ∩ W)))
    (hu : IsWeakSolutionOn A (openCubeSet (originCube d m) ∩ W) u f (fun _ => 0))
    {γ : Vec d → ℝ} (hγ : ContDiff ℝ 2 γ)
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m) ∩ W)
      (openCubeSet (originCube d m)) (fun x => u.toFun x - γ x))
    {G1 : ℝ} (hG1 : 0 ≤ G1) (hb1 : ∀ x ∈ openCubeSet (originCube d m) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1)
    {Fn Wn Gc w2 : ℝ}
    (hGcs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      ca1_Phi (23 / 50 * (3 : ℝ) ^ m) x * vecNormSq (u.grad x) = Gc ^ 2)
    (hFs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W, f x ^ 2 = Fn ^ 2)
    (hWs : (cubeVolume (originCube d m))⁻¹ * ∫ x in openCubeSet (originCube d m) ∩ W,
      (u.toFun x - γ x) ^ 2 = Wn ^ 2)
    (hw2 : Wn / (3 : ℝ) ^ m ≤ w2) (hG1w : G1 ≤ w2) (hWn0 : 0 ≤ Wn) :
    ν * Gc ^ 2 ≤ ca2_c8 * (ν⁻¹ * ((3 : ℝ) ^ m * Fn) ^ 2 + ν * w2 ^ 2 + d * Λ ^ 2 * ν⁻¹ * w2 ^ 2) := by
  classical
  have hL : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hDo : IsOpen (openCubeSet (originCube d m) ∩ W) := (isOpen_openCubeSet _).inter hWo
  have hDb : Bornology.IsBounded (openCubeSet (originCube d m) ∩ W) :=
    (isBounded_openCubeSet (originCube d m)).subset Set.inter_subset_left
  have hac : 0 < 23 / 50 * (3 : ℝ) ^ m := by positivity
  have hat : 23 / 50 * (3 : ℝ) ^ m < 3 ^ m / 2 := by linarith only [hL]
  have haV : Metric.closedBall (0 : Vec d) (23 / 50 * (3 : ℝ) ^ m) ⊆ openCubeSet (originCube d m) :=
    ca1_closedBall_subset_openCube m hat
  have hcr := ca2_crude hDo (ca2_isOpen_cube m) hDb hEll hν hΛ hsym hop u hf hu hγ hZ hac haV hG1 hb1
  have hV0 : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  set Vq := cubeVolume (originCube d m) with hVq
  have hXc : ∫ x in openCubeSet (originCube d m) ∩ W, ca1_Phi (23 / 50 * (3 : ℝ) ^ m) x * vecNormSq (u.grad x) =
      Vq * Gc ^ 2 := by rw [← hGcs, ← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul]
  have hXF : ∫ x in openCubeSet (originCube d m) ∩ W, f x ^ 2 = Vq * Fn ^ 2 := by
    rw [← hFs, ← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul]
  have hXW : ∫ x in openCubeSet (originCube d m) ∩ W, (u.toFun x - γ x) ^ 2 = Vq * Wn ^ 2 := by
    rw [← hWs, ← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul]
  have hvD : (volume (openCubeSet (originCube d m) ∩ W)).toReal ≤ Vq := by
    have h0 : (volume (openCubeSet (originCube d m))).toReal = Vq := ca2_volume_openCube_toReal _
    rw [← h0]
    exact ENNReal.toReal_mono (isBounded_openCubeSet (originCube d m)).measure_lt_top.ne
      (measure_mono Set.inter_subset_left)
  rw [hXc, hXF, hXW] at hcr
  set ac := 23 / 50 * (3 : ℝ) ^ m with hacdef
  have hvD0 : 0 ≤ (volume (openCubeSet (originCube d m) ∩ W)).toReal := ENNReal.toReal_nonneg
  have hc2 : 0 < ac ^ 2 := by positivity
  -- divide by `Vq`
  have h1 : ν * Gc ^ 2 ≤ ac ^ 2 / ν * Fn ^ 2 + (ν / ac ^ 2 + 288 * d * Λ ^ 2 / (ν * ac ^ 2)) * Wn ^ 2 +
      2 * (Λ ^ 2 * d * G1 ^ 2 / ν) := by
    have h2 : 2 * (Λ ^ 2 * d * G1 ^ 2 / ν) * (volume (openCubeSet (originCube d m) ∩ W)).toReal ≤
        2 * (Λ ^ 2 * d * G1 ^ 2 / ν) * Vq :=
      mul_le_mul_of_nonneg_left hvD (by positivity)
    have h3 : Vq * (ν * Gc ^ 2) ≤ Vq * (ac ^ 2 / ν * Fn ^ 2 + (ν / ac ^ 2 + 288 * d * Λ ^ 2 / (ν * ac ^ 2)) * Wn ^ 2 +
        2 * (Λ ^ 2 * d * G1 ^ 2 / ν)) := by
      nlinarith only [hcr, h2]
    exact le_of_mul_le_mul_left h3 hV0
  refine h1.trans ?_
  have e1 : ac ^ 2 / ν * Fn ^ 2 = (23 / 50) ^ 2 * (ν⁻¹ * ((3 : ℝ) ^ m * Fn) ^ 2) := by
    rw [hacdef]; field_simp
  have e2 : (ν / ac ^ 2 + 288 * d * Λ ^ 2 / (ν * ac ^ 2)) * Wn ^ 2 =
      (50 / 23) ^ 2 * (ν * (Wn / (3 : ℝ) ^ m) ^ 2) +
        288 * (50 / 23) ^ 2 * (d * Λ ^ 2 * ν⁻¹ * (Wn / (3 : ℝ) ^ m) ^ 2) := by
    rw [hacdef]; field_simp
  have hw0 : 0 ≤ Wn / (3 : ℝ) ^ m := by positivity
  have hw2sq : (Wn / (3 : ℝ) ^ m) ^ 2 ≤ w2 ^ 2 := pow_le_pow_left₀ hw0 hw2 2
  have hG2sq : G1 ^ 2 ≤ w2 ^ 2 := pow_le_pow_left₀ hG1 hG1w 2
  have hF0 : 0 ≤ ν⁻¹ * ((3 : ℝ) ^ m * Fn) ^ 2 := by positivity
  have hs1 : 0 ≤ ν * w2 ^ 2 := by positivity
  have hs2 : 0 ≤ (d : ℝ) * Λ ^ 2 * ν⁻¹ * w2 ^ 2 := by positivity
  have t1 : ν * (Wn / (3 : ℝ) ^ m) ^ 2 ≤ ν * w2 ^ 2 := mul_le_mul_of_nonneg_left hw2sq hν.le
  have t2 : (d : ℝ) * Λ ^ 2 * ν⁻¹ * (Wn / (3 : ℝ) ^ m) ^ 2 ≤ (d : ℝ) * Λ ^ 2 * ν⁻¹ * w2 ^ 2 :=
    mul_le_mul_of_nonneg_left hw2sq (by positivity)
  have t3 : Λ ^ 2 * d * G1 ^ 2 / ν ≤ (d : ℝ) * Λ ^ 2 * ν⁻¹ * w2 ^ 2 := by
    have : Λ ^ 2 * d * G1 ^ 2 / ν = (d : ℝ) * Λ ^ 2 * ν⁻¹ * G1 ^ 2 := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hG2sq (by positivity)
  rw [e1, e2]
  unfold ca2_c8
  have hc1 : (23 / 50 : ℝ) ^ 2 ≤ 288 * (50 / 23) ^ 2 + 2 := by norm_num
  have hc2' : (50 / 23 : ℝ) ^ 2 ≤ 288 * (50 / 23) ^ 2 + 2 := by norm_num
  nlinarith only [mul_le_mul_of_nonneg_right hc1 hF0, mul_le_mul_of_nonneg_right hc2' hs1, t1, t2, t3, hs2,
    mul_le_mul_of_nonneg_left t1 (by norm_num : (0 : ℝ) ≤ (50 / 23) ^ 2),
    mul_le_mul_of_nonneg_left t2 (by norm_num : (0 : ℝ) ≤ 288 * (50 / 23) ^ 2)]

end SuperdiffusionCLT.Section7
