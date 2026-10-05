/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaH

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Pointwise bounds for the divergence terms of the cutoff datum
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3c_div_matVec_grad_le {A : CoeffField d}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) {δ K G₁ G₂ lam : ℝ} (x : Vec d)
    (hδ : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ) (hδ1 : δ ≤ 1)
    (hK : ∀ i j k, |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K)
    (hg1 : ∀ i, |p12_grad η x i| ≤ G₁ / lam)
    (hg2 : ∀ j k, |fderiv ℝ (fun y => p12_grad η y j) x (basisVec k)| ≤ G₂ / lam ^ 2)
    (hG₁ : 0 ≤ G₁ / lam) :
    |r3c_div (fun y => matVecMul (A y) (p12_grad η y)) x| ≤
      (d : ℝ) ^ 2 * (K * (G₁ / lam) + 2 * (G₂ / lam ^ 2)) := by
  have hAij : ∀ i j, |A x i j| ≤ 2 := fun i j => by
    have h1 := hδ i j
    have h2 : |(1 : Mat d) i j| ≤ 1 := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    have := abs_sub_abs_le_abs_sub (A x i j) ((1 : Mat d) i j)
    linarith only [this, h1, h2, hδ1]
  have hterm : ∀ i : Fin d, |fderiv ℝ (fun y => matVecMul (A y) (p12_grad η y) i) x (basisVec i)| ≤
      d * (K * (G₁ / lam) + 2 * (G₂ / lam ^ 2)) := by
    intro i
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)), HasFDerivAt
        (fun y => A y i j * p12_grad η y j)
        (A x i j • fderiv ℝ (fun y => p12_grad η y j) x +
          p12_grad η x j • fderiv ℝ (fun y => A y i j) x) x := by
      intro j _
      exact ((((hAs i j).differentiable (by simp)) x).hasFDerivAt.mul
        (((r3c_contDiff_grad_apply hη j).differentiable (by simp)) x).hasFDerivAt).congr_fderiv
        (by ext v; simp)
    have hs := HasFDerivAt.fun_sum hj
    have e1 : (fun y => matVecMul (A y) (p12_grad η y) i) = fun y => ∑ j, A y i j * p12_grad η y j := by
      funext y; simp [matVecMul]
    rw [e1, hs.fderiv]
    simp only [sum_apply, add_apply, smul_apply,
      smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ j ∈ (Finset.univ : Finset (Fin d)), |A x i j * fderiv ℝ (fun y => p12_grad η y j) x (basisVec i) +
        p12_grad η x j * fderiv ℝ (fun y => A y i j) x (basisVec i)| ≤ K * (G₁ / lam) + 2 * (G₂ / lam ^ 2) := by
      intro j _
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have a1 : |A x i j| * |fderiv ℝ (fun y => p12_grad η y j) x (basisVec i)| ≤ 2 * (G₂ / lam ^ 2) :=
        mul_le_mul (hAij i j) (hg2 j i) (abs_nonneg _) (by norm_num)
      have a2 : |p12_grad η x j| * |fderiv ℝ (fun y => A y i j) x (basisVec i)| ≤ (G₁ / lam) * K :=
        mul_le_mul (hg1 j) (hK i j i) (abs_nonneg _) hG₁
      linarith only [a1, a2, mul_comm (G₁ / lam) K]
    refine (Finset.sum_le_sum this).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_rfl
  unfold r3c_div
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)


/-- The forcing `g = -c (A - 1) e_e` produced by subtracting `c · n` from a solution. -/
noncomputable def r3c_slopeField (A : CoeffField d) (e : Fin d) (c : ℝ) (y : Vec d) : Vec d :=
  fun i => -c * (A y i e - (1 : Mat d) i e)

theorem r3c_slopeField_contDiff {A : CoeffField d}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) (e : Fin d) (c : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => r3c_slopeField A e c y i) := by
  unfold r3c_slopeField
  exact contDiff_const.mul ((hAs i e).sub contDiff_const)

theorem r3c_slopeField_abs_le {A : CoeffField d} (e : Fin d) (c : ℝ) {δ : ℝ} (x : Vec d)
    (hδ : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ) (i : Fin d) :
    |r3c_slopeField A e c x i| ≤ |c| * δ := by
  unfold r3c_slopeField
  rw [abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (hδ i e) (abs_nonneg _)

theorem r3c_slopeField_norm_le {A : CoeffField d} (e : Fin d) (c : ℝ) {δ : ℝ} (x : Vec d)
    (hδ : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ) (hδ0 : 0 ≤ δ) :
    ‖r3c_slopeField A e c x‖ ≤ |c| * δ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
    rw [Real.norm_eq_abs]; exact r3c_slopeField_abs_le e c x hδ i

theorem r3c_div_cut_slope_le {A : CoeffField d}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη01 : ∀ y, 0 ≤ η y ∧ η y ≤ 1) (e : Fin d) (c : ℝ)
    {δ K G₁ lam : ℝ} (x : Vec d) (hδ : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ)
    (hK : ∀ i j k, |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K)
    (hg1 : ∀ i, |p12_grad η x i| ≤ G₁ / lam) :
    |r3c_div (fun y => η y • r3c_slopeField A e c y) x| ≤
      d * ((G₁ / lam) * (|c| * δ) + |c| * K) := by
  have hterm : ∀ i : Fin d, |fderiv ℝ (fun y => η y • r3c_slopeField A e c y i) x (basisVec i)| ≤
      (G₁ / lam) * (|c| * δ) + |c| * K := by
    intro i
    have h1 : DifferentiableAt ℝ η x := (hη.differentiable (by simp)) x
    have h2 : DifferentiableAt ℝ (fun y => r3c_slopeField A e c y i) x :=
      ((r3c_slopeField_contDiff hAs e c i).differentiable (by simp)) x
    have e1 : (fun y => (η y • r3c_slopeField A e c y) i) = fun y => η y * r3c_slopeField A e c y i := by
      funext y; simp
    show |fderiv ℝ (fun y => (η y • r3c_slopeField A e c y) i) x (basisVec i)| ≤ _
    rw [e1, fderiv_fun_mul h1 h2]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have e2 : fderiv ℝ (fun y => r3c_slopeField A e c y i) x (basisVec i) =
        -c * fderiv ℝ (fun y => A y i e) x (basisVec i) := by
      have : (fun y => r3c_slopeField A e c y i) = fun y => -c * (A y i e - (1 : Mat d) i e) := rfl
      rw [this]
      have hA : DifferentiableAt ℝ (fun y => A y i e) x := ((hAs i e).differentiable (by simp)) x
      rw [fderiv_const_mul (hA.sub_const _), fderiv_sub_const]
      simp
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    have b1 : |η x * (-c * fderiv ℝ (fun y => A y i e) x (basisVec i))| ≤ |c| * K := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (hη01 x).1]
      calc η x * (|c| * |fderiv ℝ (fun y => A y i e) x (basisVec i)|) ≤ 1 * (|c| * K) :=
            mul_le_mul (hη01 x).2 (mul_le_mul_of_nonneg_left (hK i e i) (abs_nonneg _))
              (by positivity) zero_le_one
        _ = |c| * K := one_mul _
    have b2 : |r3c_slopeField A e c x i * fderiv ℝ η x (basisVec i)| ≤ (G₁ / lam) * (|c| * δ) := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul (hg1 i) (r3c_slopeField_abs_le e c x hδ i) (abs_nonneg _)
        ((abs_nonneg _).trans (hg1 i))
    linarith only [b1, b2]
  unfold r3c_div
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_rfl


theorem r3c_abs_entry_le_two {A : CoeffField d} {δ : ℝ} (x : Vec d)
    (hδ : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ) (hδ1 : δ ≤ 1) (i j : Fin d) : |A x i j| ≤ 2 := by
  have h1 := hδ i j
  have h2 : |(1 : Mat d) i j| ≤ 1 := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have := abs_sub_abs_le_abs_sub (A x i j) ((1 : Mat d) i j)
  linarith only [this, h1, h2, hδ1]

theorem r3c_norm_matVec_le {A : CoeffField d} {δ : ℝ} (x : Vec d)
    (hδ : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ) (hδ1 : δ ≤ 1) (y : Vec d) :
    ‖matVecMul (A x) y‖ ≤ 2 * d * ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [matVecMul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ j ∈ (Finset.univ : Finset (Fin d)), |A x i j * y j| ≤ 2 * ‖y‖ := by
    intro j _
    rw [abs_mul]
    exact mul_le_mul (r3c_abs_entry_le_two x hδ hδ1 i j) (r3c_abs_apply_le y j) (abs_nonneg _)
      (by norm_num)
  refine (Finset.sum_le_sum this).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

theorem r3c_norm_grad_le {η : Vec d → ℝ} {G₁ lam : ℝ} (x : Vec d) (hG : 0 ≤ G₁ / lam)
    (hg1 : ∀ i, |p12_grad η x i| ≤ G₁ / lam) : ‖p12_grad η x‖ ≤ G₁ / lam :=
  (pi_norm_le_iff_of_nonneg hG).2 fun i => by rw [Real.norm_eq_abs]; exact hg1 i


/-- **Pointwise bound of the cutoff datum.** -/
theorem r3c_cutoffData_le {U : Set (Vec d)} {A : CoeffField d}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη01 : ∀ y, 0 ≤ η y ∧ η y ≤ 1) (e : Fin d) (c : ℝ)
    {δ K G₁ G₂ lam : ℝ} (hl : 0 < lam) (hG1 : 0 ≤ G₁) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hKl : K * lam ≤ δ) (f : Vec d → ℝ) (u : H1Function U) (x : Vec d)
    (hδ : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ δ)
    (hK : ∀ i j k, |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K)
    (hg1 : ∀ i, |p12_grad η x i| ≤ G₁ / lam)
    (hg2 : ∀ j k, |fderiv ℝ (fun y => p12_grad η y j) x (basisVec k)| ≤ G₂ / lam ^ 2) :
    |r3c_cutoffData A η f (r3c_slopeField A e c) u x| ≤ |f x| +
      (4 * (d : ℝ) ^ 2 * G₁ / lam) * ‖u.grad x‖ +
      ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2) * |u.toFun x| +
      (2 * d * G₁ + d) * (|c| * δ / lam) := by
  have hG : 0 ≤ G₁ / lam := div_nonneg hG1 hl.le
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK e e e)
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hKd : K ≤ δ / lam := by rw [le_div_iff₀ hl]; exact hKl
  set g : Vec d → Vec d := r3c_slopeField A e c with hgdef
  have hgn : ‖g x‖ ≤ |c| * δ := r3c_slopeField_norm_le e c x hδ hδ0
  have hn1 : ‖p12_grad η x‖ ≤ G₁ / lam := r3c_norm_grad_le x hG hg1
  have hAu : ‖matVecMul (A x) (u.grad x)‖ ≤ 2 * d * ‖u.grad x‖ := r3c_norm_matVec_le x hδ hδ1 _
  have hBn : ‖matVecMul (A x) (p12_grad η x)‖ ≤ 2 * d * (G₁ / lam) :=
    (r3c_norm_matVec_le x hδ hδ1 _).trans (mul_le_mul_of_nonneg_left hn1 (by positivity))
  set e1 : ℝ := |c| * δ / lam with he1
  have he10 : 0 ≤ e1 := by positivity
  have hT2 : |vecDot (g x) (p12_grad η x)| ≤ d * G₁ * e1 := by
    refine (p12_abs_vecDot_le _ _).trans ?_
    calc (d : ℝ) * (‖g x‖ * ‖p12_grad η x‖) ≤ d * ((|c| * δ) * (G₁ / lam)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hgn hn1 (norm_nonneg _) (by positivity)) hdn
      _ = d * G₁ * e1 := by rw [he1]; ring
  have hT3 : |vecDot (matVecMul (A x) (u.grad x)) (p12_grad η x)| ≤ 2 * d ^ 2 * (G₁ / lam) * ‖u.grad x‖ := by
    refine (p12_abs_vecDot_le _ _).trans ?_
    calc (d : ℝ) * (‖matVecMul (A x) (u.grad x)‖ * ‖p12_grad η x‖) ≤
          d * ((2 * d * ‖u.grad x‖) * (G₁ / lam)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hAu hn1 (norm_nonneg _) (by positivity)) hdn
      _ = 2 * d ^ 2 * (G₁ / lam) * ‖u.grad x‖ := by ring
  have hT5 : |vecDot (u.grad x) (matVecMul (A x) (p12_grad η x))| ≤ 2 * d ^ 2 * (G₁ / lam) * ‖u.grad x‖ := by
    refine (p12_abs_vecDot_le _ _).trans ?_
    calc (d : ℝ) * (‖u.grad x‖ * ‖matVecMul (A x) (p12_grad η x)‖) ≤
          d * (‖u.grad x‖ * (2 * d * (G₁ / lam))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBn (norm_nonneg _)) hdn
      _ = 2 * d ^ 2 * (G₁ / lam) * ‖u.grad x‖ := by ring
  have hT4 := r3c_div_cut_slope_le hAs hη hη01 e c x hδ hK hg1
  have hT6 := r3c_div_matVec_grad_le hAs hη x hδ hδ1 hK hg1 hg2 hG
  have hKG : K * (G₁ / lam) ≤ G₁ / lam ^ 2 := by
    calc K * (G₁ / lam) ≤ (δ / lam) * (G₁ / lam) := mul_le_mul_of_nonneg_right hKd hG
      _ ≤ (1 / lam) * (G₁ / lam) := by
          gcongr
      _ = G₁ / lam ^ 2 := by field_simp
  have hT6' : |r3c_div (fun y => matVecMul (A y) (p12_grad η y)) x| ≤
      (d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2 := by
    refine hT6.trans ?_
    have : (d : ℝ) ^ 2 * (K * (G₁ / lam) + 2 * (G₂ / lam ^ 2)) ≤
        (d : ℝ) ^ 2 * (G₁ / lam ^ 2 + 2 * (G₂ / lam ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hKG]) (by positivity)
    refine this.trans (le_of_eq ?_)
    ring
  have hT4' : |r3c_div (fun y => η y • g y) x| ≤ d * (G₁ + 1) * e1 := by
    refine hT4.trans ?_
    have h2 : (|c| * K) ≤ |c| * δ / lam := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hKd (abs_nonneg _)
    calc (d : ℝ) * ((G₁ / lam) * (|c| * δ) + |c| * K) ≤ d * (G₁ * e1 + e1) := by
          refine mul_le_mul_of_nonneg_left ?_ hdn
          have : (G₁ / lam) * (|c| * δ) = G₁ * e1 := by rw [he1]; ring
          rw [this]
          linarith only [h2]
      _ = d * (G₁ + 1) * e1 := by ring
  have hT1 : |η x * f x| ≤ |f x| := by
    rw [abs_mul, abs_of_nonneg (hη01 x).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (hη01 x).2
  have hT6'' : |u.toFun x * r3c_div (fun y => matVecMul (A y) (p12_grad η y)) x| ≤
      ((d : ℝ) ^ 2 * (G₁ + 2 * G₂) / lam ^ 2) * |u.toFun x| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hT6' (abs_nonneg _)
  unfold r3c_cutoffData
  have hsum : |(η x * f x + vecDot (g x) (p12_grad η x) -
      vecDot (matVecMul (A x) (u.grad x)) (p12_grad η x)) -
      (r3c_div (fun y => η y • g y) x +
        (vecDot (u.grad x) (matVecMul (A x) (p12_grad η x)) +
          u.toFun x * r3c_div (fun y => matVecMul (A y) (p12_grad η y)) x))| ≤
      |η x * f x| + |vecDot (g x) (p12_grad η x)| + |vecDot (matVecMul (A x) (u.grad x)) (p12_grad η x)| +
        (|r3c_div (fun y => η y • g y) x| + (|vecDot (u.grad x) (matVecMul (A x) (p12_grad η x))| +
          |u.toFun x * r3c_div (fun y => matVecMul (A y) (p12_grad η y)) x|)) := by
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans le_rfl) le_rfl)) ?_
    exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
  refine hsum.trans ?_
  have hc1 : (4 * (d : ℝ) ^ 2 * G₁ / lam) * ‖u.grad x‖ =
      2 * d ^ 2 * (G₁ / lam) * ‖u.grad x‖ + 2 * d ^ 2 * (G₁ / lam) * ‖u.grad x‖ := by ring
  have hc2 : (2 * d * G₁ + d) * e1 = d * G₁ * e1 + d * (G₁ + 1) * e1 := by ring
  linarith only [hT1, hT2, hT3, hT4', hT5, hT6'', hc1, hc2]


theorem r3c_div_eq_zero_of_eventually {B : Vec d → Vec d} {x : Vec d}
    (hB : ∀ i, (fun y => B y i) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) : r3c_div B x = 0 := by
  unfold r3c_div
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [(hB i).fderiv_eq (𝕜 := ℝ)]
  simp

/-- The cutoff datum vanishes off the support of the cutoff. -/
theorem r3c_cutoffData_eq_zero {U : Set (Vec d)} (A : CoeffField d) {η : Vec d → ℝ} (f : Vec d → ℝ)
    (g : Vec d → Vec d) (u : H1Function U) {x : Vec d} (hx : x ∉ tsupport η) :
    r3c_cutoffData A η f g u x = 0 := by
  have hnhds : (tsupport η)ᶜ ∈ 𝓝 x := (isClosed_tsupport η).isOpen_compl.mem_nhds hx
  have h1 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
  have h2 : p12_grad η x = 0 := p12_grad_eq_zero_of_notMem hx
  have hD1 : r3c_div (fun y => η y • g y) x = 0 := by
    refine r3c_div_eq_zero_of_eventually fun i => ?_
    filter_upwards [hnhds] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  have hD2 : r3c_div (fun y => matVecMul (A y) (p12_grad η y)) x = 0 := by
    refine r3c_div_eq_zero_of_eventually fun i => ?_
    filter_upwards [hnhds] with y hy
    simp [p12_grad_eq_zero_of_notMem hy, p12_matVecMul_zero]
  unfold r3c_cutoffData
  rw [hD1, hD2, h1, h2]
  simp [p12_matVecMul_zero, vecDot]

end SuperdiffusionCLT.Section7
