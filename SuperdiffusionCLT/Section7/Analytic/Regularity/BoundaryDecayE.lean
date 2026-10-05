/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaN
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayD

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# The tangential coefficients are controlled by the face energy

For `u` with zero trace on the face and the tangential affine function `m = a + ∑ b_k x_k`,
the two families of box test functions give `a²` and `b_k²` in terms of the gradient energy of `u`
near the face and `‖u - m‖²_{L²}`, with a free small width `h`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3d_face_a (e : Fin d) (m : ℤ) {ρ h r K : ℝ} (hρ : 0 < ρ) (hh : 0 < h)
    (hhL : h < (3 : ℝ) ^ m / 2) (hρL : ρ < (3 : ℝ) ^ m / 2) (hρr : ρ ≤ r) (hhr : h ≤ r)
    (hK : ∀ t, |deriv (r3d_bump (r := 1) one_pos) t| ≤ K)
    (u : H1Function (openCubeSet (originCube d m)))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) u.toFun)
    (a : ℝ) (b : Vec d) :
    a ^ 2 * ρ ^ (2 * (d - 1)) ≤ (2 * ρ) ^ (d - 1) *
      (4 * h * (∫ x in r3d_Ebox e m r, u.grad x e ^ 2) +
        4 * K ^ 2 / h * ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2) := by
  set L : ℝ := (3 : ℝ) ^ m / 2 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  have hcore := r3d_face_core e m (ρ := ρ) (h := h) (r := r) (K := K) hh hhL hρL hρr hhr hK
    (fun _ => (r3d_bump hρ : ℝ → ℝ)) (fun _ => r3d_bump_contDiff hρ) (fun _ => r3d_bump_compact hρ)
    (fun _ => by simpa using r3d_bump_tsupport hρ) u hZ a b
  rw [← hL] at hcore
  have hB1 : ρ ≤ ∫ t in Set.Ioo (-L) L, (r3d_bump hρ : ℝ → ℝ) t :=
    r3d_bump_integral_ge hρ (by rw [hL] at hρL ⊢; linarith only [hρL])
  have hodd : ∫ t in Set.Ioo (-L) L, t * (r3d_bump hρ : ℝ → ℝ) t = 0 :=
    r3d_bump_integral_odd hLpos.le hρ
  set B1 : ℝ := ∫ t in Set.Ioo (-L) L, (r3d_bump hρ : ℝ → ℝ) t with hB1d
  have hsum : ∑ k ∈ Finset.univ.erase e, b k * ∏ i ∈ Finset.univ.erase e,
      (if i = k then (∫ t in Set.Ioo (-L) L, t * (r3d_bump hρ : ℝ → ℝ) t)
        else (∫ t in Set.Ioo (-L) L, (r3d_bump hρ : ℝ → ℝ) t)) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.prod_eq_zero hk (by simp [hodd]), mul_zero]
  have hprod : ∏ i ∈ Finset.univ.erase e, (∫ t in Set.Ioo (-L) L, (r3d_bump hρ : ℝ → ℝ) t) =
      B1 ^ (d - 1) := by
    rw [Finset.prod_const, r3d_card_erase]
  rw [hsum, hprod, add_zero] at hcore
  have hSg : ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, (r3d_bump hρ : ℝ → ℝ) t ^ 2 ≤
      (2 * ρ) ^ (d - 1) := by
    calc ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, (r3d_bump hρ : ℝ → ℝ) t ^ 2
        ≤ ∏ _j ∈ Finset.univ.erase e, (2 * ρ) :=
          Finset.prod_le_prod₀ (fun j _ => integral_nonneg fun t => sq_nonneg _)
            (fun j _ => r3d_bump_integral_sq_le hρ)
      _ = (2 * ρ) ^ (d - 1) := by rw [Finset.prod_const, r3d_card_erase]
  have hX : 0 ≤ ∫ x in r3d_Ebox e m r, u.grad x e ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hG : 0 ≤ ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hK0 : 0 ≤ 2 * K ^ 2 / h := by positivity
  set Sg := ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, (r3d_bump hρ : ℝ → ℝ) t ^ 2 with hSgd
  set X := ∫ x in r3d_Ebox e m r, u.grad x e ^ 2 with hXd
  set G := ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 with hGd
  have c1 : (2 * h) * Sg * X ≤ (2 * h) * (2 * ρ) ^ (d - 1) * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSg (by positivity)) hX
  have c2 : (2 * K ^ 2 / h) * Sg * G ≤ (2 * K ^ 2 / h) * (2 * ρ) ^ (d - 1) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSg hK0) hG
  have hlow : a ^ 2 * ρ ^ (2 * (d - 1)) ≤ (a * B1 ^ (d - 1)) ^ 2 := by
    have h1 : ρ ^ (d - 1) ≤ B1 ^ (d - 1) := pow_le_pow_left₀ hρ.le hB1 _
    have h2 : (ρ ^ (d - 1)) ^ 2 ≤ (B1 ^ (d - 1)) ^ 2 := pow_le_pow_left₀ (pow_pos hρ _).le h1 2
    have h3 : a ^ 2 * (ρ ^ (d - 1)) ^ 2 ≤ a ^ 2 * (B1 ^ (d - 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
    have e1 : a ^ 2 * ρ ^ (2 * (d - 1)) = a ^ 2 * (ρ ^ (d - 1)) ^ 2 := by ring
    have e2 : (a * B1 ^ (d - 1)) ^ 2 = a ^ 2 * (B1 ^ (d - 1)) ^ 2 := by ring
    rw [e1, e2]; exact h3
  have e3 : (2 * ρ) ^ (d - 1) * (4 * h * X + 4 * K ^ 2 / h * G) =
      2 * ((2 * h) * (2 * ρ) ^ (d - 1)) * X + 2 * ((2 * K ^ 2 / h) * (2 * ρ) ^ (d - 1)) * G := by
    ring
  have c1' := mul_le_mul_of_nonneg_left c1 (by norm_num : (0 : ℝ) ≤ 2)
  have c2' := mul_le_mul_of_nonneg_left c2 (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [hlow, hcore, c1', c2', e3]

theorem r3d_face_b (e : Fin d) (m : ℤ) {ρ h r K : ℝ} (hρ : 0 < ρ) (hh : 0 < h)
    (hhL : h < (3 : ℝ) ^ m / 2) (hρL : ρ < (3 : ℝ) ^ m / 2) (hρr : ρ ≤ r) (hhr : h ≤ r)
    (hK : ∀ t, |deriv (r3d_bump (r := 1) one_pos) t| ≤ K)
    (u : H1Function (openCubeSet (originCube d m)))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) u.toFun)
    (a : ℝ) (b : Vec d) {k : Fin d} (hk : k ≠ e) :
    b k ^ 2 * (ρ ^ 3 / 12) ^ 2 * ρ ^ (2 * (d - 1 - 1)) ≤
      (2 * ρ ^ 3) * (2 * ρ) ^ (d - 1 - 1) *
      (4 * h * (∫ x in r3d_Ebox e m r, u.grad x e ^ 2) +
        4 * K ^ 2 / h * ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2) := by
  classical
  set L : ℝ := (3 : ℝ) ^ m / 2 with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  set β : ℝ → ℝ := (r3d_bump hρ : ℝ → ℝ) with hβ
  set ψ : ℝ → ℝ := fun t => t * β t with hψ
  set Ψ : Fin d → ℝ → ℝ := fun i => if i = k then ψ else β with hΨ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_id.mul (r3d_bump_contDiff hρ)
  have hψk : HasCompactSupport ψ := r3d_psi_compact hρ
  have hψt : tsupport ψ ⊆ Set.Icc (-ρ) ρ :=
    (tsupport_mul_subset_right (f := fun t : ℝ => t) (g := β)).trans (r3d_bump_tsupport hρ)
  have hcore := r3d_face_core e m (ρ := ρ) (h := h) (r := r) (K := K) hh hhL hρL hρr hhr hK Ψ
    (fun i => by by_cases hi : i = k <;> simp [hΨ, hi, hψs, r3d_bump_contDiff hρ, hβ])
    (fun i => by by_cases hi : i = k <;> simp [hΨ, hi, hψk, r3d_bump_compact hρ, hβ])
    (fun i => by by_cases hi : i = k <;> simp [hΨ, hi, hψt, r3d_bump_tsupport hρ, hβ]) u hZ a b
  rw [← hL] at hcore
  have hB1 : ρ ≤ ∫ t in Set.Ioo (-L) L, β t :=
    r3d_bump_integral_ge hρ (by rw [hL] at hρL ⊢; linarith only [hρL])
  have hB2 : ρ ^ 3 / 12 ≤ ∫ t in Set.Ioo (-L) L, t * (t * β t) :=
    r3d_bump_integral_second_ge hρ (by rw [hL] at hρL ⊢; linarith only [hρL])
  have hodd : ∫ t in Set.Ioo (-L) L, t * β t = 0 := r3d_bump_integral_odd hLpos.le hρ
  set B1 : ℝ := ∫ t in Set.Ioo (-L) L, β t with hB1d
  set B2 : ℝ := ∫ t in Set.Ioo (-L) L, t * (t * β t) with hB2d
  have hkE : k ∈ Finset.univ.erase e := Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩
  have hΨk' : Ψ k = ψ := by simp [hΨ]
  have hΨne : ∀ i, i ≠ k → Ψ i = β := fun i hi => by simp [hΨ, hi]
  -- the first term vanishes
  have hfirst : ∏ i ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ i t = 0 :=
    Finset.prod_eq_zero hkE (by rw [hΨk']; exact hodd)
  -- the sum collapses to the term `k`
  have hsum : ∑ j ∈ Finset.univ.erase e, b j * ∏ i ∈ Finset.univ.erase e,
      (if i = j then (∫ t in Set.Ioo (-L) L, t * Ψ i t) else (∫ t in Set.Ioo (-L) L, Ψ i t)) =
      b k * (B2 * B1 ^ (d - 1 - 1)) := by
    rw [Finset.sum_eq_single k]
    · congr 1
      rw [← Finset.mul_prod_erase (Finset.univ.erase e) _ hkE]
      congr 1
      · simp [hΨk', hψ, hB2d]
      · rw [Finset.prod_congr rfl (g := fun _ => B1)]
        · rw [Finset.prod_const, r3d_card_erase_erase hkE]
        · intro i hi
          have hik : i ≠ k := (Finset.mem_erase.1 hi).1
          simp [hik, hΨne i hik, hB1d]
    · intro j hj hjk
      rw [Finset.prod_eq_zero hj, mul_zero]
      simp [hΨne j hjk, hodd]
    · intro hnot
      exact absurd hkE hnot
  rw [hfirst, hsum, mul_zero, zero_add] at hcore
  have hSg : ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 ≤
      (2 * ρ ^ 3) * (2 * ρ) ^ (d - 1 - 1) := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase e) _ hkE]
    have h1 : ∫ t in Set.Ioo (-L) L, Ψ k t ^ 2 ≤ 2 * ρ ^ 3 := by
      rw [hΨk']; exact r3d_bump_integral_psi_sq_le hρ
    have h2 : ∏ i ∈ (Finset.univ.erase e).erase k, ∫ t in Set.Ioo (-L) L, Ψ i t ^ 2 ≤
        (2 * ρ) ^ (d - 1 - 1) := by
      calc ∏ i ∈ (Finset.univ.erase e).erase k, ∫ t in Set.Ioo (-L) L, Ψ i t ^ 2
          ≤ ∏ _i ∈ (Finset.univ.erase e).erase k, (2 * ρ) :=
            Finset.prod_le_prod₀ (fun i _ => integral_nonneg fun t => sq_nonneg _)
              (fun i hi => by
                have hik : i ≠ k := (Finset.mem_erase.1 hi).1
                rw [hΨne i hik]; exact r3d_bump_integral_sq_le hρ)
        _ = (2 * ρ) ^ (d - 1 - 1) := by rw [Finset.prod_const, r3d_card_erase_erase hkE]
    have h3 : 0 ≤ ∫ t in Set.Ioo (-L) L, Ψ k t ^ 2 := integral_nonneg fun t => sq_nonneg _
    exact mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => integral_nonneg fun t => sq_nonneg _)
      (by positivity)
  have hX : 0 ≤ ∫ x in r3d_Ebox e m r, u.grad x e ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hG : 0 ≤ ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hK0 : 0 ≤ 2 * K ^ 2 / h := by positivity
  set Sg := ∏ j ∈ Finset.univ.erase e, ∫ t in Set.Ioo (-L) L, Ψ j t ^ 2 with hSgd
  set X := ∫ x in r3d_Ebox e m r, u.grad x e ^ 2 with hXd
  set G := ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 with hGd
  have c1 : (2 * h) * Sg * X ≤ (2 * h) * ((2 * ρ ^ 3) * (2 * ρ) ^ (d - 1 - 1)) * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSg (by positivity)) hX
  have c2 : (2 * K ^ 2 / h) * Sg * G ≤
      (2 * K ^ 2 / h) * ((2 * ρ ^ 3) * (2 * ρ) ^ (d - 1 - 1)) * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSg hK0) hG
  have hlow : b k ^ 2 * (ρ ^ 3 / 12) ^ 2 * ρ ^ (2 * (d - 1 - 1)) ≤ (b k * (B2 * B1 ^ (d - 1 - 1))) ^ 2 := by
    have h1 : ρ ^ (d - 1 - 1) ≤ B1 ^ (d - 1 - 1) := pow_le_pow_left₀ hρ.le hB1 _
    have h1' : ρ ^ 3 / 12 * ρ ^ (d - 1 - 1) ≤ B2 * B1 ^ (d - 1 - 1) :=
      mul_le_mul hB2 h1 (pow_pos hρ _).le (le_trans (by positivity) hB2)
    have h2 : (ρ ^ 3 / 12 * ρ ^ (d - 1 - 1)) ^ 2 ≤ (B2 * B1 ^ (d - 1 - 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1' 2
    have h3 : b k ^ 2 * (ρ ^ 3 / 12 * ρ ^ (d - 1 - 1)) ^ 2 ≤ b k ^ 2 * (B2 * B1 ^ (d - 1 - 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have e1 : b k ^ 2 * (ρ ^ 3 / 12) ^ 2 * ρ ^ (2 * (d - 1 - 1)) =
        b k ^ 2 * (ρ ^ 3 / 12 * ρ ^ (d - 1 - 1)) ^ 2 := by ring
    have e2 : (b k * (B2 * B1 ^ (d - 1 - 1))) ^ 2 = b k ^ 2 * (B2 * B1 ^ (d - 1 - 1)) ^ 2 := by ring
    rw [e1, e2]; exact h3
  have e3 : (2 * ρ ^ 3) * (2 * ρ) ^ (d - 1 - 1) * (4 * h * X + 4 * K ^ 2 / h * G) =
      2 * ((2 * h) * ((2 * ρ ^ 3) * (2 * ρ) ^ (d - 1 - 1))) * X +
        2 * ((2 * K ^ 2 / h) * ((2 * ρ ^ 3) * (2 * ρ) ^ (d - 1 - 1))) * G := by
    ring
  have c1' := mul_le_mul_of_nonneg_left c1 (by norm_num : (0 : ℝ) ≤ 2)
  have c2' := mul_le_mul_of_nonneg_left c2 (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [hlow, hcore, c1', c2', e3]

end SuperdiffusionCLT.Section7
