/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedE

/-!
# The model domain is bounded and connected

* `Section7.g1b_isBoundedDomain_H`: `H` lies in the cube of half-width `a + 2h`.
* `Section7.g1b_isConnected_H`: `H` is star-shaped about `-h e`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization

variable {d : ℕ}

theorem g1b_abs_le_of_mem_H {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} (ha : 0 < a)
    (hh : 0 < h) {y : Vec d} (hy : y ∈ g1b_H e a h) (i : Fin d) : |y i| ≤ a + 2 * h := by
  obtain ⟨hu, hv⟩ := g1b_mem_H_iff_lt hy
  have h1 : vecNormSq (y - vecDot e y • e) < a ^ 2 := by
    unfold g1b_u at hu
    have := (div_lt_one (by positivity)).1 hu
    exact this
  have h2 : (vecDot e y + h) ^ 2 < h ^ 2 := by
    unfold g1b_v at hv
    exact (div_lt_one (by positivity)).1 hv
  have h3 : |(y - vecDot e y • e) i| < a := by
    refine abs_lt_of_sq_lt_sq ?_ ha.le
    have := sq_apply_le_vecNormSq (y - vecDot e y • e) i
    linarith only [this, h1]
  have h4 : |vecDot e y + h| < h := abs_lt_of_sq_lt_sq h2 hh.le
  have h5 : |vecDot e y| < 2 * h := by
    rw [abs_lt] at h4 ⊢
    constructor <;> linarith only [h4.1, h4.2]
  have h6 : |e i| ≤ 1 := abs_apply_le_one he i
  have h7 : y i = (y - vecDot e y • e) i + vecDot e y * e i := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h7]
  calc |(y - vecDot e y • e) i + vecDot e y * e i|
      ≤ |(y - vecDot e y • e) i| + |vecDot e y * e i| := abs_add_le _ _
    _ ≤ a + 2 * h := by
        rw [abs_mul]
        have : |vecDot e y| * |e i| ≤ (2 * h) * 1 :=
          mul_le_mul h5.le h6 (abs_nonneg _) (by linarith only [hh])
        linarith only [h3, this]

theorem g1b_isBoundedDomain_H {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} (ha : 0 < a)
    (hh : 0 < h) : IsBoundedDomain (g1b_H e a h) :=
  ⟨a + 2 * h, by linarith only [ha, hh], fun _ hy i => g1b_abs_le_of_mem_H he ha hh hy i⟩

theorem g1b_vecDot_comb (e x y : Vec d) (a b : ℝ) :
    vecDot e (a • x + b • y) = a * vecDot e x + b * vecDot e y := by
  simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem g1b_vecNormSq_smul' (t : ℝ) (w : Vec d) : vecNormSq (t • w) = t ^ 2 * vecNormSq w := by
  simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g1b_vecDot_smul_self {e : Vec d} (he : vecNormSq e = 1) (c : ℝ) :
    vecDot e (c • e) = c := by
  have := g1b_vecDot_comb e e e c 0
  rw [zero_smul, add_zero, zero_mul, add_zero] at this
  rw [this]
  have h3 : vecNormSq e = vecDot e e := rfl
  rw [← h3, he, mul_one]

theorem g1b_star_aux {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} {y : Vec d} (hy : y ∈ g1b_H e a h) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) : s • ((-h) • e) + t • y ∈ g1b_H e a h := by
  have hs' : s = 1 - t := by linarith only [hst]
  subst hs'
  have hdot : vecDot e ((1 - t) • ((-h) • e) + t • y) = (1 - t) * (-h) + t * vecDot e y := by
    rw [g1b_vecDot_comb, g1b_vecDot_smul_self he]
  have hproj : ((1 - t) • ((-h) • e) + t • y)
      - vecDot e ((1 - t) • ((-h) • e) + t • y) • e = t • (y - vecDot e y • e) := by
    rw [hdot]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  show g1b_Q e a h ((1 - t) • ((-h) • e) + t • y) < 1
  have hu : g1b_u e a ((1 - t) • ((-h) • e) + t • y) = t ^ 2 * g1b_u e a y := by
    unfold g1b_u
    rw [hproj, g1b_vecNormSq_smul']
    ring
  have hv : g1b_v e h ((1 - t) • ((-h) • e) + t • y) = t ^ 2 * g1b_v e h y := by
    unfold g1b_v
    rw [hdot]
    ring
  have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht, hs]
  have hq1 : g1b_phi (t ^ 2 * g1b_u e a y) ≤ g1b_phi (g1b_u e a y) :=
    g1b_phi_mono (mul_nonneg (sq_nonneg _) (g1b_u_nonneg e y))
      (by nlinarith only [ht2, g1b_u_nonneg (a := a) e y])
  have hq2 : g1b_phi (t ^ 2 * g1b_v e h y) ≤ g1b_phi (g1b_v e h y) :=
    g1b_phi_mono (mul_nonneg (sq_nonneg _) (g1b_v_nonneg e h y))
      (by nlinarith only [ht2, g1b_v_nonneg e h y])
  have h1 : g1b_Q e a h y < 1 := hy
  unfold g1b_Q at h1 ⊢
  rw [hu, hv]
  linarith only [hq1, hq2, h1]

theorem g1b_isConnected_H {e : Vec d} (he : vecNormSq e = 1) {a h : ℝ} : IsConnected (g1b_H e a h) := by
  have h0 : (-h) • e ∈ g1b_H e a h := by
    show g1b_Q e a h ((-h) • e) < 1
    unfold g1b_Q g1b_u g1b_v
    rw [g1b_vecDot_smul_self he]
    have : (-h) • e - (-h) • e = (0 : Vec d) := sub_self _
    rw [this]
    simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_div,
      neg_add_cancel]
    rw [g1b_phi_zero (by norm_num)]
    norm_num
    rw [g1b_phi_zero (by norm_num)]
    norm_num
  have hstar : StarConvex ℝ ((-h) • e) (g1b_H e a h) := by
    intro y hy s t hs ht hst
    exact g1b_star_aux he hy hs ht hst
  exact (hstar.isPathConnected h0).isConnected

end SuperdiffusionCLT.Section7
