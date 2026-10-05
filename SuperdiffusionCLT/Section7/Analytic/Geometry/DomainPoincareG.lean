/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.BoundaryRoundedJ

/-!
# Poincare inequalities: the model domain of the boundary family

`Section7.a10_isStarBallDomain_H`: the model domain `g1b_H e 1 1` is star-shaped with respect to
every point of a cube around its centre `-e`. The profile `phi` vanishes on `[0, 1/16]` and is
monotone, so a convex combination of a point of the domain with a point near the centre does not
increase either coordinate of the defining function beyond the point itself.
-/

@[expose] public section

open MeasureTheory Homogenization Set

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem a10_vecNormSq_convex (p q : Vec d) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hat : a + t = 1) :
    vecNormSq (a • p + t • q) ≤ a * vecNormSq p + t * vecNormSq q := by
  unfold vecNormSq vecDot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : a = 1 - t := by linarith only [hat]
  subst h1
  nlinarith only [sq_nonneg (p i - q i), mul_nonneg ha ht]

theorem a10_sq_convex (x y : ℝ) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hat : a + t = 1) :
    (a * x + t * y) ^ 2 ≤ a * x ^ 2 + t * y ^ 2 := by
  have h1 : a = 1 - t := by linarith only [hat]
  subst h1
  nlinarith only [sq_nonneg (x - y), mul_nonneg ha ht]

theorem a10_phi_step {Ux Ud Uy t : ℝ} (hUy : 0 ≤ Uy) (hUx : 0 ≤ Ux) (hUd : Ud ≤ 1 / 16)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hle : Uy ≤ (1 - t) * Ux + t * Ud) :
    g1b_phi Uy ≤ g1b_phi Ux := by
  by_cases h : Uy ≤ Ux
  · exact g1b_phi_mono hUy h
  · have hlt : Ux < Uy := not_le.1 h
    have hdx : Ux < Ud := by
      by_contra hc
      have hc' : Ud ≤ Ux := not_lt.1 hc
      nlinarith only [hle, hc', ht0, ht1, hlt]
    have hy : Uy ≤ Ud := by nlinarith only [hle, hdx, ht0, ht1]
    rw [g1b_phi_zero (hy.trans hUd)]
    exact g1b_phi_nonneg hUx

theorem a10_H_small {e : Vec d} (he : vecNormSq e = 1) {b : Vec d}
    (hb : ‖b - ((-1 : ℝ) • e)‖ < 1 / (4 * ((d : ℝ) + 1))) :
    vecNormSq (b - vecDot e b • e) ≤ 1 / 16 ∧ (vecDot e b + 1) ^ 2 ≤ 1 / 16 := by
  set δ : Vec d := b - ((-1 : ℝ) • e) with hδ
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hδsq : vecNormSq δ ≤ 1 / 16 := by
    refine (a10_vecNormSq_le δ).trans ?_
    have h0 : 0 ≤ ‖δ‖ := norm_nonneg _
    have h1 : ‖δ‖ ^ 2 ≤ (1 / (4 * ((d : ℝ) + 1))) ^ 2 := pow_le_pow_left₀ h0 hb.le 2
    have h2 : (d : ℝ) * (1 / (4 * ((d : ℝ) + 1))) ^ 2 ≤ 1 / 16 := by
      rw [div_pow, one_pow, mul_pow, ← mul_div_assoc, mul_one,
        div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [Nat.cast_nonneg (α := ℝ) d]
    calc (d : ℝ) * ‖δ‖ ^ 2 ≤ (d : ℝ) * (1 / (4 * ((d : ℝ) + 1))) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
      _ ≤ 1 / 16 := h2
  have hbδ : b = δ - (1 : ℝ) • e := by
    ext i
    simp [hδ]
  have hee : vecDot e e = 1 := he
  have hdot : vecDot e b = vecDot e δ - 1 := by
    rw [hbδ, g1b_vecDot_sub_smul_right, hee]
    ring
  have hnb : vecNormSq b = vecNormSq δ - 2 * vecDot e δ + 1 := by
    rw [hbδ, g1b_normSq_sub_smul, he]
    ring
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq e δ
  rw [he, one_mul] at hcs
  refine ⟨?_, ?_⟩
  · rw [g1b_normSq_proj he, hnb, hdot]
    nlinarith only [hδsq, sq_nonneg (vecDot e δ)]
  · rw [hdot]
    have : (vecDot e δ - 1 + 1) ^ 2 = vecDot e δ ^ 2 := by ring
    rw [this]
    linarith only [hcs, hδsq]

theorem a10_proj_comb {e : Vec d} (x b : Vec d) (a t : ℝ) :
    (a • x + t • b) - vecDot e (a • x + t • b) • e =
      a • (x - vecDot e x • e) + t • (b - vecDot e b • e) := by
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, g1b_vecDot_comb]
  ring

/-- The model domain is star-shaped with respect to a cube around its centre. -/
theorem a10_isStarBallDomain_H {e : Vec d} (he : vecNormSq e = 1) :
    IsStarBallDomain (g1b_H e 1 1) ((-1 : ℝ) • e) (1 / (4 * ((d : ℝ) + 1))) 6 := by
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hQ : ∀ y : Vec d, g1b_Q e 1 1 y = g1b_phi (vecNormSq (y - vecDot e y • e)) +
      g1b_phi ((vecDot e y + 1) ^ 2) := fun y => by
    simp [g1b_Q, g1b_u, g1b_v]
  have hball : Metric.ball ((-1 : ℝ) • e) (1 / (4 * ((d : ℝ) + 1))) ⊆ g1b_H e 1 1 := by
    intro b hb
    rw [Metric.mem_ball, dist_eq_norm] at hb
    obtain ⟨h1, h2⟩ := a10_H_small he hb
    show g1b_Q e 1 1 b < 1
    rw [hQ, g1b_phi_zero h1, g1b_phi_zero h2]
    norm_num
  refine ⟨g1b_isOpen_H e 1 1, by positivity, hball, ?_, ?_⟩
  · intro x hx b hb t ht
    rw [Metric.mem_ball, dist_eq_norm] at hb
    obtain ⟨h1, h2⟩ := a10_H_small he hb
    have hxQ : g1b_Q e 1 1 x < 1 := hx
    rw [hQ] at hxQ
    show g1b_Q e 1 1 ((1 - t) • x + t • b) < 1
    rw [hQ]
    have ht0 := ht.1
    have ht1 := ht.2
    have hat : (1 - t) + t = 1 := by ring
    have hu : vecNormSq (((1 - t) • x + t • b) - vecDot e ((1 - t) • x + t • b) • e) ≤
        (1 - t) * vecNormSq (x - vecDot e x • e) + t * vecNormSq (b - vecDot e b • e) := by
      rw [a10_proj_comb]
      exact a10_vecNormSq_convex _ _ (by linarith only [ht1]) ht0 hat
    have hv : (vecDot e ((1 - t) • x + t • b) + 1) ^ 2 ≤
        (1 - t) * (vecDot e x + 1) ^ 2 + t * (vecDot e b + 1) ^ 2 := by
      have : vecDot e ((1 - t) • x + t • b) + 1 =
          (1 - t) * (vecDot e x + 1) + t * (vecDot e b + 1) := by
        rw [g1b_vecDot_comb]; ring
      rw [this]
      exact a10_sq_convex _ _ (by linarith only [ht1]) ht0 hat
    have hu0 : 0 ≤ vecNormSq (((1 - t) • x + t • b) - vecDot e ((1 - t) • x + t • b) • e) := by
      unfold vecNormSq vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hx0 : 0 ≤ vecNormSq (x - vecDot e x • e) := by
      unfold vecNormSq vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have e1 := a10_phi_step hu0 hx0 h1 ht0 ht1 hu
    have e2 := a10_phi_step (sq_nonneg _) (sq_nonneg (vecDot e x + 1)) h2 ht0 ht1 hv
    linarith only [e1, e2, hxQ]
  · intro x hx y hy
    have hx' := g1b_abs_le_of_mem_H he (a := 1) (h := 1) one_pos one_pos hx
    have hy' := g1b_abs_le_of_mem_H he (a := 1) (h := 1) one_pos one_pos hy
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    have h1 := abs_le.1 (hx' i)
    have h2 := abs_le.1 (hy' i)
    rw [abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

end SuperdiffusionCLT.Section7
