/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayE

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Control of the tangential affine part by the face energy

With `h` free and small, the face bounds for `a` and `b_k` give
`∫_Ω u² ≤ 2 ∫_Ω (u - m)² + C ℓ (h X + K² h⁻¹ ∫_Ω (u - m)²)`, `X` the gradient energy near the face.
-/

namespace SuperdiffusionCLT.Section7



/-- Rescaling of the face bound for `a`: `ρ = ℓ / 7`. -/
theorem r3d_pow_aux {ℓ W a2 : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (H : a2 * (ℓ / 7) ^ (2 * N) ≤ (2 * (ℓ / 7)) ^ N * W) :
    a2 * ℓ ^ (N + 1) ≤ 14 ^ N * ℓ * W := by
  set ℓ' : ℝ := ℓ / 7 with hℓ'
  have hℓ'0 : 0 < ℓ' := by positivity
  have hℓe : ℓ = 7 * ℓ' := by rw [hℓ']; ring
  have h1 : a2 * ℓ' ^ (2 * N) = (a2 * ℓ' ^ N) * ℓ' ^ N := by rw [two_mul, pow_add]; ring
  have h2 : (2 * ℓ') ^ N * W = (2 ^ N * W) * ℓ' ^ N := by rw [mul_pow]; ring
  rw [h1, h2] at H
  have h3 : a2 * ℓ' ^ N ≤ 2 ^ N * W := le_of_mul_le_mul_right H (pow_pos hℓ'0 N)
  rw [hℓe]
  have e1 : a2 * (7 * ℓ') ^ (N + 1) = (a2 * ℓ' ^ N) * (7 ^ (N + 1) * ℓ') := by
    rw [mul_pow, pow_succ ℓ']; ring
  have e2 : 14 ^ N * (7 * ℓ') * W = (2 ^ N * W) * (7 ^ (N + 1) * ℓ') := by
    have : (14 : ℝ) ^ N = 2 ^ N * 7 ^ N := by
      rw [← mul_pow]; norm_num
    rw [this, pow_succ 7]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right h3 (by positivity)

theorem r3d_pow_aux_b {ℓ W b2 : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (H : b2 * ((ℓ / 7) ^ 3 / 12) ^ 2 * (ℓ / 7) ^ (2 * n) ≤
      (2 * (ℓ / 7) ^ 3) * (2 * (ℓ / 7)) ^ n * W) :
    b2 * ℓ ^ (n + 4) ≤ 144 * 2 ^ (n + 1) * 7 ^ (n + 3) * ℓ * W := by
  set ρ : ℝ := ℓ / 7 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hℓe : ℓ = 7 * ρ := by rw [hρ]; ring
  have h1 : b2 * (ρ ^ 3 / 12) ^ 2 * ρ ^ (2 * n) = (b2 * ρ ^ (n + 3)) * ρ ^ (n + 3) / 144 := by
    have : ρ ^ (2 * n) * ρ ^ 6 = ρ ^ (n + 3) * ρ ^ (n + 3) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    calc b2 * (ρ ^ 3 / 12) ^ 2 * ρ ^ (2 * n) = b2 * (ρ ^ (2 * n) * ρ ^ 6) / 144 := by ring
      _ = _ := by rw [this]; ring
  have h2 : (2 * ρ ^ 3) * (2 * ρ) ^ n * W = (2 ^ (n + 1) * W) * ρ ^ (n + 3) := by
    rw [mul_pow, pow_succ 2, pow_add]; ring
  rw [h1, h2] at H
  have H2 : (b2 * ρ ^ (n + 3)) * ρ ^ (n + 3) ≤ (144 * 2 ^ (n + 1) * W) * ρ ^ (n + 3) := by
    linarith only [H]
  have h3 : b2 * ρ ^ (n + 3) ≤ 144 * 2 ^ (n + 1) * W := le_of_mul_le_mul_right H2 (pow_pos hρ0 _)
  rw [hℓe]
  have e1 : b2 * (7 * ρ) ^ (n + 4) = (b2 * ρ ^ (n + 3)) * (7 ^ (n + 4) * ρ) := by
    rw [mul_pow, pow_succ ρ (n + 3)]; ring
  have e2 : 144 * 2 ^ (n + 1) * 7 ^ (n + 3) * (7 * ρ) * W =
      (144 * 2 ^ (n + 1) * W) * (7 ^ (n + 4) * ρ) := by
    rw [pow_succ 7 (n + 3)]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right h3 (by positivity)


section
variable {d : ℕ}



theorem r3d_volume_openCube (m : ℤ) :
    (volume (openCubeSet (originCube d m))).toReal = ((3 : ℝ) ^ m) ^ d := by
  rw [r3d_openCube_eq_pi, Real.volume_pi_Ioo, ENNReal.toReal_prod]
  have : ∀ i : Fin d, (ENNReal.ofReal ((3 : ℝ) ^ m / 2 - -((3 : ℝ) ^ m / 2))).toReal = (3 : ℝ) ^ m := by
    intro i
    have h0 : (0 : ℝ) ≤ (3 : ℝ) ^ m / 2 - -((3 : ℝ) ^ m / 2) := by
      have := zpow_pos (by norm_num : (0 : ℝ) < 3) m
      linarith only [this]
    rw [ENNReal.toReal_ofReal h0]; ring
  rw [Finset.prod_congr rfl (fun i _ => this i)]
  simp

theorem r3d_volume_openCube_ne_top (m : ℤ) : volume (openCubeSet (originCube d m)) ≠ ⊤ := by
  rw [r3d_openCube_eq_pi, Real.volume_pi_Ioo]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- Pointwise bound of the tangential affine function on the cube. -/
theorem r3d_m_sq_le (e : Fin d) (m : ℤ) (a : ℝ) (b : Vec d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    r3d_m e a b x ^ 2 ≤ (|a| + (3 : ℝ) ^ m / 2 * ∑ k ∈ Finset.univ.erase e, |b k|) ^ 2 := by
  have h := r3d_m_abs_le e a b (L := (3 : ℝ) ^ m / 2) (x := x) (fun i => by
    have := (hc_mem_openCubeSet_originCube_iff m x).1 hx i
    rw [abs_le]; exact ⟨this.1.le, this.2.le⟩)
  calc r3d_m e a b x ^ 2 = |r3d_m e a b x| ^ 2 := (sq_abs _).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h 2


theorem r3d_F1 (hd : 2 ≤ d) (e : Fin d) (m : ℤ) {h K : ℝ} (hh : 0 < h)
    (hh3 : h ≤ (3 : ℝ) ^ m / 3) (hK : ∀ t, |deriv (r3d_bump (r := 1) one_pos) t| ≤ K)
    (u : H1Function (openCubeSet (originCube d m)))
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m)) (r3d_window e m) u.toFun)
    (a : ℝ) (b : Vec d) :
    ∫ x in openCubeSet (originCube d m), u.toFun x ^ 2 ≤
      2 * (∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2) +
        6 * (d : ℝ) ^ 2 * (144 * 2 ^ (d - 1) * 7 ^ (d + 1)) * (3 : ℝ) ^ m *
          (4 * h * (∫ x in r3d_Ebox e m ((3 : ℝ) ^ m / 3), u.grad x e ^ 2) +
            4 * K ^ 2 / h * ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2) := by
  classical
  set ℓ : ℝ := (3 : ℝ) ^ m with hℓd
  have hℓ : 0 < ℓ := zpow_pos (by norm_num) m
  obtain ⟨n, hn⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  have hN : d - 1 = n + 1 := by omega
  have hN2 : d - 1 - 1 = n := by omega
  set U : ℝ := ∫ x in openCubeSet (originCube d m), u.toFun x ^ 2 with hU
  set G2 : ℝ := ∫ x in openCubeSet (originCube d m), (u.toFun x - r3d_m e a b x) ^ 2 with hG2
  set X : ℝ := ∫ x in r3d_Ebox e m (ℓ / 3), u.grad x e ^ 2 with hX
  set W : ℝ := 4 * h * X + 4 * K ^ 2 / h * G2 with hW
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have hG0 : 0 ≤ G2 := integral_nonneg fun x => sq_nonneg _
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hh.le) hX0)
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hh.le) hG0)
  have hρ : (0 : ℝ) < ℓ / 7 := div_pos hℓ (by norm_num)
  have hρL : ℓ / 7 < ℓ / 2 := by linarith only [hℓ]
  have hρr : ℓ / 7 ≤ ℓ / 3 := by linarith only [hℓ]
  have hhL : h < ℓ / 2 := by linarith only [hh3, hℓ]
  have hhr : h ≤ ℓ / 3 := hh3
  have ha := r3d_face_a e m (ρ := ℓ / 7) (h := h) (r := ℓ / 3) (K := K) hρ hh hhL hρL hρr hhr hK u hZ a b
  rw [hN] at ha
  have ha' := r3d_pow_aux hℓ (n + 1) ha
  have hb : ∀ k ∈ Finset.univ.erase e, b k ^ 2 * ℓ ^ (n + 4) ≤
      144 * 2 ^ (n + 1) * 7 ^ (n + 3) * ℓ * W := by
    intro k hk
    have hke : k ≠ e := (Finset.mem_erase.1 hk).1
    have := r3d_face_b e m (ρ := ℓ / 7) (h := h) (r := ℓ / 3) (K := K) hρ hh hhL hρL hρr hhr hK u hZ
      a b hke
    rw [hN2] at this
    exact r3d_pow_aux_b hℓ n this
  -- the integral of `m²` over the cube
  set S1 : ℝ := ∑ k ∈ Finset.univ.erase e, |b k| with hS1
  set Mb : ℝ := (|a| + ℓ / 2 * S1) ^ 2 with hMb
  have hQo : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _
  have hQm : MeasurableSet (openCubeSet (originCube d m)) := hQo.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (r3d_volume_openCube_ne_top m)⟩
  have hmc : Continuous (r3d_m e a b) := r3d_m_continuous e a b
  have hmbd : ∀ x ∈ openCubeSet (originCube d m), r3d_m e a b x ^ 2 ≤ Mb := fun x hx =>
    r3d_m_sq_le e m a b hx
  have hmint : Integrable (fun x => r3d_m e a b x ^ 2) (volume.restrict (openCubeSet (originCube d m))) := by
    refine (integrable_const Mb).mono' (hmc.pow 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hmbd x hx
  have hmI : ∫ x in openCubeSet (originCube d m), r3d_m e a b x ^ 2 ≤ Mb * ℓ ^ d := by
    have h1 : ∫ x in openCubeSet (originCube d m), r3d_m e a b x ^ 2 ≤
        ∫ x in openCubeSet (originCube d m), Mb := by
      refine integral_mono_ae hmint (integrable_const _) ?_
      filter_upwards [ae_restrict_mem hQm] with x hx
      exact hmbd x hx
    have h2 : ∫ x in openCubeSet (originCube d m), Mb = Mb * ℓ ^ d := by
      rw [integral_const, smul_eq_mul]
      simp only [Measure.real, Measure.restrict_apply_univ]
      rw [r3d_volume_openCube m, mul_comm]
    linarith only [h1, h2]
  -- `u² ≤ 2 (u - m)² + 2 m²`
  have hu2 : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := u.memL2
  have hm2 : MemLp (r3d_m e a b) 2 (volume.restrict (openCubeSet (originCube d m))) :=
    MemLp.of_bound hmc.aestronglyMeasurable (|a| + ℓ / 2 * S1) (by
      filter_upwards [ae_restrict_mem hQm] with x hx
      rw [Real.norm_eq_abs]
      exact r3d_m_abs_le e a b (L := ℓ / 2) (fun i => by
        have := (hc_mem_openCubeSet_originCube_iff m x).1 hx i
        rw [abs_le]; exact ⟨this.1.le, this.2.le⟩))
  have hg2 : MemLp (fun x => u.toFun x - r3d_m e a b x) 2
      (volume.restrict (openCubeSet (originCube d m))) := hu2.sub hm2
  have hUle : U ≤ 2 * G2 + 2 * ∫ x in openCubeSet (originCube d m), r3d_m e a b x ^ 2 := by
    have h1 : ∫ x in openCubeSet (originCube d m), u.toFun x ^ 2 ≤
        ∫ x in openCubeSet (originCube d m),
          (2 * (u.toFun x - r3d_m e a b x) ^ 2 + 2 * r3d_m e a b x ^ 2) := by
      refine integral_mono hu2.integrable_sq ((hg2.integrable_sq.const_mul 2).add (hmint.const_mul 2)) fun x => ?_
      have : u.toFun x ^ 2 = (u.toFun x - r3d_m e a b x + r3d_m e a b x) ^ 2 := by ring
      rw [this]
      have h0 : 0 ≤ (u.toFun x - r3d_m e a b x - r3d_m e a b x) ^ 2 := sq_nonneg _
      linarith only [h0, show (u.toFun x - r3d_m e a b x + r3d_m e a b x) ^ 2 +
        (u.toFun x - r3d_m e a b x - r3d_m e a b x) ^ 2 =
        2 * (u.toFun x - r3d_m e a b x) ^ 2 + 2 * r3d_m e a b x ^ 2 by ring]
    rw [integral_add (hg2.integrable_sq.const_mul 2) (hmint.const_mul 2), integral_const_mul,
      integral_const_mul] at h1
    exact h1
  -- the algebra
  set C₁ : ℝ := 144 * 2 ^ (n + 1) * 7 ^ (n + 3) with hC₁
  have hC₁0 : 0 < C₁ :=
    mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _)) (pow_pos (by norm_num) _)
  have hP : ℓ ^ d = ℓ ^ (n + 1 + 1) := by rw [hn]
  have hQ : ℓ ^ (n + 4) = ℓ ^ d * ℓ ^ 2 := by rw [hn, ← pow_add]
  have hS1sq : S1 ^ 2 ≤ ((n : ℝ) + 1) * ∑ k ∈ Finset.univ.erase e, b k ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase e) (fun _ : Fin d => (1 : ℝ))
      (fun k => |b k|)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
    rw [r3d_card_erase, hN] at h
    simpa [hS1] using h
  have hMb2 : Mb ≤ 2 * a ^ 2 + ℓ ^ 2 / 2 * S1 ^ 2 := by
    have h0 : 0 ≤ (|a| - ℓ / 2 * S1) ^ 2 := sq_nonneg _
    have e1 : (|a| + ℓ / 2 * S1) ^ 2 + (|a| - ℓ / 2 * S1) ^ 2 = 2 * a ^ 2 + 2 * (ℓ / 2 * S1) ^ 2 := by
      have h1 : |a| ^ 2 = a ^ 2 := sq_abs a
      have h2 : (|a| + ℓ / 2 * S1) ^ 2 + (|a| - ℓ / 2 * S1) ^ 2 =
          2 * |a| ^ 2 + 2 * (ℓ / 2 * S1) ^ 2 := by ring
      rw [h2, h1]
    have e2 : 2 * (ℓ / 2 * S1) ^ 2 = ℓ ^ 2 / 2 * S1 ^ 2 := by ring
    rw [hMb]
    linarith only [h0, e1, e2]
  have hPnn : 0 ≤ ℓ ^ d := (pow_pos hℓ d).le
  have hMbP : Mb * ℓ ^ d ≤ 2 * (a ^ 2 * ℓ ^ d) +
      ((n : ℝ) + 1) / 2 * ∑ k ∈ Finset.univ.erase e, b k ^ 2 * ℓ ^ (n + 4) := by
    have h1 := mul_le_mul_of_nonneg_right hMb2 hPnn
    have h2 : ℓ ^ 2 / 2 * S1 ^ 2 * ℓ ^ d ≤ ℓ ^ 2 / 2 * (((n : ℝ) + 1) * ∑ k ∈ Finset.univ.erase e, b k ^ 2) * ℓ ^ d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS1sq (div_nonneg (sq_nonneg ℓ) (by norm_num))) hPnn
    have h3 : ℓ ^ 2 / 2 * (((n : ℝ) + 1) * ∑ k ∈ Finset.univ.erase e, b k ^ 2) * ℓ ^ d =
        ((n : ℝ) + 1) / 2 * ∑ k ∈ Finset.univ.erase e, b k ^ 2 * ℓ ^ (n + 4) := by
      rw [hQ, ← Finset.sum_mul]
      ring
    have h4 : (2 * a ^ 2 + ℓ ^ 2 / 2 * S1 ^ 2) * ℓ ^ d = 2 * (a ^ 2 * ℓ ^ d) + ℓ ^ 2 / 2 * S1 ^ 2 * ℓ ^ d := by ring
    linarith only [h1, h2, h3, h4]
  have hsumb : ∑ k ∈ Finset.univ.erase e, b k ^ 2 * ℓ ^ (n + 4) ≤ ((n : ℝ) + 1) * (C₁ * ℓ * W) := by
    calc ∑ k ∈ Finset.univ.erase e, b k ^ 2 * ℓ ^ (n + 4)
        ≤ ∑ _k ∈ Finset.univ.erase e, (C₁ * ℓ * W) := Finset.sum_le_sum fun k hk => by
          have := hb k hk
          rw [hC₁]; linarith only [this]
      _ = ((n : ℝ) + 1) * (C₁ * ℓ * W) := by
          rw [Finset.sum_const, r3d_card_erase, hN]; simp
  have h14 : (14 : ℝ) ^ (n + 1) ≤ C₁ := by
    rw [hC₁]
    have : (14 : ℝ) ^ (n + 1) = 2 ^ (n + 1) * 7 ^ (n + 1) := by rw [← mul_pow]; norm_num
    rw [this]
    have h7 : (7 : ℝ) ^ (n + 1) ≤ 7 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (0 : ℝ) < 2 ^ (n + 1) := pow_pos (by norm_num) _
    calc 2 ^ (n + 1) * 7 ^ (n + 1) ≤ 2 ^ (n + 1) * 7 ^ (n + 3) := mul_le_mul_of_nonneg_left h7 h2.le
      _ ≤ 144 * 2 ^ (n + 1) * 7 ^ (n + 3) := by
          have : 0 ≤ (2 : ℝ) ^ (n + 1) * 7 ^ (n + 3) :=
            mul_nonneg h2.le (pow_nonneg (by norm_num) _)
          linarith only [this]
  have haP : a ^ 2 * ℓ ^ d ≤ C₁ * ℓ * W := by
    rw [hP]
    calc a ^ 2 * ℓ ^ (n + 1 + 1) ≤ 14 ^ (n + 1) * ℓ * W := ha'
      _ ≤ C₁ * ℓ * W := by
          have h0 : 0 ≤ ℓ * W := mul_nonneg hℓ.le hW0
          have h1 := mul_le_mul_of_nonneg_right h14 h0
          have e1 : (14 : ℝ) ^ (n + 1) * (ℓ * W) = 14 ^ (n + 1) * ℓ * W := by ring
          have e2 : C₁ * (ℓ * W) = C₁ * ℓ * W := by ring
          linarith only [h1, e1, e2]
  have hMbF : Mb * ℓ ^ d ≤ 3 * ((n : ℝ) + 2) ^ 2 * (C₁ * ℓ * W) := by
    have h1 : 2 * (a ^ 2 * ℓ ^ d) ≤ 2 * (C₁ * ℓ * W) := by linarith only [haP]
    have h2 : ((n : ℝ) + 1) / 2 * ∑ k ∈ Finset.univ.erase e, b k ^ 2 * ℓ ^ (n + 4) ≤
        ((n : ℝ) + 1) / 2 * (((n : ℝ) + 1) * (C₁ * ℓ * W)) :=
      mul_le_mul_of_nonneg_left hsumb
        (div_nonneg (add_nonneg (Nat.cast_nonneg n) zero_le_one) (by norm_num))
    have hCW : 0 ≤ C₁ * ℓ * W := mul_nonneg (mul_nonneg hC₁0.le hℓ.le) hW0
    have h3 : 2 * (C₁ * ℓ * W) + ((n : ℝ) + 1) / 2 * (((n : ℝ) + 1) * (C₁ * ℓ * W)) ≤
        3 * ((n : ℝ) + 2) ^ 2 * (C₁ * ℓ * W) := by
      have : 2 + ((n : ℝ) + 1) / 2 * ((n : ℝ) + 1) ≤ 3 * ((n : ℝ) + 2) ^ 2 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith only [sq_nonneg (n : ℝ), hn0]
      have h := mul_le_mul_of_nonneg_right this hCW
      linarith only [h]
    linarith only [hMbP, h1, h2, h3]
  have hfin2 : U ≤ 2 * G2 + 2 * (3 * ((n : ℝ) + 2) ^ 2 * (C₁ * ℓ * W)) := by
    have := hmI.trans hMbF
    linarith only [hUle, this]
  have hdn : (d : ℝ) = (n : ℝ) + 2 := by rw [hn]; push_cast; ring
  have e144 : (144 : ℝ) * 2 ^ (d - 1) * 7 ^ (d + 1) = C₁ := by
    rw [hC₁, hN, hn]
  rw [e144, hdn]
  linarith only [hfin2]

end

end SuperdiffusionCLT.Section7
