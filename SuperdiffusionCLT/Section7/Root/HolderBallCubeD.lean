/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderBallCube
public import SuperdiffusionCLT.Section7.Root.HolderBallCubeB
public import SuperdiffusionCLT.Section7.Root.HolderBallCubeC

/-!
# Volumes of cubes and balls, and oscillation about the average

Support for the cube-to-ball passage in the large-scale Hölder theorem: volumes of the sup-norm
cubes `h1_cube y n` and of Euclidean balls, and the elementary fact that the `L^∞` oscillation about
the average on a set is at most twice the `L^∞` distance to any constant.

## Main results

* `SuperdiffusionCLT.Section7.h1_osc_two`
* `SuperdiffusionCLT.Section7.h1_ratio_le`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory SuperdiffusionCLT.Section6

variable {d : ℕ}

theorem h1_vol_cube (y : Vec d) (n : ℕ) :
    volume (h1_cube y n) = ENNReal.ofReal (((3 : ℝ) ^ n) ^ d) := by
  unfold h1_cube
  rw [Real.volume_pi_ball _ (by positivity)]
  simp only [Fintype.card_fin]
  rw [mul_div_cancel₀ _ (two_ne_zero)]

theorem h1_volT_cube (y : Vec d) (n : ℕ) :
    (volume (h1_cube y n)).toReal = ((3 : ℝ) ^ n) ^ d := by
  rw [h1_vol_cube, ENNReal.toReal_ofReal (by positivity)]

theorem h1_vol_cube_ne_top (y : Vec d) (n : ℕ) : volume (h1_cube y n) ≠ ⊤ := by
  rw [h1_vol_cube]; exact ENNReal.ofReal_ne_top

theorem h1_vol_ball_le {R : ℝ} (hR : 0 < R) :
    (volume (euclidBall (d := d) R)).toReal ≤ (2 * R) ^ d := by
  have h : volume (euclidBall (d := d) R) ≤ ENNReal.ofReal ((2 * R) ^ d) := by
    calc volume (euclidBall (d := d) R) ≤ volume (Metric.ball (0 : Vec d) R) :=
          measure_mono (euclidBall_subset_ball hR)
      _ = ENNReal.ofReal ((2 * R) ^ d) := by rw [Real.volume_pi_ball _ hR]; simp
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-- Volume ratio of a cube inside a ball. -/
theorem h1_ratio_le {R : ℝ} (hR : 0 < R) (y : Vec d) (n : ℕ) :
    (volume (euclidBall (d := d) R)).toReal / (volume (h1_cube y n)).toReal ≤
      (2 * R / (3 : ℝ) ^ n) ^ d := by
  rw [h1_volT_cube, div_pow]
  exact div_le_div_of_nonneg_right (h1_vol_ball_le hR) (by positivity)

theorem h1_vol_cube_pos (y : Vec d) (n : ℕ) : 0 < (volume (h1_cube y n)).toReal := by
  rw [h1_volT_cube]; positivity

theorem h1_vol_ball_ne_top {R : ℝ} (hR : 0 < R) : volume (euclidBall (d := d) R) ≠ ⊤ :=
  volume_euclidBall_ne_top hR

theorem h1_finite_restrict {S : Set (Vec d)} (hS : volume S ≠ ⊤) :
    IsFiniteMeasure (volume.restrict S) :=
  ⟨by simpa [Measure.restrict_apply_univ] using hS.lt_top⟩

/-- Oscillation about the average is at most twice the distance to any constant. -/
theorem h1_osc_two {A : Set (Vec d)} {u : Vec d → ℝ} {c M : ℝ} (hA : volume A ≠ ⊤)
    (hv : 0 < (volume A).toReal) (hu : MemLp u ⊤ (volume.restrict A)) (hM : 0 ≤ M)
    (h : ∀ᵐ x ∂volume.restrict A, |u x - c| ≤ M) : h1_linf A u (h1_avg A u) ≤ 2 * M := by
  have hfin := h1_finite_restrict hA
  have hu2 : MemLp u 2 (volume.restrict A) := hu.mono_exponent le_top
  have hint : Integrable u (volume.restrict A) := hu2.integrable (by norm_num)
  have h1 : ‖∫ x in A, (u x - c)‖ ≤ M * (volume A).toReal := by
    have := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (f := fun x => u x - c)
      (s := A) (C := M) hA.lt_top (by simpa only [Real.norm_eq_abs] using h)
    simpa [Measure.real] using this
  have h2 : ∫ x in A, (u x - c) = (∫ x in A, u x) - c * (volume A).toReal := by
    rw [integral_sub hint (integrable_const c), setIntegral_const]
    simp [Measure.real, mul_comm]
  have h3 : |h1_avg A u - c| ≤ M := by
    have e : h1_avg A u - c = (∫ x in A, (u x - c)) / (volume A).toReal := by
      rw [h2]; unfold h1_avg; field_simp
    rw [e, abs_div, abs_of_pos hv, div_le_iff₀ hv]
    simpa [Real.norm_eq_abs] using h1
  refine h1_linf_le_of_ae hu.aestronglyMeasurable (by linarith only [hM]) ?_
  filter_upwards [h] with x hx
  have : |u x - h1_avg A u| ≤ |u x - c| + |h1_avg A u - c| := by
    have := abs_add_le (u x - c) (c - h1_avg A u)
    rw [abs_sub_comm c] at this
    simpa using this
  linarith only [this, hx, h3]

theorem h1_memLp_sub {A B : Set (Vec d)} (hAB : A ⊆ B) (hB : volume B ≠ ⊤) {u : Vec d → ℝ}
    (hu : MemLp u ⊤ (volume.restrict B)) (c : ℝ) :
    MemLp (fun x => u x - c) ⊤ (volume.restrict A) := by
  have hA : volume A ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono hAB)
  have := h1_finite_restrict hA
  exact (hu.mono_measure (Measure.restrict_mono hAB le_rfl)).sub (memLp_const c)

theorem h1_memLp_mono {A B : Set (Vec d)} (hAB : A ⊆ B) {u : Vec d → ℝ}
    (hu : MemLp u ⊤ (volume.restrict B)) : MemLp u ⊤ (volume.restrict A) :=
  hu.mono_measure (Measure.restrict_mono hAB le_rfl)

/-- Deviation of `u` from the average over `B` on a subset `A`. -/
theorem h1_dev_bound {A B : Set (Vec d)} (hAB : A ⊆ B) (hB : volume B ≠ ⊤)
    (hv : 0 < (volume A).toReal) {u : Vec d → ℝ} (hu : MemLp u ⊤ (volume.restrict B)) :
    ∀ᵐ x ∂volume.restrict A, |u x - h1_avg B u| ≤
      h1_linf A u (h1_avg A u) +
        Real.sqrt ((volume B).toReal / (volume A).toReal) * h1_l2 B u := by
  have h1 := h1_ae_le_linf (h1_memLp_sub hAB hB hu (h1_avg A u))
  have h2 := h1_avg_sub_le hAB (h1_memLp_two_of_top hB hu) hB hv
  filter_upwards [h1] with x hx
  have : |u x - h1_avg B u| ≤ |u x - h1_avg A u| + |h1_avg A u - h1_avg B u| := by
    have := abs_add_le (u x - h1_avg A u) (h1_avg A u - h1_avg B u)
    simpa using this
  linarith only [this, hx, h2]


theorem h1_sqrt_d_pos [NeZero d] : 1 ≤ Real.sqrt d := by
  have : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  exact Real.one_le_sqrt.2 this

theorem h1_sqrt_le_self {K : ℝ} (hK : 1 ≤ K) : Real.sqrt K ≤ K :=
  Real.sqrt_le_iff.2 ⟨by linarith only [hK], by nlinarith only [hK]⟩

/-- Small radii: centred cubes `B_r ⊆ □_n ⊆ □_m ⊆ B_R` with `3^n ≈ 2r`, `3^m ≈ 2R/√d`. -/
theorem h1_regime_small [NeZero d] {R r γ C₁ G : ℝ} {m₀ : ℕ} {u : Vec d → ℝ}
    (hR : 0 < R) (hu : MemLp u ⊤ (volume.restrict (euclidBall (d := d) R)))
    (hγ : 0 ≤ γ) (hC₁ : 0 ≤ C₁) (hG : 0 ≤ G)
    (hr0 : (3 : ℝ) ^ m₀ ≤ 2 * r) (hrR : 9 * Real.sqrt d * r ≤ R)
    (H : ∀ n m : ℕ, m₀ ≤ n → n < m → h1_cube (0 : Vec d) m ⊆ euclidBall (d := d) R →
      h1_linf (h1_cube 0 n) u (h1_avg (h1_cube 0 n) u) ≤
        C₁ * (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) * (h1_l2 (h1_cube 0 m) u + G)) :
    h1_linf (euclidBall (d := d) r) u (h1_avg (euclidBall (d := d) r) u) ≤
      2 * C₁ * (9 * Real.sqrt d) ^ γ * (3 * Real.sqrt d) ^ d * (r / R) ^ γ *
        (h1_l2 (euclidBall (d := d) R) u + G) := by
  have hsd := h1_sqrt_d_pos (d := d)
  have hr1 : 1 ≤ 2 * r := le_trans (one_le_pow₀ (by norm_num)) hr0
  have hrpos : 0 < r := by linarith only [hr1]
  obtain ⟨n, hn1, hn2⟩ := h1_exists_outer (r := r) (by linarith only [hr1])
  have hRbig : Real.sqrt d ≤ 2 * R := by nlinarith only [hrR, hsd, hr1]
  have hs1 : 1 ≤ 2 * R / Real.sqrt d := by
    rw [le_div_iff₀ (by linarith only [hsd])]; linarith only [hRbig]
  obtain ⟨m, hm1, hm2⟩ := h1_exists_inner hs1
  set T := 2 * R / Real.sqrt d with hT
  have hRT : R = T * Real.sqrt d / 2 := by rw [hT]; field_simp
  have hrT : r ≤ T / 18 := by
    have : 9 * Real.sqrt d * r ≤ T * Real.sqrt d / 2 := by rw [← hRT]; exact hrR
    nlinarith only [this, hsd]
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hnm : n < m := by
    have : (3 : ℝ) ^ n < (3 : ℝ) ^ m := by
      rw [pow_succ] at hm2; linarith only [hn2, hrT, hm2]
    exact (pow_lt_pow_iff_right₀ (by norm_num)).1 this
  have hm₀n : m₀ ≤ n := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 (hr0.trans hn1)
  have hrR' : r ≤ R := by nlinarith only [hrR, hsd, hrpos]
  have hcubeM : h1_cube (0 : Vec d) m ⊆ euclidBall (d := d) R := by
    intro x hx
    have h0 : Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) ⊆
        euclidBall (Real.sqrt d * ((3 : ℝ) ^ m / 2)) := ball_subset_euclidBall
    refine euclidBall_mono (by positivity) ?_ (h0 hx)
    have : Real.sqrt d * (3 : ℝ) ^ m ≤ 2 * R := by
      have := mul_le_mul_of_nonneg_left hm1 (by positivity : 0 ≤ Real.sqrt d)
      rw [hT, mul_div_cancel₀ _ (by positivity)] at this; exact this
    linarith only [this]
  have hBR : euclidBall (d := d) r ⊆ euclidBall (d := d) R := euclidBall_mono hrpos.le hrR'
  have hBrC : euclidBall (d := d) r ⊆ h1_cube (0 : Vec d) n := by
    intro x hx
    have := euclidBall_subset_ball hrpos hx
    unfold h1_cube
    exact Metric.ball_subset_ball (by linarith only [hn1]) this
  have hCsubR : h1_cube (0 : Vec d) n ⊆ euclidBall (d := d) R := by
    refine (Metric.ball_subset_ball ?_).trans hcubeM
    have : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hnm.le
    linarith only [this]
  have hHn := H n m hm₀n hnm hcubeM
  have hfin : volume (euclidBall (d := d) R) ≠ ⊤ := h1_vol_ball_ne_top hR
  have hMnn : 0 ≤ h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) :=
    ENNReal.toReal_nonneg
  -- oscillation on the ball
  have hvr : 0 < (volume (euclidBall (d := d) r)).toReal :=
    ENNReal.toReal_pos (volume_euclidBall_ne_zero hrpos) (h1_vol_ball_ne_top hrpos)
  have hae : ∀ᵐ x ∂volume.restrict (euclidBall (d := d) r),
      |u x - h1_avg (h1_cube (0 : Vec d) n) u| ≤
        h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) := by
    have h1 := h1_ae_le_linf (h1_memLp_sub hCsubR hfin hu (h1_avg (h1_cube (0 : Vec d) n) u))
    exact (ae_mono (Measure.restrict_mono hBrC le_rfl)) h1
  have hosc := h1_osc_two (h1_vol_ball_ne_top hrpos) hvr
    (h1_memLp_mono hBR hu) hMnn hae
  -- the L² factor
  have hK1 : 1 ≤ (3 * Real.sqrt d) ^ d :=
    one_le_pow₀ (by linarith only [hsd])
  have hratio : (volume (euclidBall (d := d) R)).toReal / (volume (h1_cube (0 : Vec d) m)).toReal ≤
      (3 * Real.sqrt d) ^ d := by
    refine (h1_ratio_le hR 0 m).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ d
    rw [div_le_iff₀ h3pos]
    have : T < 3 * (3 : ℝ) ^ m := by rw [pow_succ] at hm2; linarith only [hm2]
    rw [hT] at this
    rw [div_lt_iff₀ (by positivity)] at this
    nlinarith only [this, hsd]
  have hl2 := h1_l2_le hcubeM (h1_memLp_two_of_top hfin hu) hfin (h1_vol_cube_pos 0 m)
  have hl2B : 0 ≤ h1_l2 (euclidBall (d := d) R) u := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((volume (euclidBall (d := d) R)).toReal /
      (volume (h1_cube (0 : Vec d) m)).toReal) ≤ (3 * Real.sqrt d) ^ d :=
    (Real.sqrt_le_sqrt hratio).trans (h1_sqrt_le_self hK1)
  have hl2' : h1_l2 (h1_cube (0 : Vec d) m) u ≤ (3 * Real.sqrt d) ^ d * h1_l2 (euclidBall (d := d) R) u :=
    hl2.trans (mul_le_mul_of_nonneg_right hsq hl2B)
  -- the rate
  have hrate : (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) ≤ (9 * Real.sqrt d) ^ γ * (r / R) ^ γ := by
    have := h1_rate (γ := γ) (κ := 9 * Real.sqrt d) (r := r) (R := R) hγ (by positivity)
      hrpos.le hR (n : ℤ) (m : ℤ) (by
        rw [zpow_natCast, zpow_natCast, div_le_iff₀ h3pos]
        have : T < 3 * (3 : ℝ) ^ m := by rw [pow_succ] at hm2; linarith only [hm2]
        have e : 2 * R = T * Real.sqrt d := by rw [hT]; field_simp
        have hRr : R ≥ 9 * Real.sqrt d * r := hrR
        have hq : 0 < r / R := by positivity
        have e : 9 * Real.sqrt d * (r / R) * (T / 3) = 6 * r := by rw [hT]; field_simp; ring
        have h6 : 6 * r ≤ 9 * Real.sqrt d * (r / R) * (3 : ℝ) ^ m := by
          rw [← e]
          exact mul_le_mul_of_nonneg_left (by linarith only [this]) (by positivity)
        linarith only [hn2, h6])
    push_cast at this
    exact this
  have hP : 0 ≤ (9 * Real.sqrt d) ^ γ * (r / R) ^ γ := by positivity
  have hρ0 : 0 ≤ (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) := by positivity
  have hl2c : 0 ≤ h1_l2 (h1_cube (0 : Vec d) m) u := Real.sqrt_nonneg _
  have hKK : 0 ≤ (3 * Real.sqrt d) ^ d := by linarith only [hK1]
  have hM : h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) ≤
      C₁ * ((9 * Real.sqrt d) ^ γ * (r / R) ^ γ) * ((3 * Real.sqrt d) ^ d *
        (h1_l2 (euclidBall (d := d) R) u + G)) := by
    refine hHn.trans ?_
    have h1 : (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) * (h1_l2 (h1_cube (0 : Vec d) m) u + G) ≤
        ((9 * Real.sqrt d) ^ γ * (r / R) ^ γ) * ((3 * Real.sqrt d) ^ d *
        (h1_l2 (euclidBall (d := d) R) u + G)) := by
      refine mul_le_mul hrate ?_ (add_nonneg hl2c hG) hP
      nlinarith only [hl2', hK1, hG, hl2B]
    calc _ = C₁ * ((3 : ℝ) ^ (-γ * ((m : ℝ) - n)) * (h1_l2 (h1_cube (0 : Vec d) m) u + G)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hC₁
      _ = _ := by ring
  have hfinal : h1_linf (euclidBall (d := d) r) u (h1_avg (euclidBall (d := d) r) u) ≤
      2 * (C₁ * ((9 * Real.sqrt d) ^ γ * (r / R) ^ γ) * ((3 * Real.sqrt d) ^ d *
        (h1_l2 (euclidBall (d := d) R) u + G))) := by linarith only [hosc, hM]
  calc _ ≤ _ := hfinal
    _ = _ := by ring


/-- Radii comparable to `R`: cover `B_r` by the translated cubes `y + □_n`. -/
theorem h1_regime_large [NeZero d] {R r γ C₁ G : ℝ} {m₀ : ℕ} {u : Vec d → ℝ}
    (hR : 0 < R) (hu : MemLp u ⊤ (volume.restrict (euclidBall (d := d) R)))
    (hγ : 0 ≤ γ) (hC₁ : 0 ≤ C₁) (hG : 0 ≤ G)
    (hr0 : 12 * Real.sqrt d * (3 : ℝ) ^ m₀ ≤ r) (hrR : r ≤ R / 2) (hrc : R < 9 * Real.sqrt d * r)
    (H : ∀ y ∈ h1_lattice d ((3 : ℝ) ^ m₀), ∀ n m : ℕ, m₀ ≤ n → n < m →
      h1_cube y m ⊆ euclidBall (d := d) R →
      h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤
        C₁ * (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) * (h1_l2 (h1_cube y m) u + G)) :
    h1_linf (euclidBall (d := d) r) u (h1_avg (euclidBall (d := d) r) u) ≤
      2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁) * (9 * Real.sqrt d) ^ γ *
        (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u + G) := by
  have hsd := h1_sqrt_d_pos (d := d)
  have h3m : (1 : ℝ) ≤ (3 : ℝ) ^ m₀ := one_le_pow₀ (by norm_num)
  have hrpos : 0 < r := by nlinarith only [hr0, hsd, h3m]
  have hs1 : 1 ≤ R / (4 * Real.sqrt d) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith only [hr0, hsd, h3m, hrR]
  obtain ⟨n, hn1, hn2⟩ := h1_exists_inner hs1
  set s := R / (4 * Real.sqrt d) with hsdef
  have hRs : R = 4 * Real.sqrt d * s := by rw [hsdef]; field_simp
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hn3 : s < 3 * (3 : ℝ) ^ n := by rw [pow_succ] at hn2; linarith only [hn2]
  have hm₀lt : (3 : ℝ) ^ m₀ < (3 : ℝ) ^ n := by
    have : 2 * (3 : ℝ) ^ m₀ ≤ s / 3 := by
      have h1 : 24 * Real.sqrt d * (3 : ℝ) ^ m₀ ≤ R := by linarith only [hr0, hrR, hsd, h3m]
      rw [hRs] at h1
      have : 6 * (3 : ℝ) ^ m₀ ≤ s := by nlinarith only [h1, hsd]
      linarith only [this]
    linarith only [this, hn3, h3m]
  have hm₀n : m₀ ≤ n := ((pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hm₀lt).le
  have hcov := h1_covering (d := d) (R := R) hrpos (by positivity : (0 : ℝ) < (3 : ℝ) ^ m₀) hm₀lt
    (by
      have : 2 * Real.sqrt d * (3 : ℝ) ^ n ≤ R / 2 := by
        rw [hRs]; nlinarith only [hn1, hsd]
      linarith only [this, hrR])
  obtain ⟨Y, hYlat, -, hYcov, hYsub⟩ := hcov
  have hfin : volume (euclidBall (d := d) R) ≠ ⊤ := h1_vol_ball_ne_top hR
  have hl2B : 0 ≤ h1_l2 (euclidBall (d := d) R) u := Real.sqrt_nonneg _
  set K2 : ℝ := (24 * Real.sqrt d) ^ d with hK2
  have hK2' : 1 ≤ K2 := one_le_pow₀ (by linarith only [hsd])
  have hrat : ∀ k : ℕ, (3 : ℝ) ^ n ≤ (3 : ℝ) ^ k → ∀ y : Vec d,
      Real.sqrt ((volume (euclidBall (d := d) R)).toReal / (volume (h1_cube y k)).toReal) ≤ K2 := by
    intro k hk y
    refine (Real.sqrt_le_sqrt ((h1_ratio_le hR y k).trans ?_)).trans (h1_sqrt_le_self hK2')
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have h3k : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
    rw [div_le_iff₀ h3k]
    have : 2 * R ≤ 24 * Real.sqrt d * (3 : ℝ) ^ n := by
      rw [hRs]; nlinarith only [hn3, hsd]
    nlinarith only [this, hk, hsd]
  have hMv : ∀ y ∈ Y, ∀ᵐ x ∂volume.restrict (h1_cube y n),
      |u x - h1_avg (euclidBall (d := d) R) u| ≤
        (C₁ * K2 + K2) * h1_l2 (euclidBall (d := d) R) u + C₁ * G := by
    intro y hy
    have hsub1 := hYsub y hy
    have hsub0 : h1_cube y n ⊆ euclidBall (d := d) R :=
      (Metric.ball_subset_ball (by
        have : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith only [this])).trans hsub1
    have hdev := h1_dev_bound hsub0 hfin (h1_vol_cube_pos y n) hu
    have hH := H y (hYlat y hy) n (n + 1) hm₀n (by omega) hsub1
    have hl2 := h1_l2_le hsub1 (h1_memLp_two_of_top hfin hu) hfin (h1_vol_cube_pos y (n + 1))
    have hsq1 := hrat (n + 1) (by rw [pow_succ]; linarith only [h3n]) y
    have hsq0 := hrat n le_rfl y
    have hρ1 : (3 : ℝ) ^ (-γ * (((n + 1 : ℕ) : ℝ) - n)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      push_cast
      nlinarith only [hγ]
    have hl2c : 0 ≤ h1_l2 (h1_cube y (n + 1)) u := Real.sqrt_nonneg _
    have hl2K : h1_l2 (h1_cube y (n + 1)) u ≤ K2 * h1_l2 (euclidBall (d := d) R) u :=
      hl2.trans (mul_le_mul_of_nonneg_right hsq1 hl2B)
    have hlin : h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤
        C₁ * (K2 * h1_l2 (euclidBall (d := d) R) u + G) := by
      refine hH.trans ?_
      have h1 : C₁ * (3 : ℝ) ^ (-γ * (((n + 1 : ℕ) : ℝ) - n)) ≤ C₁ := by
        nlinarith only [hρ1, hC₁]
      have h2 : 0 ≤ h1_l2 (h1_cube y (n + 1)) u + G := add_nonneg hl2c hG
      calc _ ≤ C₁ * (h1_l2 (h1_cube y (n + 1)) u + G) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hl2K]) hC₁
    filter_upwards [hdev] with x hx
    have h3 : Real.sqrt ((volume (euclidBall (d := d) R)).toReal / (volume (h1_cube y n)).toReal) *
        h1_l2 (euclidBall (d := d) R) u ≤ K2 * h1_l2 (euclidBall (d := d) R) u :=
      mul_le_mul_of_nonneg_right hsq0 hl2B
    nlinarith only [hx, hlin, h3]
  have hMnn : 0 ≤ (C₁ * K2 + K2) * h1_l2 (euclidBall (d := d) R) u + C₁ * G := by positivity
  have hae : ∀ᵐ x ∂volume.restrict (euclidBall (d := d) r),
      |u x - h1_avg (euclidBall (d := d) R) u| ≤
        (C₁ * K2 + K2) * h1_l2 (euclidBall (d := d) R) u + C₁ * G := by
    have hU : ∀ᵐ x ∂volume.restrict (⋃ y ∈ Y, h1_cube y n),
        |u x - h1_avg (euclidBall (d := d) R) u| ≤
          (C₁ * K2 + K2) * h1_l2 (euclidBall (d := d) R) u + C₁ * G :=
      (ae_restrict_biUnion_finset_iff _ Y _).2 hMv
    exact ae_mono (Measure.restrict_mono hYcov le_rfl) hU
  have hrR' : r ≤ R := by linarith only [hrR, hR]
  have hBR : euclidBall (d := d) r ⊆ euclidBall (d := d) R := euclidBall_mono hrpos.le hrR'
  have hvr : 0 < (volume (euclidBall (d := d) r)).toReal :=
    ENNReal.toReal_pos (volume_euclidBall_ne_zero hrpos) (h1_vol_ball_ne_top hrpos)
  have hosc := h1_osc_two (h1_vol_ball_ne_top hrpos) hvr (h1_memLp_mono hBR hu) hMnn hae
  have hq : 1 ≤ (9 * Real.sqrt d) ^ γ * (r / R) ^ γ := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.one_le_rpow _ hγ
    rw [← mul_div_assoc, le_div_iff₀ hR]
    linarith only [hrc]
  set Q := (9 * Real.sqrt d) ^ γ * (r / R) ^ γ with hQ
  have hC : 0 ≤ C₁ * K2 + K2 + C₁ := by positivity
  have hfin2 : (C₁ * K2 + K2) * h1_l2 (euclidBall (d := d) R) u + C₁ * G ≤
      (C₁ * K2 + K2 + C₁) * (h1_l2 (euclidBall (d := d) R) u + G) := by
    nlinarith only [mul_nonneg hC₁ hl2B, mul_nonneg (by positivity : 0 ≤ C₁ * K2 + K2) hG]
  have hlast : (C₁ * K2 + K2 + C₁) * (h1_l2 (euclidBall (d := d) R) u + G) ≤
      Q * ((C₁ * K2 + K2 + C₁) * (h1_l2 (euclidBall (d := d) R) u + G)) := by
    have : 0 ≤ (C₁ * K2 + K2 + C₁) * (h1_l2 (euclidBall (d := d) R) u + G) := by positivity
    nlinarith only [hq, this]
  calc _ ≤ 2 * ((C₁ * K2 + K2) * h1_l2 (euclidBall (d := d) R) u + C₁ * G) := hosc
    _ ≤ 2 * (Q * ((C₁ * K2 + K2 + C₁) * (h1_l2 (euclidBall (d := d) R) u + G))) := by
        linarith only [hfin2, hlast]
    _ = _ := by rw [hQ]; ring


/-- **Cube-to-ball passage (PDE-free).** Let `u` be bounded and measurable on `B_R ⊆ ℝ^d` and
suppose the translated cube estimate `H` holds for every centre `y` of the lattice `3^{m₀} ℤ^d`
and all `m₀ ≤ n < m` with `y + □_m ⊆ B_R`.  Then for every real `r` with
`12 √d 3^{m₀} ≤ r ≤ R/2`,
`‖u - (u)_{B_r}‖_{L^∞(B_r)} ≤ C (r/R)^γ (‖u - (u)_{B_R}‖_{L̲²(B_R)} + G)` with
`C = 2 (C₁ K + K + C₁) (9 √d)^γ`, `K = (24 √d)^d`. -/
theorem h1_ball_holder [NeZero d] {R r γ C₁ G : ℝ} {m₀ : ℕ} {u : Vec d → ℝ}
    (hR : 0 < R) (hu : MemLp u ⊤ (volume.restrict (euclidBall (d := d) R)))
    (hγ : 0 ≤ γ) (hC₁ : 0 ≤ C₁) (hG : 0 ≤ G)
    (hr0 : 12 * Real.sqrt d * (3 : ℝ) ^ m₀ ≤ r) (hrR : r ≤ R / 2)
    (H : ∀ y ∈ h1_lattice d ((3 : ℝ) ^ m₀), ∀ n m : ℕ, m₀ ≤ n → n < m →
      h1_cube y m ⊆ euclidBall (d := d) R →
      h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤
        C₁ * (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) * (h1_l2 (h1_cube y m) u + G)) :
    h1_linf (euclidBall (d := d) r) u (h1_avg (euclidBall (d := d) r) u) ≤
      2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁) * (9 * Real.sqrt d) ^ γ *
        (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u + G) := by
  have hsd := h1_sqrt_d_pos (d := d)
  have h3m : (1 : ℝ) ≤ (3 : ℝ) ^ m₀ := one_le_pow₀ (by norm_num)
  by_cases hc : 9 * Real.sqrt d * r ≤ R
  · have h := h1_regime_small hR hu hγ hC₁ hG (by nlinarith only [hr0, hsd, h3m]) hc
      (fun n m hn hnm hs => H 0 (fun _ => ⟨0, by simp⟩) n m hn hnm hs)
    refine h.trans ?_
    have hK : (3 * Real.sqrt d) ^ d ≤ (24 * Real.sqrt d) ^ d :=
      pow_le_pow_left₀ (by positivity) (by nlinarith only [hsd]) d
    have hK1 : 1 ≤ (3 * Real.sqrt d) ^ d := one_le_pow₀ (by linarith only [hsd])
    have hl2B : 0 ≤ h1_l2 (euclidBall (d := d) R) u := Real.sqrt_nonneg _
    have hnn : 0 ≤ (9 * Real.sqrt d) ^ γ * (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u + G) := by
      have hrpos : 0 < r := by nlinarith only [hr0, hsd, h3m]
      positivity
    have : 2 * C₁ * (3 * Real.sqrt d) ^ d ≤
        2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁) := by
      nlinarith only [mul_le_mul_of_nonneg_left hK hC₁, hK, hK1, hC₁]
    calc _ = (2 * C₁ * (3 * Real.sqrt d) ^ d) *
          ((9 * Real.sqrt d) ^ γ * (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u + G)) := by ring
      _ ≤ (2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁)) *
          ((9 * Real.sqrt d) ^ γ * (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u + G)) :=
        mul_le_mul_of_nonneg_right this hnn
      _ = _ := by ring
  · exact h1_regime_large hR hu hγ hC₁ hG hr0 hrR (by linarith only [hc]) H

/-- Satisfiability of `h1_ball_holder`: `d = 1`, `u = 0`, `R = 100`, `r = 20`, `m₀ = 0`. -/
example : h1_linf (euclidBall (d := 1) 20) (fun _ => (0 : ℝ)) (h1_avg (euclidBall (d := 1) 20) fun _ => (0 : ℝ)) ≤
    2 * (1 * (24 * Real.sqrt (1 : ℕ)) ^ 1 + (24 * Real.sqrt (1 : ℕ)) ^ 1 + 1) *
      (9 * Real.sqrt (1 : ℕ)) ^ (1 / 2 : ℝ) * (20 / 100 : ℝ) ^ (1 / 2 : ℝ) *
      (h1_l2 (euclidBall (d := 1) 100) (fun _ => (0 : ℝ)) + 0) := by
  refine h1_ball_holder (R := 100) (m₀ := 0) (γ := 1 / 2) (C₁ := 1) (G := 0) (by norm_num)
    (by simp) (by norm_num) (by norm_num) le_rfl (by simp; norm_num) (by norm_num) ?_
  intro y _ n m _ _ _
  simp [h1_linf, h1_avg, h1_l2]

end SuperdiffusionCLT.Section7
