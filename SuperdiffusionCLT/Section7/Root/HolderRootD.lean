/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderRootC
public import Homogenization.PDE.Harmonic

/-!
# From the cube estimate to the ball estimate

The cube-to-ball passage of the large-scale Hölder theorem, for a function which is square
integrable on `B_R` and bounded only where the interior estimate provides it: for radii `r ≤ R/(9√d)`
the centred cubes, for radii comparable to `R` a covering by finitely many translated cubes whose
centres lie on the lattice `3^{lv n} ℤ^d`.
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- If `u` is bounded on `A` then `u - c` is. -/
theorem hr_memLp_sub {A : Set (Vec d)} {u : Vec d → ℝ} (hu : MemLp u ⊤ (volume.restrict A))
    (hA : volume A ≠ ⊤) (c : ℝ) : MemLp (fun x => u x - c) ⊤ (volume.restrict A) := by
  have := h1_finite_restrict hA
  exact hu.sub (memLp_const c)

/-- Deviation of `u` from the average over `B` on a subset `A`, with `u` bounded only on `A`. -/
theorem hr_dev_bound {A B : Set (Vec d)} (hAB : A ⊆ B) (hB : volume B ≠ ⊤)
    (hv : 0 < (volume A).toReal) {u : Vec d → ℝ} (hu2 : MemLp u 2 (volume.restrict B))
    (huA : MemLp u ⊤ (volume.restrict A)) :
    ∀ᵐ x ∂volume.restrict A, |u x - h1_avg B u| ≤
      h1_linf A u (h1_avg A u) +
        Real.sqrt ((volume B).toReal / (volume A).toReal) * h1_l2 B u := by
  have hA : volume A ≠ ⊤ := ne_top_of_le_ne_top hB (measure_mono hAB)
  have h1 := h1_ae_le_linf (hr_memLp_sub huA hA (h1_avg A u))
  have h2 := h1_avg_sub_le hAB hu2 hB hv
  filter_upwards [h1] with x hx
  have : |u x - h1_avg B u| ≤ |u x - h1_avg A u| + |h1_avg A u - h1_avg B u| := by
    have := abs_add_le (u x - h1_avg A u) (h1_avg A u - h1_avg B u)
    simpa using this
  linarith only [this, hx, h2]

/-- Small radii: centred cubes `B_r ⊆ □_n ⊆ □_m ⊆ B_R` with `3^n ≈ 2r`, `3^m ≈ 2R/√d`. -/
theorem hr_regime_small [NeZero d] {R r γ C₁ G : ℝ} {m₀ mT : ℕ} {u : Vec d → ℝ}
    (hR : 0 < R) (hu2 : MemLp u 2 (volume.restrict (euclidBall (d := d) R)))
    (hγ : 0 ≤ γ) (hC₁ : 0 ≤ C₁) (hG : 0 ≤ G)
    (hr0 : (3 : ℝ) ^ m₀ ≤ 2 * r) (hrR : 9 * Real.sqrt d * r ≤ R)
    (hmT : ∀ m : ℕ, Real.sqrt d * (3 : ℝ) ^ m ≤ 2 * R → m ≤ mT)
    (H : ∀ n m : ℕ, m₀ ≤ n → n < m → h1_cube (0 : Vec d) m ⊆ euclidBall (d := d) R → m ≤ mT →
      MemLp u ⊤ (volume.restrict (h1_cube (0 : Vec d) n)) ∧
      h1_linf (h1_cube 0 n) u (h1_avg (h1_cube 0 n) u) ≤
        C₁ * (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) * (h1_l2 (h1_cube 0 m) u + G)) :
    MemLp u ⊤ (volume.restrict (euclidBall (d := d) r)) ∧
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
  have hm3 : Real.sqrt d * (3 : ℝ) ^ m ≤ 2 * R := by
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : 0 ≤ Real.sqrt d)
    rw [hT, mul_div_cancel₀ _ (by positivity)] at this; exact this
  have hcubeM : h1_cube (0 : Vec d) m ⊆ euclidBall (d := d) R := by
    intro x hx
    have h0 : Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) ⊆
        euclidBall (Real.sqrt d * ((3 : ℝ) ^ m / 2)) := ball_subset_euclidBall
    refine euclidBall_mono (by positivity) ?_ (h0 hx)
    linarith only [hm3]
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
  obtain ⟨hmemn, hHn⟩ := H n m hm₀n hnm hcubeM (hmT m hm3)
  refine ⟨h1_memLp_mono hBrC hmemn, ?_⟩
  have hfin : volume (euclidBall (d := d) R) ≠ ⊤ := h1_vol_ball_ne_top hR
  have hMnn : 0 ≤ h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) :=
    ENNReal.toReal_nonneg
  -- oscillation on the ball
  have hvr : 0 < (volume (euclidBall (d := d) r)).toReal :=
    ENNReal.toReal_pos (volume_euclidBall_ne_zero hrpos) (h1_vol_ball_ne_top hrpos)
  have hae : ∀ᵐ x ∂volume.restrict (euclidBall (d := d) r),
      |u x - h1_avg (h1_cube (0 : Vec d) n) u| ≤
        h1_linf (h1_cube (0 : Vec d) n) u (h1_avg (h1_cube (0 : Vec d) n) u) := by
    have h1 := h1_ae_le_linf (hr_memLp_sub hmemn (h1_vol_cube_ne_top 0 n) (h1_avg (h1_cube (0 : Vec d) n) u))
    exact (ae_mono (Measure.restrict_mono hBrC le_rfl)) h1
  have hosc := h1_osc_two (h1_vol_ball_ne_top hrpos) hvr
    (h1_memLp_mono hBrC hmemn) hMnn hae
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
  have hl2 := h1_l2_le hcubeM hu2 hfin (h1_vol_cube_pos 0 m)
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
theorem hr_regime_large [NeZero d] {R r γ C₁ G : ℝ} {m₀ mT A : ℕ} {u : Vec d → ℝ}
    {lv : ℕ → ℤ}
    (hR : 0 < R) (hu2 : MemLp u 2 (volume.restrict (euclidBall (d := d) R)))
    (hγ : 0 ≤ γ) (hC₁ : 0 ≤ C₁) (hG : 0 ≤ G)
    (hr0 : 12 * Real.sqrt d * (3 : ℝ) ^ m₀ ≤ r) (hrR : r ≤ R / 2) (hrc : R < 9 * Real.sqrt d * r)
    (hlv : ∀ n : ℕ, lv n < (n : ℤ)) (hA : 7 * Real.sqrt d ≤ (3 : ℝ) ^ A)
    (hmT : ∀ m : ℕ, Real.sqrt d * (3 : ℝ) ^ m ≤ 2 * R → m ≤ mT)
    (H : ∀ n : ℕ, m₀ ≤ n → ∀ y : Vec d, y ∈ h1_lattice d ((3 : ℝ) ^ lv n) →
      (∀ i, |y i| ≤ (3 : ℝ) ^ (n + A)) → h1_cube y (n + 1) ⊆ euclidBall (d := d) R →
      n + 1 ≤ mT → MemLp u ⊤ (volume.restrict (h1_cube y n)) ∧
      h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤
        C₁ * (h1_l2 (h1_cube y (n + 1)) u + G)) :
    MemLp u ⊤ (volume.restrict (euclidBall (d := d) r)) ∧
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
  have hlvn : (3 : ℝ) ^ lv n < (3 : ℝ) ^ n := by
    have := zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 3) (hlv n)
    simpa only [zpow_natCast] using this
  have hcov := h1_covering (d := d) (R := R) hrpos (by positivity : (0 : ℝ) < (3 : ℝ) ^ lv n) hlvn
    (by
      have : 2 * Real.sqrt d * (3 : ℝ) ^ n ≤ R / 2 := by
        rw [hRs]; nlinarith only [hn1, hsd]
      linarith only [this, hrR])
  obtain ⟨Y, hYlat, hYbd, hYcov, hYsub⟩ := hcov
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
    have hyA : ∀ i, |y i| ≤ (3 : ℝ) ^ (n + A) := by
      intro i
      refine (hYbd y hy i).trans ?_
      have h1 : R < 12 * Real.sqrt d * (3 : ℝ) ^ n := by
        rw [hRs]; nlinarith only [hn3, hsd]
      have h2 : 7 * Real.sqrt d * (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (n + A) := by
        rw [pow_add]; nlinarith only [hA, h3n]
      nlinarith only [h1, h2, hrR, hsd, h3n]
    have hmT1 : n + 1 ≤ mT := by
      refine hmT (n + 1) ?_
      rw [pow_succ]
      nlinarith only [hn1, hsd, hRs, h3n]
    obtain ⟨hmemy, hH⟩ := H n hm₀n y (hYlat y hy) hyA hsub1 hmT1
    have hdev := hr_dev_bound hsub0 hfin (h1_vol_cube_pos y n) hu2 hmemy
    have hl2 := h1_l2_le hsub1 hu2 hfin (h1_vol_cube_pos y (n + 1))
    have hsq1 := hrat (n + 1) (by rw [pow_succ]; linarith only [h3n]) y
    have hsq0 := hrat n le_rfl y
    have hl2c : 0 ≤ h1_l2 (h1_cube y (n + 1)) u := Real.sqrt_nonneg _
    have hl2K : h1_l2 (h1_cube y (n + 1)) u ≤ K2 * h1_l2 (euclidBall (d := d) R) u :=
      hl2.trans (mul_le_mul_of_nonneg_right hsq1 hl2B)
    have hlin : h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤
        C₁ * (K2 * h1_l2 (euclidBall (d := d) R) u + G) := by
      refine hH.trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith only [hl2K]) hC₁
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
  have hmemr : MemLp u ⊤ (volume.restrict (euclidBall (d := d) r)) := by
    have := h1_finite_restrict (h1_vol_ball_ne_top (d := d) hrpos)
    refine memLp_top_of_bound ((hu2.mono_measure (Measure.restrict_mono hBR le_rfl)).aestronglyMeasurable) 
      (|h1_avg (euclidBall (d := d) R) u| + ((C₁ * K2 + K2) * h1_l2 (euclidBall (d := d) R) u + C₁ * G))
      ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (u x) (h1_avg (euclidBall (d := d) R) u)
    linarith only [this, hx]
  refine ⟨hmemr, ?_⟩
  have hosc := h1_osc_two (h1_vol_ball_ne_top hrpos) hvr hmemr hMnn hae
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



/-- **Cube-to-ball passage.** -/
theorem hr_ball_holder [NeZero d] {R r γ C₁ G : ℝ} {m₀ mT A : ℕ} {u : Vec d → ℝ} {lv : ℕ → ℤ}
    (hR : 0 < R) (hu2 : MemLp u 2 (volume.restrict (euclidBall (d := d) R)))
    (hγ : 0 ≤ γ) (hC₁ : 0 ≤ C₁) (hG : 0 ≤ G)
    (hr0 : 12 * Real.sqrt d * (3 : ℝ) ^ m₀ ≤ r) (hrR : r ≤ R / 2)
    (hlv : ∀ n : ℕ, lv n < (n : ℤ)) (hA : 7 * Real.sqrt d ≤ (3 : ℝ) ^ A)
    (hmT : ∀ m : ℕ, Real.sqrt d * (3 : ℝ) ^ m ≤ 2 * R → m ≤ mT)
    (H0 : ∀ n m : ℕ, m₀ ≤ n → n < m → h1_cube (0 : Vec d) m ⊆ euclidBall (d := d) R → m ≤ mT →
      MemLp u ⊤ (volume.restrict (h1_cube (0 : Vec d) n)) ∧
      h1_linf (h1_cube 0 n) u (h1_avg (h1_cube 0 n) u) ≤
        C₁ * (3 : ℝ) ^ (-γ * ((m : ℝ) - n)) * (h1_l2 (h1_cube 0 m) u + G))
    (H1 : ∀ n : ℕ, m₀ ≤ n → ∀ y : Vec d, y ∈ h1_lattice d ((3 : ℝ) ^ lv n) →
      (∀ i, |y i| ≤ (3 : ℝ) ^ (n + A)) → h1_cube y (n + 1) ⊆ euclidBall (d := d) R →
      n + 1 ≤ mT → MemLp u ⊤ (volume.restrict (h1_cube y n)) ∧
      h1_linf (h1_cube y n) u (h1_avg (h1_cube y n) u) ≤
        C₁ * (h1_l2 (h1_cube y (n + 1)) u + G)) :
    MemLp u ⊤ (volume.restrict (euclidBall (d := d) r)) ∧
    h1_linf (euclidBall (d := d) r) u (h1_avg (euclidBall (d := d) r) u) ≤
      2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁) * (9 * Real.sqrt d) ^ γ *
        (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u + G) := by
  have hsd := h1_sqrt_d_pos (d := d)
  have h3m : (1 : ℝ) ≤ (3 : ℝ) ^ m₀ := one_le_pow₀ (by norm_num)
  by_cases hc : 9 * Real.sqrt d * r ≤ R
  · obtain ⟨hmem, h⟩ := hr_regime_small hR hu2 hγ hC₁ hG (by nlinarith only [hr0, hsd, h3m]) hc
      hmT H0
    refine ⟨hmem, h.trans ?_⟩
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
  · exact hr_regime_large hR hu2 hγ hC₁ hG hr0 hrR (by linarith only [hc]) hlv hA hmT H1

/-- Satisfiability of `hr_ball_holder`: `d = 1`, `u = 0`, `R = 100`, `r = 20`. -/
example : MemLp (fun _ : Vec 1 => (0 : ℝ)) ⊤ (volume.restrict (euclidBall (d := 1) 20)) ∧
    h1_linf (euclidBall (d := 1) 20) (fun _ => (0 : ℝ))
        (h1_avg (euclidBall (d := 1) 20) fun _ => (0 : ℝ)) ≤
      2 * (1 * (24 * Real.sqrt (1 : ℕ)) ^ 1 + (24 * Real.sqrt (1 : ℕ)) ^ 1 + 1) *
        (9 * Real.sqrt (1 : ℕ)) ^ (1 / 2 : ℝ) * (20 / 100 : ℝ) ^ (1 / 2 : ℝ) *
        (h1_l2 (euclidBall (d := 1) 100) (fun _ => (0 : ℝ)) + 0) := by
  refine hr_ball_holder (R := 100) (m₀ := 0) (mT := 5) (A := 2) (γ := 1 / 2) (C₁ := 1) (G := 0)
    (lv := fun n => (n : ℤ) - 1) (by norm_num) MeasureTheory.MemLp.zero (by norm_num) (by norm_num) le_rfl
    (by simp; norm_num) (by norm_num) (fun n => by omega) (by simp; norm_num) ?_ ?_ ?_
  · intro m hm
    by_contra h
    have h6 : (3 : ℝ) ^ 6 ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    have : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by simp
    rw [this] at hm
    norm_num at h6 hm
    linarith only [h6, hm]
  · intro n m _ _ _ _
    exact ⟨MeasureTheory.MemLp.zero, by simp [h1_linf, h1_avg, h1_l2]⟩
  · intro n _ y _ _ _ _
    exact ⟨MeasureTheory.MemLp.zero, by simp [h1_linf, h1_avg, h1_l2]⟩

/-- A harmonic function is a weak solution with zero data. -/
theorem hr_harmonic_weak {a : CoeffField d} {U : Set (Vec d)} (v : AHarmonicFunction a U) :
    IsWeakSolutionOn a U v.toH1 (fun _ => 0) (fun _ => 0) := by
  intro φ
  have h := v.isHarmonic.2 φ
  simp only [zero_mul, integral_zero, vecDot_zero_left, add_zero]
  exact h

/-- Centring costs at most a factor two in `L²` of a probability measure. -/
theorem hr_centre {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f x - ∫ y, f y ∂μ) 2 μ ≤ 2 * eLpNorm f 2 μ := by
  have h1 := eLpNorm_sub_le (p := (2 : ℝ≥0∞)) (μ := μ) (f := f)
    (g := fun _ : α => ∫ y, f y ∂μ) (by norm_num)
  have h2 : eLpNorm (fun _ : α => ∫ y, f y ∂μ) 2 μ ≤ eLpNorm f 2 μ := by
    rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero μ)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    calc ‖∫ y, f y ∂μ‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm f 1 μ := (eLpNorm_one_eq_lintegral_enorm hf).symm
      _ ≤ eLpNorm f 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  calc _ ≤ eLpNorm f 2 μ + eLpNorm (fun _ : α => ∫ y, f y ∂μ) 2 μ := h1
    _ ≤ eLpNorm f 2 μ + eLpNorm f 2 μ := add_le_add_right h2 _
    _ = 2 * eLpNorm f 2 μ := (two_mul _).symm

/-- **Liouville statement from the oscillation estimate.** -/
theorem hr_liouville [NeZero d] {a : CoeffField d} {X C γ : ℝ} (hX : 2 ≤ X) (hC : 0 < C)
    (hH : ∀ R : ℝ, X ≤ R → ∀ (f : Vec d → ℝ) (u : H1Function (euclidBall (d := d) R)),
      IsWeakSolutionOn a (euclidBall (d := d) R) u f (fun _ => 0) →
      ∀ r : ℝ, X ≤ r → r ≤ R / 2 →
        eLpNorm (fun x => u.toFun x - ∫ y, u.toFun y ∂(ballMeasure (d := d) r)) ⊤
            (volume.restrict (euclidBall (d := d) r)) ≤
          ENNReal.ofReal (C * (r / R) ^ γ) *
            (ballL2 R (fun x => u.toFun x - ∫ y, u.toFun y ∂(ballMeasure (d := d) R)) +
              ENNReal.ofReal (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) *
                eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R))))
    (u : Vec d → ℝ) (G : Vec d → Vec d) (hu : IsEntireSolution a u G)
    (hlim : Filter.liminf (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)) * ballL2 r u)
      Filter.atTop = 0) :
    ∃ c : ℝ, u =ᵐ[volume] fun _ => c := by
  -- oscillation vanishes on every ball of radius at least `X`
  have hosc : ∀ r : ℝ, X ≤ r → ∃ c : ℝ, u =ᵐ[volume.restrict (euclidBall (d := d) r)] fun _ => c := by
    intro r hr
    have hrpos : 0 < r := by linarith only [hr, hX]
    refine ⟨∫ y, u y ∂(ballMeasure (d := d) r), ?_⟩
    set c : ℝ := ∫ y, u y ∂(ballMeasure (d := d) r) with hc
    have hsubr : ∀ R : ℝ, r ≤ R → euclidBall (d := d) r ⊆ euclidBall (d := d) R :=
      fun R hR => euclidBall_mono hrpos.le hR
    -- the bound for every large `R`
    have hbound : ∀ R : ℝ, X ≤ R → 2 * r ≤ R →
        eLpNorm (fun x => u x - c) ⊤ (volume.restrict (euclidBall (d := d) r)) ≤
          ENNReal.ofReal (2 * C * r ^ γ) *
            (ENNReal.ofReal (R ^ (-γ)) * ballL2 R u) := by
      intro R hXR h2R
      have hRpos : 0 < R := by linarith only [hrpos, h2R]
      obtain ⟨v, hv1, -⟩ := hu R hRpos
      have hw := hH R hXR (fun _ => 0) v.toH1 (hr_harmonic_weak v) r hr (by linarith only [h2R])
      simp only [eLpNorm_fun_zero, mul_zero, add_zero] at hw
      have hBR := hsubr R (by linarith only [hrpos, h2R])
      have hae_r : v.toH1.toFun =ᵐ[volume.restrict (euclidBall (d := d) r)] u :=
        ae_mono (Measure.restrict_mono hBR le_rfl) hv1
      have hac : ∀ s : ℝ, ballMeasure (d := d) s ≪ volume.restrict (euclidBall (d := d) s) := by
        intro s
        rw [hr_ballMeasure_eq]
        exact Measure.smul_absolutelyContinuous
      have hint : ∫ y, v.toH1.toFun y ∂(ballMeasure (d := d) r) = c := by
        refine integral_congr_ae ?_
        exact (hac r).ae_le hae_r
      rw [hint] at hw
      have hL : eLpNorm (fun x => u x - c) ⊤ (volume.restrict (euclidBall (d := d) r)) =
          eLpNorm (fun x => v.toH1.toFun x - c) ⊤ (volume.restrict (euclidBall (d := d) r)) :=
        eLpNorm_congr_ae (by filter_upwards [hae_r] with x hx; rw [hx])
      rw [hL]
      refine hw.trans ?_
      have hμ : IsProbabilityMeasure (ballMeasure (d := d) R) := by
        unfold ballMeasure
        exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
          (SuperdiffusionCLT.Section6.volume_euclidBall_ne_zero hRpos)
          (h1_vol_ball_ne_top hRpos)
      have hms : AEStronglyMeasurable v.toH1.toFun (ballMeasure (d := d) R) := by
        have h0 : AEStronglyMeasurable v.toH1.toFun (volume.restrict (euclidBall (d := d) R)) :=
          v.toH1.memL2.aestronglyMeasurable
        exact h0.mono_ac (hac R)
      have hcen := hr_centre (μ := ballMeasure (d := d) R) hms
      have heq : eLpNorm v.toH1.toFun 2 (ballMeasure (d := d) R) = eLpNorm u 2 (ballMeasure (d := d) R) := by
        exact eLpNorm_congr_ae ((hac R).ae_le hv1)
      have hrR : ENNReal.ofReal (C * (r / R) ^ γ) =
          ENNReal.ofReal (C * r ^ γ) * ENNReal.ofReal (R ^ (-γ)) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.div_rpow hrpos.le hRpos.le, Real.rpow_neg hRpos.le]
        congr 1; field_simp
      have h2C : ENNReal.ofReal (2 * C * r ^ γ) = 2 * ENNReal.ofReal (C * r ^ γ) := by
        rw [show 2 * C * r ^ γ = 2 * (C * r ^ γ) by ring, ENNReal.ofReal_mul (by norm_num)]
        simp
      calc ENNReal.ofReal (C * (r / R) ^ γ) *
            ballL2 R (fun x => v.toH1.toFun x - ∫ y, v.toH1.toFun y ∂(ballMeasure (d := d) R))
          ≤ ENNReal.ofReal (C * (r / R) ^ γ) * (2 * ballL2 R u) := by
            refine mul_le_mul_right ?_ _
            unfold ballL2
            rw [← heq]; exact hcen
        _ = _ := by rw [hrR, h2C]; ring
    have hzero : eLpNorm (fun x => u x - c) ⊤ (volume.restrict (euclidBall (d := d) r)) = 0 := by
      refine le_antisymm ?_ bot_le
      refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
      rw [zero_add]
      set K : ℝ := 2 * C * r ^ γ with hK
      have hKpos : 0 < K := by positivity
      have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal ((ε : ℝ) / K) := by
        rw [ENNReal.ofReal_pos]; exact div_pos hεr hKpos
      have hlt : Filter.liminf (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)) * ballL2 r u) Filter.atTop <
          ENNReal.ofReal ((ε : ℝ) / K) := by rw [hlim]; exact hδ
      have hfreq := Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
      obtain ⟨R, hR, hRlt⟩ := Filter.frequently_atTop.1 hfreq (max X (2 * r))
      have h := hbound R (le_trans (le_max_left _ _) hR) (le_trans (le_max_right _ _) hR)
      calc _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (R ^ (-γ)) * ballL2 R u) := h
        _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((ε : ℝ) / K) := mul_le_mul_right hRlt.le _
        _ = ε := by
          rw [← ENNReal.ofReal_mul hKpos.le, mul_div_cancel₀ _ hKpos.ne', ENNReal.ofReal_coe_nnreal]
    have h0 := (eLpNorm_eq_zero_iff (by simp)).1 hzero
    filter_upwards [h0] with x hx
    exact sub_eq_zero.1 hx
  -- one constant for all radii
  have hXpos : 0 < X := by linarith only [hX]
  choose! cc hcc using hosc
  have hall : ∀ n : ℕ, u =ᵐ[volume.restrict (euclidBall (d := d) (X + n))] fun _ => cc X := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 := hcc (X + n) (by linarith only [hn0])
    have h0 := hcc X le_rfl
    have h0' := ae_mono (Measure.restrict_mono (euclidBall_mono hXpos.le
      (by linarith only [hn0] : X ≤ X + n)) le_rfl) h1
    have hne : (volume.restrict (euclidBall (d := d) X)) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact SuperdiffusionCLT.Section6.volume_euclidBall_ne_zero hXpos
    have : (MeasureTheory.ae (volume.restrict (euclidBall (d := d) X))).NeBot := ae_neBot.2 hne
    obtain ⟨x, hx1, hx2⟩ := (h0.and h0').exists
    have hcn : cc (X + n) = cc X := hx2.symm.trans hx1
    filter_upwards [h1] with y hy
    rw [hy, hcn]
  refine ⟨cc X, ?_⟩
  have hU : (⋃ n : ℕ, euclidBall (d := d) (X + n)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (|vecNormSq x| + 1)
    refine ⟨n, ?_⟩
    show vecNormSq x < (X + n) ^ 2
    have h1 := le_abs_self (vecNormSq x)
    have h2 := abs_nonneg (vecNormSq x)
    nlinarith only [hn, h1, h2, hXpos]
  have hfin := (ae_restrict_iUnion_iff (μ := volume)
    (fun n : ℕ => euclidBall (d := d) (X + n)) (fun x => u x = cc X)).2 hall
  rw [hU, Measure.restrict_univ] at hfin
  exact hfin

end SuperdiffusionCLT.Section7
