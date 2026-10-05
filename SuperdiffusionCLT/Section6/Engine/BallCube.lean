/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers

/-!
# Balls and cubes

Comparison of the volume-normalized `L²` norms on a Euclidean ball `B_r` and on an origin cube
`□_k` of comparable size, from the inclusions `B_r ⊆ □_k ⊆ B_{√d 3^k / 2}` and the volume ratios.
Also: the ball average is the best constant in `L̲²(B_r)`, and linear functions have zero average
on centered balls (odd symmetry `x ↦ -x`).
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem e0d_cubeMeasure_eq (k : ℕ) :
    cubeMeasure (originCube d (k : ℤ)) = volume.restrict (engCube d k) := by
  unfold cubeMeasure
  exact Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)

theorem e0d_normCube_apply (k : ℕ) {s : Set (Vec d)} (hs : MeasurableSet s) :
    normalizedCubeMeasure (originCube d (k : ℤ)) s =
      ENNReal.ofReal ((((3 : ℝ) ^ k) ^ d)⁻¹) * volume (s ∩ engCube d k) := by
  rw [normalizedCubeMeasure, Measure.smul_apply, e0d_cubeMeasure_eq, Measure.restrict_apply hs,
    cubeVolume_eq_pow_scale, smul_eq_mul]
  rw [show (originCube d (k : ℤ)).scale = (k : ℤ) from rfl, zpow_natCast]

theorem e0d_ball_vol_le {r : ℝ} (hr : 0 < r) :
    volume (euclidBall (d := d) r) ≤ ENNReal.ofReal ((2 * r) ^ d) := by
  calc volume (euclidBall (d := d) r) ≤ volume (Metric.ball (0 : Vec d) r) :=
        measure_mono (euclidBall_subset_ball hr)
    _ = ENNReal.ofReal ((2 * r) ^ d) := by rw [Real.volume_pi_ball _ hr]; simp

theorem e0d_ball_vol_ge [NeZero d] {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d) ≤ volume (euclidBall (d := d) r) := by
  have hpos : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d)))
  calc ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d)
      = volume (Metric.ball (0 : Vec d) (r / Real.sqrt d)) := by
        rw [Real.volume_pi_ball _ (div_pos hr hpos)]; simp
    _ ≤ volume (euclidBall (d := d) r) := by
        refine measure_mono ((ball_subset_euclidBall).trans ?_)
        rw [mul_div_cancel₀ _ hpos.ne']

theorem e0d_ball_sub_cube {r : ℝ} {k : ℕ} (hr : 0 < r) (h2 : 2 * r ≤ (3 : ℝ) ^ k) :
    euclidBall (d := d) r ⊆ engCube d k := by
  intro x hx
  have hb := euclidBall_subset_ball hr hx
  rw [mem_ball_zero_iff] at hb
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi : |x i| < r := by simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans_lt hb
  have h3 : ((3 : ℝ) ^ (k : ℤ)) = (3 : ℝ) ^ k := zpow_natCast _ _
  rw [h3]
  constructor
  · linarith only [(abs_lt.1 hi).1, h2]
  · linarith only [(abs_lt.1 hi).2, h2]

theorem e0d_cube_sub_ball [NeZero d] {r : ℝ} {k : ℕ}
    (h : Real.sqrt d * (3 : ℝ) ^ k ≤ 2 * r) : engCube d k ⊆ euclidBall (d := d) r := by
  intro x hx
  rw [mem_openCubeSet_originCube_iff] at hx
  have h3 : ((3 : ℝ) ^ (k : ℤ)) = (3 : ℝ) ^ k := zpow_natCast _ _
  have hxi : ∀ i, x i ^ 2 < ((3 : ℝ) ^ k / 2) ^ 2 := by
    intro i
    have := hx i
    rw [h3] at this
    exact sq_lt_sq' (by linarith only [this.1]) (by linarith only [this.2])
  have hsum : vecNormSq x < (d : ℝ) * ((3 : ℝ) ^ k / 2) ^ 2 := by
    unfold vecNormSq vecDot
    have h1 : ∑ i, x i * x i < ∑ _i : Fin d, ((3 : ℝ) ^ k / 2) ^ 2 :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i _ => by simpa [pow_two] using hxi i)
    simpa using h1
  rw [mem_euclidBall]
  refine lt_of_lt_of_le hsum ?_
  have h0 : 0 ≤ Real.sqrt d * (3 : ℝ) ^ k := by positivity
  have hsq : (Real.sqrt d * (3 : ℝ) ^ k) ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)] at hsq
  linarith only [hsq]

theorem e0d_eLpNorm_le {μ ν : Measure (Vec d)} {C : ℝ} (hC : 0 ≤ C)
    (h : μ ≤ ENNReal.ofReal (C ^ 2) • ν) (f : Vec d → ℝ) (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal C * eLpNorm f 2 ν := by
  refine (eLpNorm_mono_measure f h).trans ?_
  rw [eLpNorm_smul_measure_of_ne_top (by simp) f _ hf, smul_eq_mul]
  refine le_of_eq ?_
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  have : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by simp [ENNReal.toReal_inv]
  rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_sq hC]

theorem e0d_ball_le_cube [NeZero d] {r : ℝ} {k : ℕ} (hr : 0 < r) (h2 : 2 * r ≤ (3 : ℝ) ^ k)
    (h54 : (3 : ℝ) ^ k ≤ 54 * r) :
    ballMeasure (d := d) r ≤
      ENNReal.ofReal (((27 * (d : ℝ)) ^ d) ^ 2) • normalizedCubeMeasure (originCube d (k : ℤ)) := by
  rw [Measure.le_iff]
  intro s hs
  rw [ballMeasure_apply, Measure.smul_apply, e0d_normCube_apply k hs, smul_eq_mul, ← mul_assoc]
  have hsub : euclidBall (d := d) r ∩ s ⊆ s ∩ engCube d k :=
    fun x hx => ⟨hx.2, e0d_ball_sub_cube hr h2 hx.1⟩
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith only [hd])
  have hs1 : 1 ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact hd
  have hss : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (by linarith only [hd])
  have hmpos : 0 < (2 * (r / Real.sqrt d)) ^ d := by positivity
  have hVpos : 0 < ((3 : ℝ) ^ k) ^ d := by positivity
  have hreal : ((2 * (r / Real.sqrt d)) ^ d)⁻¹ ≤ ((27 * (d : ℝ)) ^ d) ^ 2 * (((3 : ℝ) ^ k) ^ d)⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hmpos hVpos, one_mul]
    have h1 : (((3 : ℝ) ^ k) ^ d) ≤ (54 * r) ^ d := pow_le_pow_left₀ (by positivity) h54 d
    have h2' : 54 * r ≤ (27 * (d : ℝ)) ^ 2 * (2 * (r / Real.sqrt d)) := by
      have : (27 * (d : ℝ)) ^ 2 * (2 * (r / Real.sqrt d)) = 1458 * (d ^ 2 / Real.sqrt d) * r := by
        field_simp; ring
      rw [this]
      have : 1 ≤ (d : ℝ) ^ 2 / Real.sqrt d := by
        rw [le_div_iff₀ hspos]
        nlinarith only [hd, hs1, hss]
      nlinarith only [this, hr]
    calc (((3 : ℝ) ^ k) ^ d) ≤ (54 * r) ^ d := h1
      _ ≤ ((27 * (d : ℝ)) ^ 2 * (2 * (r / Real.sqrt d))) ^ d := pow_le_pow_left₀ (by positivity) h2' d
      _ = ((27 * (d : ℝ)) ^ d) ^ 2 * (2 * (r / Real.sqrt d)) ^ d := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm d 2]
  have hcoef : (volume (euclidBall (d := d) r))⁻¹ ≤
      ENNReal.ofReal (((27 * (d : ℝ)) ^ d) ^ 2) * ENNReal.ofReal ((((3 : ℝ) ^ k) ^ d)⁻¹) := by
    calc (volume (euclidBall (d := d) r))⁻¹
        ≤ (ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d))⁻¹ := ENNReal.inv_le_inv.2 (e0d_ball_vol_ge hr)
      _ = ENNReal.ofReal (((2 * (r / Real.sqrt d)) ^ d)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos hmpos).symm
      _ ≤ ENNReal.ofReal (((27 * (d : ℝ)) ^ d) ^ 2 * (((3 : ℝ) ^ k) ^ d)⁻¹) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := ENNReal.ofReal_mul (by positivity)
  calc (volume (euclidBall (d := d) r))⁻¹ * volume (euclidBall r ∩ s)
      ≤ (ENNReal.ofReal (((27 * (d : ℝ)) ^ d) ^ 2) * ENNReal.ofReal ((((3 : ℝ) ^ k) ^ d)⁻¹)) *
          volume (euclidBall r ∩ s) := by gcongr
    _ ≤ _ := by gcongr

theorem e0d_cube_le_ball [NeZero d] {r : ℝ} {k : ℕ} (h1 : Real.sqrt d * (3 : ℝ) ^ k ≤ 2 * r)
    (h2 : r ≤ (d : ℝ) * (3 : ℝ) ^ (k + 2)) :
    normalizedCubeMeasure (originCube d (k : ℤ)) ≤
      ENNReal.ofReal (((18 * (d : ℝ)) ^ d) ^ 2) • ballMeasure (d := d) r := by
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have hspos : 0 < Real.sqrt d := Real.sqrt_pos.2 (by linarith only [hd])
  have hr : 0 < r := by
    have : 0 < Real.sqrt d * (3 : ℝ) ^ k := by positivity
    linarith only [this, h1]
  rw [Measure.le_iff]
  intro s hs
  rw [e0d_normCube_apply k hs, Measure.smul_apply, ballMeasure_apply, smul_eq_mul]
  have hsub : s ∩ engCube d k ⊆ euclidBall (d := d) r ∩ s :=
    fun x hx => ⟨e0d_cube_sub_ball h1 hx.2, hx.1⟩
  have h2rpos : 0 < (2 * r) ^ d := by positivity
  have hVpos : 0 < ((3 : ℝ) ^ k) ^ d := by positivity
  have hC1 : (1 : ℝ) ≤ (18 * (d : ℝ)) ^ d := one_le_pow₀ (by linarith only [hd])
  have hreal : (((3 : ℝ) ^ k) ^ d)⁻¹ ≤ ((18 * (d : ℝ)) ^ d) ^ 2 * ((2 * r) ^ d)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hVpos h2rpos, one_mul]
    have h3 : 2 * r ≤ 18 * (d : ℝ) * (3 : ℝ) ^ k := by
      have : (3 : ℝ) ^ (k + 2) = 9 * 3 ^ k := by rw [pow_add]; ring
      rw [this] at h2
      nlinarith only [h2]
    calc (2 * r) ^ d ≤ (18 * (d : ℝ) * (3 : ℝ) ^ k) ^ d := pow_le_pow_left₀ (by positivity) h3 d
      _ = (18 * (d : ℝ)) ^ d * ((3 : ℝ) ^ k) ^ d := mul_pow _ _ _
      _ ≤ ((18 * (d : ℝ)) ^ d * (18 * (d : ℝ)) ^ d) * ((3 : ℝ) ^ k) ^ d := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hC1
      _ = ((18 * (d : ℝ)) ^ d) ^ 2 * ((3 : ℝ) ^ k) ^ d := by ring
  have hcoef : ENNReal.ofReal ((((3 : ℝ) ^ k) ^ d)⁻¹) ≤
      ENNReal.ofReal (((18 * (d : ℝ)) ^ d) ^ 2) * (volume (euclidBall (d := d) r))⁻¹ := by
    calc ENNReal.ofReal ((((3 : ℝ) ^ k) ^ d)⁻¹)
        ≤ ENNReal.ofReal (((18 * (d : ℝ)) ^ d) ^ 2 * ((2 * r) ^ d)⁻¹) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (((18 * (d : ℝ)) ^ d) ^ 2) * (ENNReal.ofReal ((2 * r) ^ d))⁻¹ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos h2rpos]
      _ ≤ _ := by gcongr; exact e0d_ball_vol_le hr
  calc ENNReal.ofReal ((((3 : ℝ) ^ k) ^ d)⁻¹) * volume (s ∩ engCube d k)
      ≤ (ENNReal.ofReal (((18 * (d : ℝ)) ^ d) ^ 2) * (volume (euclidBall (d := d) r))⁻¹) *
          volume (s ∩ engCube d k) := by gcongr
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr

/-! ### Main statements -/

/-- A ball inside a comparable cube: `B_r ⊆ □_k` when `2r ≤ 3^k`, and the normalized norms
compare with a dimensional constant when moreover `3^k ≤ 54 r`. -/
theorem ballL2_le_cubeL2 (d : ℕ) [NeZero d] :
    ∃ Cd : ℝ, 1 ≤ Cd ∧ ∀ (r : ℝ) (k : ℕ), 0 < r → 2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 54 * r →
      ∀ f : Vec d → ℝ, MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) →
        ballL2 r f ≤ ENNReal.ofReal (Cd * cubeL2 k f) := by
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  refine ⟨(27 * (d : ℝ)) ^ d, one_le_pow₀ (by linarith only [hd]), ?_⟩
  intro r k hr h2 h54 f hf
  have hC : (0 : ℝ) ≤ (27 * (d : ℝ)) ^ d := by positivity
  have h := e0d_eLpNorm_le hC (e0d_ball_le_cube hr h2 h54) f hf.aestronglyMeasurable
  unfold ballL2 cubeL2 cubeLpNorm
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

/-- A cube inside a comparable ball: `□_k ⊆ B_r` when `√d 3^k ≤ 2r`. -/
theorem cubeL2_le_ballL2 (d : ℕ) [NeZero d] :
    ∃ Cd : ℝ, 1 ≤ Cd ∧ ∀ (r : ℝ) (k : ℕ), Real.sqrt d * (3 : ℝ) ^ k ≤ 2 * r →
      r ≤ (d : ℝ) * (3 : ℝ) ^ (k + 2) →
      ∀ f : Vec d → ℝ, MemLp f 2 (ballMeasure r) →
        cubeL2 k f ≤ Cd * (ballL2 r f).toReal := by
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  refine ⟨(18 * (d : ℝ)) ^ d, one_le_pow₀ (by linarith only [hd]), ?_⟩
  intro r k h1 h2 f hf
  have hC : (0 : ℝ) ≤ (18 * (d : ℝ)) ^ d := by positivity
  have h := e0d_eLpNorm_le hC (e0d_cube_le_ball h1 h2) f hf.aestronglyMeasurable
  unfold cubeL2 cubeLpNorm ballL2
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at h'

theorem ballGradL2_le_cubeGradL2 (d : ℕ) [NeZero d] :
    ∃ Cd : ℝ, 1 ≤ Cd ∧ ∀ (r : ℝ) (k : ℕ), 0 < r → 2 * r ≤ (3 : ℝ) ^ k → (3 : ℝ) ^ k ≤ 54 * r →
      ∀ F : Vec d → Vec d,
        MemLp (fun x => engNorm (F x)) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) →
        ballGradL2 r F ≤ ENNReal.ofReal (Cd * cubeGradL2 k F) := by
  obtain ⟨Cd, hC, h⟩ := ballL2_le_cubeL2 d
  exact ⟨Cd, hC, fun r k hr h2 h54 F hF => h r k hr h2 h54 _ hF⟩

theorem cubeGradL2_le_ballGradL2 (d : ℕ) [NeZero d] :
    ∃ Cd : ℝ, 1 ≤ Cd ∧ ∀ (r : ℝ) (k : ℕ), Real.sqrt d * (3 : ℝ) ^ k ≤ 2 * r →
      r ≤ (d : ℝ) * (3 : ℝ) ^ (k + 2) →
      ∀ F : Vec d → Vec d, MemLp (fun x => engNorm (F x)) 2 (ballMeasure r) →
        cubeGradL2 k F ≤ Cd * (ballGradL2 r F).toReal := by
  obtain ⟨Cd, hC, h⟩ := cubeL2_le_ballL2 d
  exact ⟨Cd, hC, fun r k h1 h2 F hF => h r k h1 h2 _ hF⟩

/-- The ball average is the best constant: `‖f - (f)_{B_r}‖ ≤ ‖f - c‖` in `L̲²(B_r)`. -/
theorem ballL2_sub_average_le [NeZero d] {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : MemLp f 2 (ballMeasure r)) (c : ℝ) :
    ballL2 r (fun x => f x - ∫ y, f y ∂ballMeasure r) ≤ ballL2 r (fun x => f x - c) := by
  have := isProbabilityMeasure_ballMeasure (d := d) hr
  set μ : Measure (Vec d) := ballMeasure r with hμ
  set m : ℝ := ∫ y, f y ∂μ with hm
  have hg : MemLp (fun x => f x - m) 2 μ := hf.sub (memLp_const m)
  have hh : MemLp (fun x => f x - c) 2 μ := hf.sub (memLp_const c)
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hgi : Integrable (fun x => f x - m) μ := hfi.sub (integrable_const m)
  have hg2 : Integrable (fun x => (f x - m) ^ 2) μ := hg.integrable_sq
  have hg0 : ∫ x, (f x - m) ∂μ = 0 := by
    rw [integral_sub hfi (integrable_const m), integral_const]
    simp [hm]
  have hlin : Integrable (fun x => 2 * (m - c) * (f x - m)) μ := hgi.const_mul _
  have hexp : ∫ x, (f x - c) ^ 2 ∂μ = ∫ x, (f x - m) ^ 2 ∂μ + (m - c) ^ 2 := by
    have e : (fun x => (f x - c) ^ 2) =
        fun x => (f x - m) ^ 2 + (2 * (m - c) * (f x - m) + (m - c) ^ 2) := by
      ext x; ring
    have h1 := integral_add hg2 (hlin.add (integrable_const ((m - c) ^ 2)))
    have h2 := integral_add hlin (integrable_const ((m - c) ^ 2))
    simp only [Pi.add_apply] at h1 h2
    rw [e, h1, h2, integral_const_mul, hg0]
    simp
  unfold ballL2
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (integral_nonneg fun x => by positivity) _ (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  linarith only [hexp, sq_nonneg (m - c)]

/-- Linear functions have zero average on centered balls. -/
theorem integral_vecDot_ballMeasure [NeZero d] {r : ℝ} (hr : 0 < r) (e : Vec d) :
    ∫ y, vecDot e y ∂ballMeasure r = 0 := by
  have _ := hr
  have hB := measurableSet_euclidBall (d := d) r
  set g : Vec d → ℝ := (euclidBall (d := d) r).indicator (fun y => vecDot e y) with hg
  have hodd : ∀ x, g (-x) = -g x := by
    intro x
    have hmem : (-x ∈ euclidBall (d := d) r) ↔ x ∈ euclidBall r := by
      simp [mem_euclidBall, vecNormSq, vecDot]
    by_cases hx : x ∈ euclidBall (d := d) r
    · rw [hg, Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
      simp [vecDot, Finset.sum_neg_distrib]
    · rw [hg, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      simp
  have hI : ∫ x, g x = 0 := by
    have h1 : ∫ x, g (-x) = ∫ x, g x := integral_neg_eq_self g volume
    have h2 : ∫ x, g (-x) = -∫ x, g x := by
      simp only [hodd]; exact integral_neg _
    linarith only [h1, h2]
  unfold ballMeasure ProbabilityTheory.cond
  rw [integral_smul_measure, ← integral_indicator hB]
  simp [← hg, hI]

/-- Witness: the unit ball with `k = 1` in dimension two meets the ball-in-cube hypotheses, and
the ball of radius `3` meets the cube-in-ball ones, with a function that is in `L²` of both. -/
example :
    (0 : ℝ) < 1 ∧ 2 * (1 : ℝ) ≤ (3 : ℝ) ^ 1 ∧ (3 : ℝ) ^ 1 ≤ 54 * 1 ∧
      MemLp (fun _ : Vec 2 => (0 : ℝ)) 2 (normalizedCubeMeasure (originCube 2 ((1 : ℕ) : ℤ))) ∧
      Real.sqrt (2 : ℕ) * (3 : ℝ) ^ 1 ≤ 2 * 3 ∧ (3 : ℝ) ≤ ((2 : ℕ) : ℝ) * (3 : ℝ) ^ (1 + 2) ∧
      MemLp (fun _ : Vec 2 => (0 : ℝ)) 2 (ballMeasure (3 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, memLp_const _, ?_, by norm_num, ?_⟩
  · have : Real.sqrt (2 : ℕ) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith only [this]
  · have := isProbabilityMeasure_ballMeasure (d := 2) (r := 3) (by norm_num)
    exact memLp_const _

end SuperdiffusionCLT.Section6
