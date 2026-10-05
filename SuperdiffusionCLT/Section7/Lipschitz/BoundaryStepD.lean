/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryStepC

/-!
# The boundary one-step inequality

`lip_bdry_step`: from the harmonic approximation `lip_bdry_approx`, the pinned decay of the
difference `ub - gt` (localized by a cutoff to an `H¹₀` solution of the Poisson equation), and the
Taylor expansion of the mollified datum, the pinned flatness at the scale `k - k₀` is bounded by
a small multiple of the pinned flatness at the scale `k + 1`.  The boundary Caccioppoli block is
used only inside `lip_bdry_approx`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The first term of the bracket of the decay estimate, normalized by the side `ℓ`. -/
theorem lip_bdry_step_term1 {V Su : Set (Vec d)} {z x₀ G p : Vec d} {k N : ℕ} {R ℓ Ca G1 c₀ Kd : ℝ}
    {u ub gt : Vec d → ℝ} (hVo : IsOpen V) (hSuo : IsOpen Su) (hVSu : V ⊆ Su)
    (hV0 : volume V ≠ 0) (hVball : V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2))
    (hSuball : Su ⊆ Metric.ball z ((3 : ℝ) ^ (k + 1) / 2))
    (hSuR : ∀ y ∈ Su, ‖y - x₀‖ ≤ 3 * (3 : ℝ) ^ k)
    (hℓ : 0 < ℓ) (hℓN : ℓ * 3 ^ N = (3 : ℝ) ^ k) (hRℓ : R = Kd * ℓ) (hKd : 1 ≤ Kd)
    (hKN : Kd ≤ 3 ^ N) (hCa : 0 ≤ Ca) (hG1 : 0 ≤ G1)
    (hu : MemLp u 2 (volume.restrict Su)) (hub : MemLp ub 2 (volume.restrict V))
    (hgtc : Continuous gt)
    (hgg : |c₀ - gt x₀| ≤ Ca * (3 : ℝ) ^ k * G1)
    (hTay : ∀ y, ‖y - x₀‖ ≤ R →
      |gt y - gt x₀ - vecDot G (y - x₀)| ≤ Ca * ((3 : ℝ) ^ k)⁻¹ * G1 * R * R) :
    ℓ⁻¹ * (eLpNorm (fun y => (ub y - gt y) - vecDot (p - G) (y - x₀)) 2
        (p12_nmeas ℓ (V ∩ Metric.ball x₀ R))).toReal ≤
      (3 : ℝ) ^ N * Real.sqrt (((3 : ℝ) ^ N) ^ d) *
          (((3 : ℝ)⁻¹) ^ k * lipL2 V (fun x => u x - ub x)) +
        3 * 3 ^ N * Real.sqrt (((3 : ℝ) ^ (N + 1)) ^ d) *
          lipPin Su (k + 1) x₀ c₀ u p +
        2 * 3 ^ N * Ca * G1 * Real.sqrt ((2 * Kd) ^ d) := by
  have hR0 : 0 < R := by rw [hRℓ]; positivity
  have hTpos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hPpos : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hSm : MeasurableSet (V ∩ Metric.ball x₀ R) := (hVo.inter Metric.isOpen_ball).measurableSet
  have hSV : V ∩ Metric.ball x₀ R ⊆ V := Set.inter_subset_left
  have hSSu : V ∩ Metric.ball x₀ R ⊆ Su := hSV.trans hVSu
  have hVt : volume V ≠ ⊤ := (lip_bdry_step_vol_ball (by positivity) hℓ hVball).1
  have hSut : volume Su ≠ ⊤ := (lip_bdry_step_vol_ball (by positivity) hℓ hSuball).1
  have hSu0 : volume Su ≠ 0 := fun h => hV0 (le_antisymm (h ▸ measure_mono hVSu) bot_le)
  have hSt : volume (V ∩ Metric.ball x₀ R) ≠ ⊤ := ne_top_of_le_ne_top hVt (measure_mono hSV)
  have hub' : MemLp ub 2 (volume.restrict V) := hub
  have hR1 : MemLp (fun y => ub y - u y) 2 (volume.restrict V) :=
    hub'.sub (hu.mono_measure (Measure.restrict_mono hVSu le_rfl))
  have hR2 := lip_bdry_step_memLp_aff hSuo.measurableSet hSut hu hSuR c₀ p
  have hR3c : Continuous (fun y : Vec d => (c₀ - gt x₀) -
      (gt y - gt x₀ - vecDot G (y - x₀))) :=
    continuous_const.sub ((hgtc.sub continuous_const).sub (lip_bdry_approx_continuous_aff G x₀))
  set B3 : ℝ := Ca * (3 : ℝ) ^ k * G1 + Ca * ((3 : ℝ) ^ k)⁻¹ * G1 * R * R with hB3
  have hB30 : 0 ≤ B3 := by rw [hB3]; positivity
  have hR3b : ∀ y ∈ V ∩ Metric.ball x₀ R, |(c₀ - gt x₀) -
      (gt y - gt x₀ - vecDot G (y - x₀))| ≤ B3 := by
    intro y hy
    have hyR : ‖y - x₀‖ ≤ R := by
      have := hy.2
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this.le
    exact (abs_sub _ _).trans (add_le_add hgg (hTay y hyR))
  have hX := lip_bdry_step_X1 (S := V ∩ Metric.ball x₀ R) (Sv := V) (Su := Su) hSm hSV hSSu hV0 hVt
    hSu0 hSut hSt hℓ (H := fun y => (ub y - gt y) - vecDot (p - G) (y - x₀))
    (R1 := fun y => ub y - u y)
    (R2 := fun y => u y - c₀ - vecDot p (y - x₀))
    (R3 := fun y => (c₀ - gt x₀) - (gt y - gt x₀ - vecDot G (y - x₀)))
    (fun y _ => by
      simp only [lip_bdry_step_vecDot_sub_left]
      ring) hR1 hR2 hR3c.aestronglyMeasurable hB30 hR3b
  -- volumes
  have hvV := (lip_bdry_step_vol_ball (by positivity) hℓ hVball).2
  have hvSu := (lip_bdry_step_vol_ball (by positivity) hℓ hSuball).2
  have hvS := (lip_bdry_step_vol_ball (c := x₀) hR0 hℓ
    (Set.inter_subset_right : V ∩ Metric.ball x₀ R ⊆ Metric.ball x₀ R)).2
  have eV : 2 * ((3 : ℝ) ^ k / 2) / ℓ = 3 ^ N := by
    field_simp
    linarith only [hℓN]
  have eSu : 2 * ((3 : ℝ) ^ (k + 1) / 2) / ℓ = 3 ^ (N + 1) := by
    rw [pow_succ, pow_succ]
    field_simp
    linarith only [hℓN]
  have eS : 2 * R / ℓ = 2 * Kd := by
    rw [hRℓ]; field_simp
  rw [eV] at hvV
  rw [eSu] at hvSu
  rw [eS] at hvS
  have sV := Real.sqrt_le_sqrt hvV
  have sSu := Real.sqrt_le_sqrt hvSu
  have sS := Real.sqrt_le_sqrt hvS
  have hinv : ℓ⁻¹ = (3 : ℝ) ^ N * ((3 : ℝ)⁻¹) ^ k := by
    rw [inv_pow, ← hℓN]
    field_simp
  have hΦ : lipL2 Su (fun x => u x - c₀ - vecDot p (x - x₀)) =
      (3 : ℝ) ^ (k + 1) * lipPin Su (k + 1) x₀ c₀ u p := by
    unfold lipPin
    rw [← mul_assoc, show (3 : ℝ) ^ (k + 1) * ((3 : ℝ)⁻¹) ^ (k + 1) = 1 by
      rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow], one_mul]
  have hcomm := lip_bdry_step_lipL2_comm V (fun x => ub x) (fun x => u x)
  have hL1 : lipL2 V (fun y => ub y - u y) = lipL2 V (fun x => u x - ub x) := hcomm
  rw [hL1, hΦ] at hX
  set Z : ℝ := ((3 : ℝ)⁻¹) ^ k with hZ
  set P : ℝ := (3 : ℝ) ^ N with hP
  set sN := Real.sqrt (((3 : ℝ) ^ N) ^ d) with hsN
  set sN1 := Real.sqrt (((3 : ℝ) ^ (N + 1)) ^ d) with hsN1
  set sK := Real.sqrt ((2 * Kd) ^ d) with hsK
  have hZT : Z * (3 : ℝ) ^ k = 1 := by
    rw [hZ, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  have hL0 : 0 ≤ lipL2 V (fun x => u x - ub x) := ENNReal.toReal_nonneg
  have hΦ0 : 0 ≤ lipPin Su (k + 1) x₀ c₀ u p := by
    unfold lipPin lipL2
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hℓ0 : 0 ≤ ℓ⁻¹ := inv_nonneg.2 hℓ.le
  have hsN0 : 0 ≤ sN := Real.sqrt_nonneg _
  have hsN10 : 0 ≤ sN1 := Real.sqrt_nonneg _
  have hsK0 : 0 ≤ sK := Real.sqrt_nonneg _
  have hsv0 : 0 ≤ Real.sqrt ((ℓ ^ d)⁻¹ * (volume V).toReal) := Real.sqrt_nonneg _
  have hsu0 : 0 ≤ Real.sqrt ((ℓ ^ d)⁻¹ * (volume Su).toReal) := Real.sqrt_nonneg _
  have hss0 : 0 ≤ Real.sqrt ((ℓ ^ d)⁻¹ * (volume (V ∩ Metric.ball x₀ R)).toReal) :=
    Real.sqrt_nonneg _
  have t1 : Real.sqrt ((ℓ ^ d)⁻¹ * (volume V).toReal) * lipL2 V (fun x => u x - ub x) ≤
      sN * lipL2 V (fun x => u x - ub x) := mul_le_mul_of_nonneg_right sV hL0
  have t2 : Real.sqrt ((ℓ ^ d)⁻¹ * (volume Su).toReal) *
      ((3 : ℝ) ^ (k + 1) * lipPin Su (k + 1) x₀ c₀ u p) ≤
      sN1 * ((3 : ℝ) ^ (k + 1) * lipPin Su (k + 1) x₀ c₀ u p) :=
    mul_le_mul_of_nonneg_right sSu (by positivity)
  have t3 : B3 * Real.sqrt ((ℓ ^ d)⁻¹ * (volume (V ∩ Metric.ball x₀ R)).toReal) ≤ B3 * sK :=
    mul_le_mul_of_nonneg_left sS hB30
  have hX' := hX.trans (add_le_add (add_le_add t1 t2) t3)
  have hB3ℓ : ℓ⁻¹ * B3 ≤ 2 * P * Ca * G1 := by
    have hTP : ℓ = (3 : ℝ) ^ k / P := by
      rw [eq_div_iff hPpos.ne']; exact hℓN
    have hKP : Kd * Kd ≤ P * P := mul_le_mul hKN hKN (by linarith only [hKd]) hPpos.le
    have e : ℓ⁻¹ * B3 = Ca * G1 * P + Ca * G1 * (Kd * Kd) / P := by
      rw [hB3, hRℓ, hTP]
      field_simp
    rw [e]
    have : Ca * G1 * (Kd * Kd) / P ≤ Ca * G1 * P := by
      rw [div_le_iff₀ hPpos]
      have := mul_le_mul_of_nonneg_left hKP (mul_nonneg hCa hG1)
      linarith only [this]
    linarith only [this]
  calc ℓ⁻¹ * (eLpNorm (fun y => (ub y - gt y) - vecDot (p - G) (y - x₀)) 2
        (p12_nmeas ℓ (V ∩ Metric.ball x₀ R))).toReal
      ≤ ℓ⁻¹ * (sN * lipL2 V (fun x => u x - ub x) +
        sN1 * ((3 : ℝ) ^ (k + 1) * lipPin Su (k + 1) x₀ c₀ u p) + B3 * sK) :=
        mul_le_mul_of_nonneg_left hX' hℓ0
    _ = P * sN * (Z * lipL2 V (fun x => u x - ub x)) +
        3 * P * sN1 * (lipPin Su (k + 1) x₀ c₀ u p * (Z * (3 : ℝ) ^ k)) + (ℓ⁻¹ * B3) * sK := by
        rw [hinv, pow_succ]
        ring
    _ ≤ _ := by
        rw [hZT, mul_one]
        have := mul_le_mul_of_nonneg_right hB3ℓ hsK0
        have e : 3 * P * sN1 * lipPin Su (k + 1) x₀ c₀ u p =
            3 * 3 ^ N * sN1 * lipPin Su (k + 1) x₀ c₀ u p := rfl
        linarith only [this]

private theorem lip_step_nat_a (N ag N₀ : ℕ) : ag + 1 ≤ N + ag + 1 + N₀ := by omega

private theorem lip_step_nat_b {N ag N₀ k₀ k : ℕ} (hk₀ : N + ag + 1 + N₀ ≤ k₀) (hk : k₀ + 1 ≤ k) :
    N ≤ k ∧ k₀ ≤ k ∧ ag + 1 ≤ k₀ ∧ N ≤ k₀ := by omega

private theorem lip_step_nat_c {N ag N₀ k₀ k : ℕ} (hk₀ : N + ag + 1 + N₀ ≤ k₀) (hk : k₀ ≤ k) :
    k - k₀ + (N + N₀) ≤ k := by omega

private theorem lip_step_nat_d {N ag N₀ k₀ k : ℕ} (hk₀ : N + ag + 1 + N₀ ≤ k₀) (hk : k₀ ≤ k) :
    k - k₀ ≤ k - N := by omega

private theorem lip_step_nat_e {N k₀ k : ℕ} (hN : N ≤ k₀) (hk : k₀ ≤ k) :
    k - N = k - k₀ + (k₀ - N) := by omega

private theorem lip_step_nat_f (N ag N₀ k₀ : ℕ) : k₀ - (N + ag + 1 + N₀) ≤ k₀ - N := by omega

private theorem lip_step_nat_g {k₀ k : ℕ} (h : k₀ ≤ k) : k ≤ k₀ + (k - k₀ + 2) := by omega

/-- **The boundary one-step inequality** (with the slope term of the
corrected decay display and the flatness `θ` of the true patch).  `C₁` and `a₁` do not depend on
`k₀`; `(√3)⁻¹ ^ (k₀ - a₁)` is the decay `3^{-α (k₀ - a₁)}` at `α = 1/2`. -/
theorem lip_bdry_step (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cin M₁ MU rU : ℝ) (hCin : 1 ≤ Cin)
    (hrU : 0 < rU) (hMU : 0 ≤ MU) (ag A : ℕ) :
    ∃ (C₁ : ℝ) (a₁ : ℕ), 1 ≤ C₁ ∧ ag + 1 ≤ a₁ ∧ ∀ k₀ : ℕ, a₁ ≤ k₀ → ∃ C₂ : ℝ, 1 ≤ C₂ ∧
      ∀ (a : CoeffField d) (W V : Set (Vec d)) (rW M₂W DW nu s δ E θ lam Lam : ℝ)
        (z x₀ : Vec d) (k : ℕ),
        0 < nu → 1 ≤ s → 0 ≤ δ → δ ≤ 1 → 0 ≤ E → 0 ≤ θ → θ ≤ 1 → k₀ + 1 ≤ k →
        ((k : ℝ) ^ A)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu → ((k : ℝ) ^ A)⁻¹ * s ≤ 1 →
        IsUniformC11Domain W rW M₁ M₂W DW → rU * (3 : ℝ) ^ k ≤ rW →
        M₂W * (3 : ℝ) ^ k ≤ MU * θ →
        z ∈ W → x₀ ∈ frontier W → ‖x₀ - z‖ ≤ (3 : ℝ) ^ (k - k₀) / 2 →
        IsOpen V → Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V →
        V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ W →
        IsEllipticFieldOn lam Lam (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) a → 0 < lam →
        LipL2Block a nu s δ Cin A k V →
        LipCaccBdryS a nu s Cin E W z (k + 1) → LipCaccBdryS a nu s Cin E W z (k + 2) →
        ∀ (f g : Vec d → ℝ) (F G1 G2 : ℝ) (u : H1Function (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W)),
          ContDiff ℝ 2 g → 0 ≤ F → 0 ≤ G1 → 0 ≤ G2 →
          (∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ g x‖ ≤ G1) →
          (∀ x ∈ shiftCube z ((k + 2 : ℕ) : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) →
          (∀ᵐ x ∂volume.restrict (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W), |f x| ≤ F) →
          IsWeakSolutionOn a (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) u f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W)
            (shiftCube z ((k + 2 : ℕ) : ℤ)) (fun x => u.toFun x - g x) →
          ∀ p : Vec d, ∃ p' : Vec d,
            lipPin (shiftCube z ((k - k₀ : ℕ) : ℤ) ∩ W) (k - k₀) x₀ (g x₀) u.toFun p' ≤
              (C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) + C₂ * δ) *
                  lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p +
                (C₂ * δ + C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) * θ) * ‖p‖ +
                C₂ * (G1 + s⁻¹ * (3 : ℝ) ^ k * F + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) := by
  classical
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_two hd)
  obtain ⟨Ca, hCa1, hCa⟩ := lip_bdry_approx d hd Cin M₁ rU hCin hrU ag A
  have hp : (d : ℝ) < 2 * (d : ℝ) := by linarith only [hd0]
  obtain ⟨εd, Cdec, cdec, Kd, hεd, hCdec, hcdec, hKd, hdec⟩ := lip_patch_decay_loc d hd M₁ hp
  obtain ⟨κ, hκ, hratio⟩ := lip_bdry_approx_volume_ratio d M₁ rU hrU 0
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (max (max (MU / εd) (Kd / rU)) (Kd * 3 ^ (ag + 2))) (by norm_num : (1 : ℝ) < 3)
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (1 / cdec) (by norm_num : (1 : ℝ) < 3)
  have hT31 : (1 : ℝ) ≤ 3 ^ N := one_le_pow₀ (by norm_num)
  have hN1 : MU ≤ εd * 3 ^ N := by
    have h1 : MU / εd ≤ 3 ^ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN.le
    rwa [div_le_iff₀ hεd, mul_comm] at h1
  have hN2 : Kd ≤ rU * 3 ^ N := by
    have h1 : Kd / rU ≤ 3 ^ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN.le
    rwa [div_le_iff₀ hrU, mul_comm] at h1
  have hN3 : Kd * 3 ^ (ag + 2) ≤ 3 ^ N := le_trans (le_max_right _ _) hN.le
  have hN4 : 1 ≤ cdec * 3 ^ N₀ := by
    have h1 : 1 / cdec ≤ 3 ^ N₀ := hN₀.le
    rwa [div_le_iff₀ hcdec, mul_comm] at h1
  have hKd0 : 0 < Kd := by linarith only [hKd]
  obtain ⟨cY, hcY⟩ : ∃ x : ℝ, x = (2 * Kd) ^ d := ⟨_, rfl⟩
  obtain ⟨sN, hsN⟩ : ∃ x : ℝ, x = Real.sqrt (((3 : ℝ) ^ N) ^ d) := ⟨_, rfl⟩
  obtain ⟨sN1, hsN1⟩ : ∃ x : ℝ, x = Real.sqrt (((3 : ℝ) ^ (N + 1)) ^ d) := ⟨_, rfl⟩
  obtain ⟨sK, hsK⟩ : ∃ x : ℝ, x = Real.sqrt cY := ⟨_, rfl⟩
  have hsN0 : 0 ≤ sN := hsN ▸ Real.sqrt_nonneg _
  have hsN10 : 0 ≤ sN1 := hsN1 ▸ Real.sqrt_nonneg _
  have hsK0 : 0 ≤ sK := hsK ▸ Real.sqrt_nonneg _
  have hcY1 : 1 ≤ cY := by
    rw [hcY]
    exact one_le_pow₀ (by linarith only [hKd])
  obtain ⟨a1, ha1⟩ : ∃ x : ℝ, x = 3 ^ N * sN := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ x : ℝ, x = 3 * 3 ^ N * sN1 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ x : ℝ, x = 2 * 3 ^ N * Ca * sK + MU * Ca + cY * ((d : ℝ) * Ca) :=
    ⟨_, rfl⟩
  have hCa0 : 0 ≤ Ca := by linarith only [hCa1]
  have ha10 : 0 ≤ a1 := by rw [ha1]; positivity
  have ha20 : 0 ≤ a2 := by rw [ha2]; positivity
  have ha30 : 0 ≤ a3 := by rw [ha3]; positivity
  refine ⟨Cdec * (a1 * Ca + a2 + MU) + 1, N + ag + 1 + N₀, ?_, lip_step_nat_a N ag N₀, ?_⟩
  · have : 0 ≤ Cdec * (a1 * Ca + a2 + MU) := by positivity
    linarith only [this]
  intro k₀ hk₀
  obtain ⟨A1, hA1⟩ : ∃ x : ℝ, x = 3 ^ k₀ * Real.sqrt (((3 : ℝ) ^ k₀) ^ d * κ) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ x : ℝ, x = (1 + 3 ^ k₀) * Ca := ⟨_, rfl⟩
  have hA10 : 0 ≤ A1 := by rw [hA1]; positivity
  have hA20 : 0 ≤ A2 := by rw [hA2]; positivity
  refine ⟨Cdec * (a1 * Ca + a3 + cY) + A1 * Ca + A2 + 1, ?_, ?_⟩
  · have : 0 ≤ Cdec * (a1 * Ca + a3 + cY) + A1 * Ca + A2 := by positivity
    linarith only [this]
  intro a W V rW M₂W DW nu s δ E θ lam Lam z x₀ k hnu hs hδ0 hδ1 hE hθ0 hθ1 hk hP1 hP2 hW hrW hMθ
    hzW hx₀F hx₀ hVo hBV hVk hell hlam hblk hc1 hc2 f g F G1 G2 u hg hF0 hG1 hG2 hDg hD2g hFae
    hsol hz p
  have hs0 : 0 < s := by linarith only [hs]
  obtain ⟨hNk, hk₀k, hag1, hNk₀⟩ := lip_step_nat_b hk₀ hk
  have hk1 : 1 ≤ k := (Nat.le_add_left 1 k₀).trans hk
  have ht : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hρle : (3 : ℝ) ^ (k - k₀) ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le k k₀)
  have hx₀k : ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 2 := by linarith only [hx₀, hρle]
  obtain ⟨gt, ub, hgt, hgt1, hgt2, hgtg, hubsol, htrace, hmain⟩ := hCa a W V rW M₂W DW nu s δ E
    lam Lam z x₀ k hnu hs hδ0 hδ1 hE hk1 hP1 hP2 hW hrW hzW hx₀k hVo hBV hVk hell hlam hblk hc1
    hc2 f g F G1 G2 u hg hF0 hG1 hG2 hDg hD2g hFae hsol hz
  clear hCa hP1 hP2 hlam hblk hc1 hc2 hDg hD2g hz
  obtain ⟨κV, hκV, hratioV⟩ := lip_bdry_approx_volume_ratio d M₁ rU hrU ag
  have hVQ0 : V ⊆ shiftCube z (k : ℤ) := by
    intro x hx
    rw [lip_bdry_approx_shiftCube_eq_ball]
    exact (hVk hx).1
  have hVW : V ⊆ W := fun x hx => (hVk hx).2
  obtain ⟨hV0, -⟩ := hratioV W V rW M₂W DW z k hW hrW hzW hBV hVQ0
  have hQ01 : shiftCube z (k : ℤ) ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) :=
    lip_bdry_approx_cube_mono z (Nat.le_succ k)
  have hQ12 : shiftCube z ((k + 1 : ℕ) : ℤ) ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) :=
    lip_bdry_approx_cube_mono z (Nat.le_succ (k + 1))
  have hD01 : shiftCube z (k : ℤ) ∩ W ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ01
  have hD12 : shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W :=
    Set.inter_subset_inter_left _ hQ12
  have hVD1 : V ⊆ shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W := fun x hx => hD01 ⟨hVQ0 hx, hVW hx⟩
  have hVD2 : V ⊆ shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W := hVD1.trans hD12
  have hD1o : IsOpen (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) :=
    (lip_bdry_approx_isOpen_cube z _).inter hW.1
  have hD2o : IsOpen (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) :=
    (lip_bdry_approx_isOpen_cube z _).inter hW.1
  have hVt : volume V ≠ ⊤ :=
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z k) (measure_mono hVQ0)
  have hVb : IsBoundedDomain V := lip_bdry_approx_isBoundedDomain hVQ0
  have hgt2' : ContDiff ℝ 2 gt := hgt.of_le (by simp)
  have hgtc : Continuous gt := hgt2'.continuous
  -- the scale `ℓ = 3^(k-N)`
  set ℓ : ℝ := (3 : ℝ) ^ (k - N) with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hℓN : ℓ * 3 ^ N = (3 : ℝ) ^ k := by
    rw [hℓdef, ← pow_add]; congr 1; exact Nat.sub_add_cancel hNk
  have hℓk : ℓ ≤ (3 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (Nat.sub_le k N)
  have hz3 : (3 : ℝ) ^ (((k - N : ℕ) : ℤ)) = ℓ := zpow_natCast _ _
  -- the replaced right-hand side and the function `φ`
  obtain ⟨f', hf'm, hf'b, -, hf'int⟩ := lip_bdry_approx_repl hD2o hVo hVD2 hell hsol hF0 hFae
  clear hell hFae
  have hubsol' : IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f' (fun _ => 0) := by
    intro φ
    rw [hubsol φ, hf'int φ]
  obtain ⟨φ, hφeq, hF₀L2, hφsol⟩ := lip_bdry_step_phi hVo hVb hVt hs0 hf'm hf'b ub hubsol' hgt
  clear hubsol hubsol'
  have hφf : φ.toFun = fun x => ub.toFun x - gt x := funext hφeq
  set G : Vec d := fun i => fderiv ℝ gt x₀ (basisVec i) with hGdef
  have hlapM : ∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ Ca * ((3 : ℝ) ^ k)⁻¹ * G1 := hgt2
  set BF : ℝ := s⁻¹ * F + (d : ℝ) * (Ca * ((3 : ℝ) ^ k)⁻¹ * G1) with hBF
  have hCaG : 0 ≤ Ca * ((3 : ℝ) ^ k)⁻¹ * G1 :=
    mul_nonneg (mul_nonneg hCa0 (inv_nonneg.2 ht.le)) hG1
  have hBF0 : 0 ≤ BF := by
    rw [hBF]
    exact add_nonneg (mul_nonneg (inv_nonneg.2 hs0.le) hF0) (mul_nonneg hd0.le hCaG)
  have hF₀b : ∀ᵐ x ∂volume.restrict V, |s⁻¹ * f' x +
      ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)| ≤ BF := by
    filter_upwards [hf'b] with x hx
    have h1 : |s⁻¹ * f' x| ≤ s⁻¹ * F := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hs0)]
      exact mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hs0.le)
    have h2 := lip_bdry_step_lap_le hgt hlapM x
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hF₀m : AEStronglyMeasurable (fun x => s⁻¹ * f' x +
      ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i)) (volume.restrict V) :=
    hF₀L2.aestronglyMeasurable
  -- the decay estimate
  set R₀ : ℝ := (3 : ℝ) ^ k / 3 ^ ag / 3 with hR₀
  have hVR : V ∩ Metric.ball x₀ R₀ = W ∩ Metric.ball x₀ R₀ := by
    ext y
    constructor
    · rintro ⟨hy, hb⟩; exact ⟨hVW hy, hb⟩
    · rintro ⟨hy, hb⟩
      exact ⟨hBV ⟨lip_bdry_step_ball_win hag1 hk₀k hx₀ hb, hy⟩, hb⟩
  have hKℓ9 : Kd * ℓ ≤ (3 : ℝ) ^ k / 3 ^ ag / 9 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have h3 : (3 : ℝ) ^ (ag + 2) = 3 ^ ag * 9 := by rw [pow_add]; norm_num
    calc Kd * ℓ * (3 ^ ag * 9) = (Kd * 3 ^ (ag + 2)) * ℓ := by rw [h3]; ring
      _ ≤ 3 ^ N * ℓ := mul_le_mul_of_nonneg_right hN3 hℓ.le
      _ = 3 ^ k := by rw [mul_comm]; exact hℓN
  have hpos9 : (0 : ℝ) < (3 : ℝ) ^ k / 3 ^ ag := by positivity
  have hρℓ : (3 : ℝ) ^ (k - k₀) ≤ cdec * ℓ := by
    have h1 : (3 : ℝ) ^ (k - k₀) * 3 ^ (N + N₀) ≤ 3 ^ k := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (lip_step_nat_c hk₀ hk₀k)
    have h2 : (3 : ℝ) ^ (k - k₀) * 3 ^ N₀ ≤ ℓ := by
      have h3 : ((3 : ℝ) ^ (k - k₀) * 3 ^ N₀) * 3 ^ N ≤ ℓ * 3 ^ N := by
        rw [hℓN]; calc _ = (3 : ℝ) ^ (k - k₀) * 3 ^ (N + N₀) := by rw [pow_add]; ring
          _ ≤ _ := h1
      exact le_of_mul_le_mul_right h3 (by positivity)
    have hρ0 : (0 : ℝ) < (3 : ℝ) ^ (k - k₀) := by positivity
    calc (3 : ℝ) ^ (k - k₀) = (3 : ℝ) ^ (k - k₀) * 1 := by ring
      _ ≤ (3 : ℝ) ^ (k - k₀) * (cdec * 3 ^ N₀) := mul_le_mul_of_nonneg_left hN4 hρ0.le
      _ = cdec * ((3 : ℝ) ^ (k - k₀) * 3 ^ N₀) := by ring
      _ ≤ cdec * ℓ := mul_le_mul_of_nonneg_left h2 hcdec.le
  have hρℓ1 : (3 : ℝ) ^ (k - k₀) ≤ ℓ := pow_le_pow_right₀ (by norm_num) (lip_step_nat_d hk₀ hk₀k)
  have hdec' := hdec V W (Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2)) rW M₂W DW R₀ ((k - N : ℕ) : ℤ) x₀
    hVo hVb Metric.isOpen_ball hW hx₀F hVR
  simp only [hz3] at hdec'
  have hdec2 := hdec' (by
      have h1 : M₂W * ℓ * 3 ^ N ≤ εd * 3 ^ N := by
        calc M₂W * ℓ * 3 ^ N = M₂W * (ℓ * 3 ^ N) := by ring
          _ = M₂W * 3 ^ k := by rw [hℓN]
          _ ≤ MU * θ := hMθ
          _ ≤ MU * 1 := mul_le_mul_of_nonneg_left hθ1 hMU
          _ ≤ εd * 3 ^ N := by linarith only [hN1]
      exact le_of_mul_le_mul_right h1 (by positivity))
    (by
      calc Kd * ℓ ≤ (rU * 3 ^ N) * ℓ := mul_le_mul_of_nonneg_right hN2 hℓ.le
        _ = rU * 3 ^ k := by rw [← hℓN]; ring
        _ ≤ rW := hrW)
    (by rw [hR₀]; linarith only [hKℓ9, hpos9])
    (lip_bdry_step_closedBall_win hag1 hk₀k
      (lip_bdry_step_dist_small hag1 hk₀k hx₀) hKℓ9) φ
    (fun x => s⁻¹ * f' x + ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i))
    hF₀L2 hφsol (by rw [hφf]; exact htrace) (by
      have : IsFiniteMeasure (volume.restrict (V ∩ Metric.ball x₀ (Kd * ℓ))) :=
        ⟨by simpa using (ne_top_of_le_ne_top hVt (measure_mono Set.inter_subset_left)).lt_top⟩
      refine MemLp.of_bound (hF₀m.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))
        BF ?_
      exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
        (hF₀b.mono fun x hx => by rwa [Real.norm_eq_abs]))
  obtain ⟨b, hb⟩ := hdec2 (p - G) (3 ^ (k - k₀)) (by positivity) hρℓ hρℓ1
  clear hdec hdec' hdec2
  rw [hφf] at hb
  beta_reduce at hb
  rw [show 1 - (d : ℝ) / (2 * (d : ℝ)) = 1 / 2 by field_simp; ring] at hb
  have hx₀Q2 : x₀ ∈ shiftCube z ((k + 2 : ℕ) : ℤ) := by
    rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball, dist_eq_norm]
    have h9 : (3 : ℝ) ^ (k + 2) = 9 * (3 : ℝ) ^ k := by rw [pow_add]; ring
    linarith only [hx₀k, h9, ht]
  have hKN : Kd ≤ 3 ^ N := by
    have h1 : (1 : ℝ) ≤ 3 ^ (ag + 2) := one_le_pow₀ (by norm_num)
    nlinarith only [hN3, h1, hKd0]
  set Φ : ℝ := lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p with hΦdef
  have hΦ0 : 0 ≤ Φ := by
    rw [hΦdef]; unfold lipPin lipL2
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  set Tt : ℝ := ((3 : ℝ)⁻¹) ^ k * lipL2 V (fun x => u.toFun x - ub.toFun x) with hTtdef
  have hTt : Tt ≤ Ca * (δ * (Φ + ‖p‖) + G1 + s⁻¹ * (3 : ℝ) ^ k * F + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) :=
    hmain p
  have hVball : V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) := fun x hx => by
    have := (hVk hx).1
    exact this
  have hSuball : shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W ⊆ Metric.ball z ((3 : ℝ) ^ (k + 1) / 2) := fun x hx => by
    have := hx.1
    rwa [lip_bdry_approx_shiftCube_eq_ball] at this
  have ht1 := lip_bdry_step_term1 (V := V) (Su := shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (z := z)
    (x₀ := x₀) (G := G) (p := p) (k := k) (N := N) (R := Kd * ℓ) (ℓ := ℓ) (Ca := Ca) (G1 := G1)
    (c₀ := g x₀) (Kd := Kd) (u := u.toFun) (ub := ub.toFun) (gt := gt) hVo hD1o hVD1 hV0 hVball
    hSuball (fun y hy => lip_bdry_approx_dist_le hx₀k hy.1) hℓ hℓN rfl hKd hKN hCa0 hG1
    (u.memL2.mono_measure (Measure.restrict_mono hD12 le_rfl)) ub.memL2 hgtc
    (by rw [abs_sub_comm]; exact hgtg x₀ hx₀Q2)
    (fun y hy => lip_bdry_step_taylor_R hgt2' hlapM x₀ y hy)
  rw [← hsN, ← hsN1, ← hcY, ← hsK, ← ha1, ← ha2] at ht1
  -- the pointwise bound of the right-hand side in the decay estimate
  have hSt : volume (V ∩ Metric.ball x₀ (Kd * ℓ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hVt (measure_mono Set.inter_subset_left)
  have hvS := (lip_bdry_step_vol_ball (c := x₀) (r := Kd * ℓ) (ℓ := ℓ) (by positivity) hℓ
    (Set.inter_subset_right : V ∩ Metric.ball x₀ (Kd * ℓ) ⊆ Metric.ball x₀ (Kd * ℓ))).2
  have eS : 2 * (Kd * ℓ) / ℓ = 2 * Kd := by field_simp
  rw [eS, ← hcY] at hvS
  have hq1 : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this]
  rw [← hTtdef, ← hΦdef] at ht1
  have hmS : AEStronglyMeasurable (fun x => s⁻¹ * f' x +
      ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i))
      (volume.restrict (V ∩ Metric.ball x₀ (Kd * ℓ))) :=
    hF₀m.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
  have hbS := ae_restrict_of_ae_restrict_of_subset
    (Set.inter_subset_left : V ∩ Metric.ball x₀ (Kd * ℓ) ⊆ V) hF₀b
  have hE3 := lip_bdry_step_bdd hSt hℓ hq1 hmS hBF0 hbS
  have hx0 : 0 ≤ (ℓ ^ d)⁻¹ * (volume (V ∩ Metric.ball x₀ (Kd * ℓ))).toReal :=
    mul_nonneg (inv_nonneg.2 (pow_nonneg hℓ.le d)) ENNReal.toReal_nonneg
  have hpow : ((ℓ ^ d)⁻¹ * (volume (V ∩ Metric.ball x₀ (Kd * ℓ))).toReal) ^ (1 / (2 * (d : ℝ))) ≤
      cY := by
    calc _ ≤ cY ^ (1 / (2 * (d : ℝ))) :=
          Real.rpow_le_rpow hx0 hvS (div_nonneg zero_le_one (mul_nonneg zero_le_two hd0.le))
      _ ≤ cY ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hcY1 (by
          rw [div_le_one (mul_pos two_pos hd0)]; exact hq1)
      _ = cY := Real.rpow_one _
  have hE3' := hE3.trans (mul_le_mul_of_nonneg_left hpow hBF0)
  have hGn : ‖G‖ ≤ Ca * G1 := (lip_bdry_step_grad_norm_le _).trans (hgt1 x₀)
  have hbn : ‖p - G‖ ≤ ‖p‖ + Ca * G1 := (norm_sub_le _ _).trans (by linarith only [hGn])
  have hM2 : M₂W * ℓ ≤ MU * θ := by
    by_cases hle : M₂W * ℓ ≤ 0
    · exact hle.trans (mul_nonneg hMU hθ0)
    · push Not at hle
      calc M₂W * ℓ ≤ M₂W * ℓ * 3 ^ N := le_mul_of_one_le_right hle.le hT31
        _ = M₂W * 3 ^ k := by rw [mul_assoc, hℓN]
        _ ≤ MU * θ := hMθ
  have hMid : M₂W * ℓ * ‖p - G‖ ≤ MU * θ * ‖p‖ + MU * Ca * G1 := by
    have h1 := mul_le_mul hM2 hbn (norm_nonneg _) (mul_nonneg hMU hθ0)
    have h2 : MU * θ * (Ca * G1) ≤ MU * Ca * G1 := by
      have := mul_le_mul_of_nonneg_left hθ1 (mul_nonneg hMU (mul_nonneg hCa0 hG1))
      linarith only [this]
    linarith only [h1, h2]
  have hℓE3 : ℓ * (eLpNorm (fun x => s⁻¹ * f' x +
      ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i))
      (ENNReal.ofReal (2 * (d : ℝ))) (p12_nmeas ℓ (V ∩ Metric.ball x₀ (Kd * ℓ)))).toReal ≤
      cY * (s⁻¹ * (3 : ℝ) ^ k * F) + cY * ((d : ℝ) * Ca) * G1 := by
    have h1 := mul_le_mul_of_nonneg_left hE3' hℓ.le
    have h2 : ℓ * (BF * cY) ≤ cY * (s⁻¹ * (3 : ℝ) ^ k * F) + cY * ((d : ℝ) * Ca) * G1 := by
      have hk1 : ℓ * ((3 : ℝ) ^ k)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one ht]; exact hℓk
      have e1 : ℓ * (s⁻¹ * F) ≤ s⁻¹ * (3 : ℝ) ^ k * F := by
        calc ℓ * (s⁻¹ * F) = s⁻¹ * F * ℓ := by ring
          _ ≤ s⁻¹ * F * 3 ^ k :=
              mul_le_mul_of_nonneg_left hℓk (mul_nonneg (inv_nonneg.2 hs0.le) hF0)
          _ = _ := by ring
      have e2 : ℓ * ((d : ℝ) * (Ca * ((3 : ℝ) ^ k)⁻¹ * G1)) ≤ (d : ℝ) * Ca * G1 := by
        have := mul_le_mul_of_nonneg_right hk1 (mul_nonneg (mul_nonneg hd0.le hCa0) hG1)
        calc _ = (ℓ * ((3 : ℝ) ^ k)⁻¹) * ((d : ℝ) * Ca * G1) := by ring
          _ ≤ 1 * ((d : ℝ) * Ca * G1) := this
          _ = _ := one_mul _
      have e3 : ℓ * BF ≤ s⁻¹ * (3 : ℝ) ^ k * F + (d : ℝ) * Ca * G1 := by
        rw [hBF, mul_add]; linarith only [e1, e2]
      have := mul_le_mul_of_nonneg_left e3 (by linarith only [hcY1] : 0 ≤ cY)
      calc ℓ * (BF * cY) = cY * (ℓ * BF) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    exact h1.trans h2
  have hQb : ℓ⁻¹ * (eLpNorm (fun y => ub.toFun y - gt y - vecDot (p - G) (y - x₀)) 2
        (p12_nmeas ℓ (V ∩ Metric.ball x₀ (Kd * ℓ)))).toReal +
      M₂W * ℓ * ‖p - G‖ + ℓ * (eLpNorm (fun x => s⁻¹ * f' x +
      ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i))
      (ENNReal.ofReal (2 * (d : ℝ))) (p12_nmeas ℓ (V ∩ Metric.ball x₀ (Kd * ℓ)))).toReal ≤
      a1 * Tt + a2 * Φ + a3 * G1 + MU * θ * ‖p‖ + cY * (s⁻¹ * (3 : ℝ) ^ k * F) := by
    rw [ha3]
    linarith only [ht1, hMid, hℓE3]
  generalize (ℓ⁻¹ * (eLpNorm (fun y => ub.toFun y - gt y - vecDot (p - G) (y - x₀)) 2
        (p12_nmeas ℓ (V ∩ Metric.ball x₀ (Kd * ℓ)))).toReal +
      M₂W * ℓ * ‖p - G‖ + ℓ * (eLpNorm (fun x => s⁻¹ * f' x +
      ∑ i, fderiv ℝ (fun y => fderiv ℝ gt y (basisVec i)) x (basisVec i))
      (ENNReal.ofReal (2 * (d : ℝ))) (p12_nmeas ℓ (V ∩ Metric.ball x₀ (Kd * ℓ)))).toReal) = Q at hb hQb
  -- the small patch
  set ρ : ℝ := (3 : ℝ) ^ (k - k₀) with hρdef
  have hρ0 : 0 < ρ := by positivity
  set D : Set (Vec d) := shiftCube z ((k - k₀ : ℕ) : ℤ) ∩ W with hDdef
  have hDV : D ⊆ V := lip_bdry_step_Dm_sub (Nat.le_of_succ_le hag1) hk₀k hBV
  have hDball : D ⊆ Metric.ball x₀ ρ := Set.inter_subset_left.trans (lip_bdry_step_Dm_ball hx₀)
  have hDo : IsOpen D := (lip_bdry_approx_isOpen_cube z _).inter hW.1
  obtain ⟨hD0, hvolκ⟩ := hratio W D rW M₂W DW z (k - k₀) hW
    (by
      calc rU * (3 : ℝ) ^ (k - k₀) ≤ rU * 3 ^ k := mul_le_mul_of_nonneg_left hρle hrU.le
        _ ≤ rW := hrW) hzW
    (by
      intro y hy
      refine ⟨?_, hy.2⟩
      rw [lip_bdry_approx_shiftCube_eq_ball]
      simpa using hy.1)
    Set.inter_subset_left
  have hvol : (volume V).toReal ≤ (((3 : ℝ) ^ k₀) ^ d * κ) * (volume D).toReal := by
    have e1 : (volume V).toReal ≤ ((3 : ℝ) ^ k) ^ d :=
      (ENNReal.toReal_mono (lip_bdry_approx_vol_cube_ne_top z k) (measure_mono hVQ0)).trans
        (by rw [lip_bdry_approx_vol_cube, ENNReal.toReal_ofReal (by positivity)])
    have e2 : (volume (shiftCube z ((k - k₀ + 2 : ℕ) : ℤ))).toReal =
        ((3 : ℝ) ^ (k - k₀ + 2)) ^ d := by
      rw [lip_bdry_approx_vol_cube, ENNReal.toReal_ofReal (by positivity)]
    have e3 : ((3 : ℝ) ^ k) ^ d ≤ ((3 : ℝ) ^ k₀) ^ d * ((3 : ℝ) ^ (k - k₀ + 2)) ^ d := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ d
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (lip_step_nat_g hk₀k)
    rw [e2] at hvolκ
    calc (volume V).toReal ≤ ((3 : ℝ) ^ k₀) ^ d * ((3 : ℝ) ^ (k - k₀ + 2)) ^ d := e1.trans e3
      _ ≤ ((3 : ℝ) ^ k₀) ^ d * (κ * (volume D).toReal) :=
          mul_le_mul_of_nonneg_left hvolκ (by positivity)
      _ = _ := by ring
  have hDsub : D ⊆ V ∩ Metric.ball x₀ ρ := fun y hy => ⟨hDV hy, hDball hy⟩
  have hb1 : ∀ᵐ x ∂volume.restrict D, |ub.toFun x - gt x - vecDot b (x - x₀)| ≤
      Cdec * ρ * (ρ / ℓ) ^ (1 / 2 : ℝ) * Q := ae_restrict_of_ae_restrict_of_subset hDsub hb
  have hB1nn : 0 ≤ Cdec * ρ * (ρ / ℓ) ^ (1 / 2 : ℝ) * Q := by
    have : (MeasureTheory.ae (volume.restrict D)).NeBot := by
      rw [MeasureTheory.ae_neBot]
      intro h
      apply hD0
      have := congrArg (fun m : Measure (Vec d) => m Set.univ) h
      simpa using this
    obtain ⟨y, hy⟩ := hb1.exists
    exact (abs_nonneg _).trans hy
  have hrpos : 0 < (ρ / ℓ) ^ (1 / 2 : ℝ) := by positivity
  have hQ0 : 0 ≤ Q := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg (by positivity : 0 < Cdec * ρ * (ρ / ℓ) ^ (1 / 2 : ℝ)) hneg
    linarith only [this, hB1nn]
  have hubD : AEStronglyMeasurable ub.toFun (volume.restrict D) :=
    ub.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hDV le_rfl)
  have hmeas : AEStronglyMeasurable (fun x => ub.toFun x - gt x - vecDot b (x - x₀))
      (volume.restrict D) :=
    (hubD.sub hgtc.aestronglyMeasurable).sub (lip_bdry_approx_continuous_aff b x₀).aestronglyMeasurable
  have humb : MemLp (fun x => u.toFun x - ub.toFun x) 2 (volume.restrict V) :=
    (u.memL2.mono_measure (Measure.restrict_mono hVD2 le_rfl)).sub ub.memL2
  have hDfin := lip_bdry_step_Dpart (D := D) (V := V) (u := u.toFun) (ub := ub.toFun) (gt := gt)
    (x₀ := x₀) (c₀ := g x₀) (b := b) (G := G) (j := k - k₀) (κ' := ((3 : ℝ) ^ k₀) ^ d * κ)
    (B1 := Cdec * ρ * (ρ / ℓ) ^ (1 / 2 : ℝ) * Q) (T := Ca * ((3 : ℝ) ^ k)⁻¹ * G1 * ρ * ρ)
    (Cc := Ca * (3 : ℝ) ^ k * G1) hDV hDo.measurableSet hD0 hVt hvol humb hmeas hgtc hB1nn
    (mul_nonneg (mul_nonneg hCaG hρ0.le) hρ0.le) (mul_nonneg (mul_nonneg hCa0 ht.le) hG1) hb1
    (fun x hx => lip_bdry_step_taylor_R hgt2' hlapM x₀ x (by
      have := hDball hx
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this.le))
    (hgtg x₀ hx₀Q2)
  refine ⟨b + G, ?_⟩
  clear hratio hmain htrace hφsol hF₀L2 hsol hmeas hubD humb hVo hBV hVk hW hrW hMθ hx₀F hf'int hf'm hf'b
  set Zj : ℝ := ((3 : ℝ)⁻¹) ^ (k - k₀) with hZjdef
  have h3k₀ : (3 : ℝ) ^ k₀ * ((3 : ℝ)⁻¹) ^ k₀ = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
  have hZk : (3 : ℝ) ^ k * ((3 : ℝ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
  have hZj : Zj = (3 : ℝ) ^ k₀ * ((3 : ℝ)⁻¹) ^ k := by
    have h1 : ((3 : ℝ)⁻¹) ^ k = Zj * ((3 : ℝ)⁻¹) ^ k₀ := by
      rw [hZjdef, ← pow_add]; congr 1; exact (Nat.sub_add_cancel hk₀k).symm
    rw [h1]
    calc Zj = Zj * ((3 : ℝ) ^ k₀ * ((3 : ℝ)⁻¹) ^ k₀) := by rw [h3k₀, mul_one]
      _ = _ := by ring
  have hjρ : Zj * ρ = 1 := by
    rw [hZjdef, hρdef, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
  have hkj : (3 : ℝ) ^ k * Zj = 3 ^ k₀ := by
    rw [hZj]
    calc (3 : ℝ) ^ k * ((3 : ℝ) ^ k₀ * ((3 : ℝ)⁻¹) ^ k) =
        (3 : ℝ) ^ k₀ * ((3 : ℝ) ^ k * ((3 : ℝ)⁻¹) ^ k) := by ring
      _ = _ := by rw [hZk, mul_one]
  have hbase0 : 0 ≤ (Real.sqrt 3)⁻¹ := by positivity
  have hbase1 : (Real.sqrt 3)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hρℓeq : ρ / ℓ = ((3 : ℝ)⁻¹) ^ (k₀ - N) := by
    rw [div_eq_iff hℓ.ne']
    have hℓ' : ℓ = ρ * 3 ^ (k₀ - N) := by
      rw [hℓdef, hρdef, ← pow_add]; congr 1; exact lip_step_nat_e hNk₀ hk₀k
    have h4 : ((3 : ℝ)⁻¹) ^ (k₀ - N) * (3 : ℝ) ^ (k₀ - N) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
    rw [hℓ']
    calc ρ = ρ * (((3 : ℝ)⁻¹) ^ (k₀ - N) * (3 : ℝ) ^ (k₀ - N)) := by rw [h4, mul_one]
      _ = _ := by ring
  set r0 : ℝ := (ρ / ℓ) ^ (1 / 2 : ℝ) with hr0def
  have hr0 : r0 = ((Real.sqrt 3)⁻¹) ^ (k₀ - N) := by
    rw [hr0def, hρℓeq, lip_bdry_step_rpow_half]
  have hr01 : r0 ≤ ((Real.sqrt 3)⁻¹) ^ (k₀ - (N + ag + 1 + N₀)) := by
    rw [hr0]
    exact pow_le_pow_of_le_one hbase0 hbase1 (lip_step_nat_f N ag N₀ k₀)
  have hr0' : r0 ≤ 1 := hr01.trans (pow_le_one₀ hbase0 hbase1)
  have hr00 : 0 ≤ r0 := hrpos.le
  have hFm : lipPin D (k - k₀) x₀ (g x₀) u.toFun (b + G) ≤ A1 * Tt + Cdec * r0 * Q + A2 * G1 := by
    refine hDfin.trans ?_
    have eA : Zj * (Real.sqrt (((3 : ℝ) ^ k₀) ^ d * κ) *
        lipL2 V (fun x => u.toFun x - ub.toFun x)) = A1 * Tt := by
      rw [hA1, hTtdef, hZj]; ring
    have eB : Zj * (Cdec * ρ * r0 * Q) = Cdec * r0 * Q := by
      calc Zj * (Cdec * ρ * r0 * Q) = Cdec * r0 * Q * (Zj * ρ) := by ring
        _ = _ := by rw [hjρ, mul_one]
    have eT : Zj * (Ca * ((3 : ℝ) ^ k)⁻¹ * G1 * ρ * ρ) ≤ Ca * G1 := by
      have h1 : ((3 : ℝ) ^ k)⁻¹ * ρ ≤ 1 := by
        rw [← div_eq_inv_mul, div_le_one ht]; exact hρle
      calc Zj * (Ca * ((3 : ℝ) ^ k)⁻¹ * G1 * ρ * ρ) =
          (Ca * G1) * (((3 : ℝ) ^ k)⁻¹ * ρ) * (Zj * ρ) := by ring
        _ = (Ca * G1) * (((3 : ℝ) ^ k)⁻¹ * ρ) := by rw [hjρ, mul_one]
        _ ≤ (Ca * G1) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := mul_one _
    have eC : Zj * (Ca * (3 : ℝ) ^ k * G1) = Ca * 3 ^ k₀ * G1 := by
      calc Zj * (Ca * (3 : ℝ) ^ k * G1) = Ca * G1 * ((3 : ℝ) ^ k * Zj) := by ring
        _ = _ := by rw [hkj]; ring
    rw [hA2, mul_add, mul_add, mul_add]
    linarith only [eA, eB, eT, eC]
  have hrel := lip_bdry_step_arith (Ca := Ca) (Cdec := Cdec) (MU := MU) (a1 := a1) (a2 := a2)
    (a3 := a3) (a4 := cY) (A1 := A1) (A2 := A2) (C₁ := Cdec * (a1 * Ca + a2 + MU) + 1)
    (C₂ := Cdec * (a1 * Ca + a3 + cY) + A1 * Ca + A2 + 1) (r0 := r0)
    (r1 := ((Real.sqrt 3)⁻¹) ^ (k₀ - (N + ag + 1 + N₀))) (δ := δ) (θ := θ) (Φ := Φ) (P := ‖p‖)
    (G1 := G1) (Fs := s⁻¹ * (3 : ℝ) ^ k * F) (Gk := (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) (Tt := Tt)
    (Q := Q) (Fm := lipPin D (k - k₀) x₀ (g x₀) u.toFun (b + G)) hCa0 hCdec.le hMU ha10 ha20 ha30
    (by linarith only [hcY1]) hA10 hA20 hr00 hr01 hr0' hδ0 hδ1 hθ0 hΦ0 (norm_nonneg _) hG1
    (mul_nonneg (mul_nonneg (inv_nonneg.2 hs0.le) ht.le) hF0)
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) ht.le) hG2)
    (by linarith only) (by linarith only) hTt hQb hFm
  exact hrel


/-- Witness: the numerical and geometric hypotheses of `lip_bdry_step` hold together on the unit
ball, with a frontier point at the centre distance `1`. -/
example [NeZero d] (k₀ : ℕ) :
    ∃ (M₁ MU rU : ℝ) (W V : Set (Vec d)) (rW M₂W DW nu s δ E θ : ℝ) (z x₀ : Vec d)
      (k A ag : ℕ), 0 < rU ∧ 0 ≤ MU ∧ 0 < nu ∧ 1 ≤ s ∧ 0 ≤ δ ∧ δ ≤ 1 ∧ 0 ≤ E ∧ 0 ≤ θ ∧ θ ≤ 1 ∧
      k₀ + 1 ≤ k ∧ ((k : ℝ) ^ A)⁻¹ * Real.sqrt s ≤ δ * Real.sqrt nu ∧
      ((k : ℝ) ^ A)⁻¹ * s ≤ 1 ∧ IsUniformC11Domain W rW M₁ M₂W DW ∧ rU * (3 : ℝ) ^ k ≤ rW ∧
      M₂W * (3 : ℝ) ^ k ≤ MU * θ ∧ z ∈ W ∧ x₀ ∈ frontier W ∧
      ‖x₀ - z‖ ≤ (3 : ℝ) ^ (k - k₀) / 2 ∧ IsOpen V ∧
      Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V ∧
      V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ W := by
  obtain ⟨r, M₁, M₂, D, h⟩ := isUniformC11Domain_euclidBall (d := d)
  have hr : 0 < r := h.2.1
  have hbd : ∀ x ∈ closure (Section6.euclidBall (d := d) 1), ‖x‖ ≤ 1 := by
    have hcl : IsClosed {x : Vec d | vecNormSq x ≤ 1} := by
      refine isClosed_le ?_ continuous_const
      unfold vecNormSq vecDot
      exact continuous_finsetSum _ fun i _ => ((continuous_apply i).mul (continuous_apply i))
    have hsub : Section6.euclidBall (d := d) 1 ⊆ {x : Vec d | vecNormSq x ≤ 1} := by
      intro x hx
      have : vecNormSq x < 1 ^ 2 := hx
      exact (by linarith only [this] : vecNormSq x ≤ 1)
    intro x hx
    have h1 : vecNormSq x ≤ 1 := closure_minimal hsub hcl hx
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have h2 : x i * x i ≤ vecNormSq x := by
      unfold vecNormSq vecDot
      exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    exact abs_le_one_iff_mul_self_le_one.2 (h2.trans h1)
  have hfr : (frontier (Section6.euclidBall (d := d) 1)).Nonempty := by
    by_contra hcon
    have hfe : frontier (Section6.euclidBall (d := d) 1) = ∅ := Set.not_nonempty_iff_eq_empty.1 hcon
    have hclo : IsClopen (Section6.euclidBall (d := d) 1) := isClopen_iff_frontier_eq_empty.2 hfe
    rcases isClopen_iff.1 hclo with h0 | h0
    · have := Section6.zero_mem_euclidBall (d := d) one_pos
      rw [h0] at this
      exact this
    · have hbig : (fun _ => (2 : ℝ) : Vec d) ∈ Section6.euclidBall (d := d) 1 := by
        rw [h0]; trivial
      have : vecNormSq (fun _ => (2 : ℝ) : Vec d) < 1 ^ 2 := hbig
      have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
      simp only [vecNormSq, vecDot, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
      nlinarith only [this, hd0]
  obtain ⟨x₀, hx₀⟩ := hfr
  have hx₀n : ‖x₀‖ ≤ 1 := hbd x₀ (frontier_subset_closure hx₀)
  refine ⟨M₁, |M₂| * 3 ^ (k₀ + 1), r / 3 ^ (k₀ + 1), Section6.euclidBall (d := d) 1,
    Metric.ball (0 : Vec d) ((3 : ℝ) ^ (k₀ + 1) / 3 ^ 0 / 2) ∩ Section6.euclidBall (d := d) 1,
    r, M₂, D, 1, 1, 1, 0, 1, 0, x₀, k₀ + 1, 1, 0, by positivity, by positivity, one_pos, le_rfl,
    zero_le_one, le_rfl, le_rfl, zero_le_one, le_rfl, le_rfl, ?_, ?_, h, ?_, ?_, Section6.zero_mem_euclidBall one_pos,
    hx₀, ?_, ?_, ?_, ?_⟩
  · have hk : (1 : ℝ) ≤ ((k₀ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k₀
    simpa using inv_le_one_of_one_le₀ hk
  · have hk : (1 : ℝ) ≤ ((k₀ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k₀
    simpa using inv_le_one_of_one_le₀ hk
  · rw [div_mul_cancel₀ _ (by positivity)]
  · calc M₂ * (3 : ℝ) ^ (k₀ + 1) ≤ |M₂| * 3 ^ (k₀ + 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = |M₂| * 3 ^ (k₀ + 1) * 1 := (mul_one _).symm
  · simp only [sub_zero]
    refine hx₀n.trans ?_
    rw [Nat.add_sub_cancel_left]
    norm_num
  · exact Metric.isOpen_ball.inter h.1
  · exact Set.Subset.rfl
  · refine Set.inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    norm_num

end SuperdiffusionCLT.Section7
