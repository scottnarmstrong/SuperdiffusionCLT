/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryDet

/-!
# The boundary large-scale Lipschitz estimate, deterministic form

`lip_bdry_det`: the pinned flatness `Φ_j(0)` at the scales `n₁ ≤ j ≤ mt` is bounded by the pinned
flatness at the top scale plus the data terms, and so is the gradient on the cube of the scale
`j`.  The proof applies the abstract iteration to the one-step inequality `lip_bdry_step`, the
slope comparison and restriction bounds of the pinned flatness, and the monotonicity of the
blocks in the scale of the homogenized coefficient.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

private theorem lip_det_nat1 {k mt : ℕ} (h : k + 1 ≤ mt - 1) : k + 2 ≤ mt := by omega

private theorem lip_det_nat3 {n m : ℕ} (h : n ≤ m) : n ≤ m - 1 ∨ n = m := by omega

private theorem lip_det_nat4 {k₀ n₁ mt k : ℕ} (hn₁ : k₀ + 3 ≤ n₁)
    (hk : n₁ + k₀ ≤ k ∧ k ≤ mt - 1 - 1) : n₁ ≤ k ∧ k + 2 ≤ mt := by omega

private theorem lip_det_nat5 {k mt : ℕ} (h : k + 2 ≤ mt) : k < mt := by omega

private theorem lip_det_nat6 {k₀ n₁ : ℕ} (h : k₀ + 3 ≤ n₁) : 0 < n₁ := by omega

private theorem lip_det_nat7 {n₁ k₀ mt : ℕ} (h : n₁ ≤ mt) :
    (mt - 1 - 1 + 1 - (n₁ + k₀) : ℕ) + n₁ ≤ mt + 1 := by omega

private theorem lip_det_nat8 {j mt : ℕ} (h : j ≤ mt) (hne : ¬ j = mt) : j ≤ mt - 1 := by omega

private theorem lip_det_nat10 {k₀ n₁ mt : ℕ} (hn₁ : k₀ + 3 ≤ n₁) (hn₁mt : n₁ ≤ mt) : 1 ≤ mt := by
  omega

private theorem lip_det_nat11 {k₀ n₁ j : ℕ} (hn₁ : k₀ + 3 ≤ n₁) (hj : n₁ ≤ j) : 1 ≤ j := by omega

private theorem lip_det_nat12 {k₀ n₁ k : ℕ} (hn₁ : k₀ + 3 ≤ n₁) (hk : n₁ + k₀ ≤ k) :
    k₀ + 1 ≤ k := by omega

private theorem lip_det_a_nonneg {C₂ G1 G2 E F s : ℝ} {k : ℕ} (hC : 0 ≤ C₂) (hG1 : 0 ≤ G1)
    (hG2 : 0 ≤ G2) :
    0 ≤ C₂ * (G1 + max (s⁻¹ * (3 : ℝ) ^ k * F) 0 + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) := by
  positivity

private theorem lip_det_b_nonneg {C₁ C₂ δ : ℝ} {m l : ℕ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ C₂ * max δ 0 + C₁ * ((Real.sqrt 3)⁻¹) ^ m * ((3 : ℝ)⁻¹) ^ l := by
  positivity

/-- **The boundary large-scale Lipschitz estimate, deterministic form**,
between the scales `n₁` and `mt`, for a frontier point `x₀` within `3^{n₁}/2` of the centre. -/
theorem lip_bdry_det (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cin M₁ MU rU : ℝ) (hCin : 1 ≤ Cin)
    (hrU : 0 < rU) (hMU : 0 ≤ MU) (ag A : ℕ) :
    ∃ (C c : ℝ) (k₀ : ℕ), 1 ≤ C ∧ 0 < c ∧
      ∀ (a : CoeffField d) (W : Set (Vec d)) (rW M₂W DW nu E lam Lam : ℝ) (s δ : ℕ → ℝ)
        (z x₀ : Vec d) (n₁ mt : ℕ),
        0 < nu → 0 ≤ E → k₀ + 3 ≤ n₁ → n₁ ≤ mt →
        (∀ k, n₁ ≤ k → k ≤ mt →
          1 ≤ s k ∧ s mt ≤ 2 * s k ∧ s k ≤ 2 * s mt ∧ 0 ≤ δ k ∧
            ((k : ℝ) ^ A)⁻¹ * Real.sqrt (s k) ≤ δ k * Real.sqrt nu ∧
            ((k : ℝ) ^ A)⁻¹ * s k ≤ 1) →
        ∑ k ∈ Finset.Icc n₁ mt, δ k ≤ c →
        IsUniformC11Domain W rW M₁ M₂W DW → rU * (3 : ℝ) ^ mt ≤ rW →
        M₂W * (3 : ℝ) ^ mt ≤ MU →
        z ∈ W → x₀ ∈ frontier W → ‖x₀ - z‖ ≤ (3 : ℝ) ^ n₁ / 2 →
        IsEllipticFieldOn lam Lam (shiftCube z (mt : ℤ) ∩ W) a → 0 < lam →
        (∀ k, n₁ ≤ k → k ≤ mt → LipCaccBdryS a nu (s k) Cin E W z k) →
        (∀ k, n₁ ≤ k → k ≤ mt → ∃ V : Set (Vec d), IsOpen V ∧
          Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V ∧
          V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ W ∧ LipL2Block a nu (s k) (δ k) Cin A k V) →
        ∀ (f g : Vec d → ℝ) (F G1 G2 : ℝ) (u : H1Function (shiftCube z (mt : ℤ) ∩ W)),
          ContDiff ℝ 2 g → 0 ≤ F → 0 ≤ G1 → 0 ≤ G2 →
          (∀ x ∈ shiftCube z (mt : ℤ), ‖fderiv ℝ g x‖ ≤ G1) →
          (∀ x ∈ shiftCube z (mt : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) →
          (∀ᵐ x ∂volume.restrict (shiftCube z (mt : ℤ) ∩ W), |f x| ≤ F) →
          IsWeakSolutionOn a (shiftCube z (mt : ℤ) ∩ W) u f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (shiftCube z (mt : ℤ) ∩ W) (shiftCube z (mt : ℤ))
            (fun x => u.toFun x - g x) →
          ∀ j, n₁ ≤ j → j ≤ mt →
            lipPin (shiftCube z (j : ℤ) ∩ W) j x₀ (g x₀) u.toFun 0 ≤
                C * (lipPin (shiftCube z (mt : ℤ) ∩ W) mt x₀ (g x₀) u.toFun 0 +
                  ((mt : ℝ) - (n₁ : ℝ) + 1) * G1 + (s mt)⁻¹ * (3 : ℝ) ^ mt * F +
                  (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2) ∧
              (j + 1 ≤ mt →
                (Real.sqrt (s mt))⁻¹ * Real.sqrt nu *
                    lipGradL2 (shiftCube z (j : ℤ) ∩ W) u.grad ≤
                  C * (lipPin (shiftCube z (mt : ℤ) ∩ W) mt x₀ (g x₀) u.toFun 0 +
                    ((mt : ℝ) - (n₁ : ℝ) + 1) * G1 + (s mt)⁻¹ * (3 : ℝ) ^ mt * F +
                    (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2)) := by
  classical
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hCin4 : 1 ≤ 4 * Cin := by linarith only [hCin]
  obtain ⟨c', hc'0, hc'1, hinner⟩ := lip_bdry_det_inner d M₁ rU hrU
  obtain ⟨Cs, hCs0, hslope⟩ := lip_pin_slope d c' hc'0 hc'1
  obtain ⟨Cr, hCr1, hrestr⟩ := lip_pin_restrict d c' hc'0 hc'1
  obtain ⟨C₁, a₁, hC₁, ha₁, hstep⟩ := lip_bdry_step d hd (4 * Cin) M₁ MU rU hCin4 hrU hMU ag A
  have hC₁0 : 0 < C₁ := by linarith only [hC₁]
  have hCs1 : 0 < Cs + 1 := by linarith only [hCs0]
  have hε : 0 < 1 / (24 * (Cs + 1)) := by positivity
  have hs3 : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one (by norm_num)
  have hb1 : (Real.sqrt 3)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs3
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (div_pos hε hC₁0) hb1
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, k₀ = a₁ + t := ⟨_, rfl⟩
  have hk₀a : a₁ ≤ k₀ := hk₀ ▸ Nat.le_add_right a₁ t
  obtain ⟨C₂, hC₂, hstep2⟩ := hstep k₀ hk₀a
  have hC₂0 : 0 < C₂ := by linarith only [hC₂]
  obtain ⟨Cit, hCit, hit⟩ := lip_iteration Cs (d : ℝ) Cr hCs0 (by positivity) hCr1 k₀
  have hr1 : C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) ≤ 1 / (24 * (Cs + 1)) := by
    have : k₀ - a₁ = t := by rw [hk₀]; exact Nat.add_sub_cancel_left _ _
    rw [this]
    have h2 := (lt_div_iff₀ hC₁0).1 ht
    linarith only [h2, mul_comm C₁ (((Real.sqrt 3)⁻¹) ^ t)]
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Cit * (Cr + 2 * C₂) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by
    rw [hK]
    calc (1 : ℝ) ≤ Cit * 1 := by linarith only [hCit]
      _ ≤ Cit * (Cr + 2 * C₂) :=
          mul_le_mul_of_nonneg_left (by linarith only [hCr1, hC₂]) (by linarith only [hCit])
  refine ⟨2 * Cin * (K + 3), 1 / (16 * C₂ * (Cs + 1)), k₀, ?_, by positivity, ?_⟩
  · nlinarith only [hCin, hK1]
  intro a W rW M₂W DW nu E lam Lam s δ z x₀ n₁ mt hnu hE hn₁ hn₁mt hsδ hsum hW hrW hMW hzW hfr
    hx₀F hell hlam hcacc hL2 f g F G1 G2 u hg hF0 hG1 hG2 hDg hD2g hFae hsol hz
  have hs1 : ∀ k, n₁ ≤ k → k ≤ mt → 1 ≤ s k := fun k h1 h2 => (hsδ k h1 h2).1
  have hsm : ∀ k, n₁ ≤ k → k ≤ mt → s mt ≤ 2 * s k := fun k h1 h2 => (hsδ k h1 h2).2.1
  have hsk : ∀ k, n₁ ≤ k → k ≤ mt → s k ≤ 2 * s mt := fun k h1 h2 => (hsδ k h1 h2).2.2.1
  have hδ0 : ∀ k, n₁ ≤ k → k ≤ mt → 0 ≤ δ k := fun k h1 h2 => (hsδ k h1 h2).2.2.2.1
  have hP1 : ∀ k, n₁ ≤ k → k ≤ mt → ((k : ℝ) ^ A)⁻¹ * Real.sqrt (s k) ≤ δ k * Real.sqrt nu :=
    fun k h1 h2 => (hsδ k h1 h2).2.2.2.2.1
  have hP2 : ∀ k, n₁ ≤ k → k ≤ mt → ((k : ℝ) ^ A)⁻¹ * s k ≤ 1 :=
    fun k h1 h2 => (hsδ k h1 h2).2.2.2.2.2
  have hs0 : ∀ k, n₁ ≤ k → k ≤ mt → 0 < s k := fun k h1 h2 => by linarith only [hs1 k h1 h2]
  have hsmt : 1 ≤ s mt := hs1 mt hn₁mt le_rfl
  -- geometry of the cubes
  have hDo : ∀ j : ℕ, IsOpen (shiftCube z (j : ℤ) ∩ W) := fun j =>
    (lip_bdry_approx_isOpen_cube z j).inter hW.1
  have hDmono : ∀ j j' : ℕ, j ≤ j' → shiftCube z (j : ℤ) ∩ W ⊆ shiftCube z (j' : ℤ) ∩ W :=
    fun j j' h => Set.inter_subset_inter_left _ (lip_bdry_approx_cube_mono z h)
  have hDball : ∀ j : ℕ, shiftCube z (j : ℤ) ∩ W ⊆ Metric.ball z ((3 : ℝ) ^ j / 2) := fun j y hy => by
    have := hy.1
    rwa [lip_bdry_approx_shiftCube_eq_ball] at this
  have hqex : ∀ j : ℕ, j ≤ mt → ∃ q : Vec d,
      Metric.ball q (c' * (3 : ℝ) ^ j) ⊆ shiftCube z (j : ℤ) ∩ W :=
    fun j hj => hinner W rW M₂W DW z j mt hW hrW hj hzW
  have hvol : ∀ j : ℕ, j ≤ mt → volume (shiftCube z (j : ℤ) ∩ W) ≠ 0 := by
    intro j hj h0
    obtain ⟨q, hq⟩ := hqex j hj
    have h1 := measure_mono (μ := volume) hq
    rw [h0] at h1
    exact (Metric.measure_ball_pos volume q (by positivity)).ne' (le_antisymm h1 bot_le)
  have hmem : ∀ j : ℕ, j ≤ mt → MemLp u.toFun 2 (volume.restrict (shiftCube z (j : ℤ) ∩ W)) :=
    fun j hj => u.memL2.mono_measure (Measure.restrict_mono (hDmono j mt hj) le_rfl)
  have hx₀j : ∀ j : ℕ, n₁ ≤ j → ‖x₀ - z‖ ≤ (3 : ℝ) ^ j / 2 := fun j hj => by
    have : (3 : ℝ) ^ n₁ ≤ 3 ^ j := pow_le_pow_right₀ (by norm_num) hj
    linarith only [hx₀F, this]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → Vec d → ℝ, ∀ j p,
      Φ j p = lipPin (shiftCube z (j : ℤ) ∩ W) j x₀ (g x₀) u.toFun p := ⟨_, fun _ _ => rfl⟩
  have hΦ0 : ∀ j p, 0 ≤ Φ j p := by
    intro j p
    rw [hΦ]; unfold lipPin lipL2
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hslope' : ∀ j, n₁ ≤ j → j + 1 ≤ mt → ∀ p q : Vec d,
      ‖p‖ ≤ ‖q‖ + Cs * (Φ j p + Φ (j + 1) q) := by
    intro j hj1 hj2 p q
    obtain ⟨qq, hqq⟩ := hqex j (Nat.le_of_succ_le hj2)
    have h := hslope (shiftCube z (j : ℤ) ∩ W) (shiftCube z ((j + 1 : ℕ) : ℤ) ∩ W) z qq x₀ j
      (g x₀) u.toFun p q (hDo j).measurableSet (hDo (j + 1)).measurableSet
      (hDmono j (j + 1) (Nat.le_succ j)) hqq (hDball (j + 1)) (hmem (j + 1) hj2)
    rw [hΦ, hΦ]
    have h2 : ‖p‖ ≤ ‖q‖ + ‖p - q‖ := by
      have := norm_add_le q (p - q)
      simpa using this
    linarith only [h, h2]
  have hrestr' : ∀ j, n₁ ≤ j → j + 1 ≤ mt → ∀ p : Vec d, Φ j p ≤ Cr * Φ (j + 1) p := by
    intro j hj1 hj2 p
    obtain ⟨qq, hqq⟩ := hqex j (Nat.le_of_succ_le hj2)
    rw [hΦ, hΦ]
    exact hrestr (shiftCube z (j : ℤ) ∩ W) (shiftCube z ((j + 1 : ℕ) : ℤ) ∩ W) z qq x₀ j
      (g x₀) u.toFun p (hDo j).measurableSet (hDo (j + 1)).measurableSet
      (hDmono j (j + 1) (Nat.le_succ j)) hqq (hDball (j + 1)) (hmem (j + 1) hj2)
  have hosc' : ∀ j, n₁ ≤ j → j ≤ mt → ∀ p : Vec d, Φ j 0 ≤ Φ j p + (d : ℝ) * ‖p‖ := by
    intro j hj1 hj2 p
    rw [hΦ, hΦ]
    exact lip_pin_zero d (shiftCube z (j : ℤ) ∩ W) z x₀ j (g x₀) u.toFun p
      (hDo j).measurableSet (hDball j) (hx₀j j hj1) (hvol j hj2) (hmem j hj2)
  -- the smallness of `δ`
  have hcle : 1 / (16 * C₂ * (Cs + 1)) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : (1 : ℝ) ≤ Cs + 1 := by linarith only [hCs0]
    nlinarith only [mul_le_mul hC₂ h1 zero_le_one (by linarith only [hC₂])]
  have hδc : ∀ k, n₁ ≤ k → k ≤ mt → δ k ≤ 1 / (16 * C₂ * (Cs + 1)) := fun k h1 h2 =>
    le_trans (Finset.single_le_sum (f := δ) (fun i hi => by
      rw [Finset.mem_Icc] at hi; exact hδ0 i hi.1 hi.2) (Finset.mem_Icc.2 ⟨h1, h2⟩)) hsum
  have hC₂δ : ∀ k, n₁ ≤ k → k ≤ mt → C₂ * δ k ≤ 1 / 16 := by
    intro k h1 h2
    have e1 : C₂ * δ k ≤ C₂ * (1 / (16 * C₂ * (Cs + 1))) :=
      mul_le_mul_of_nonneg_left (hδc k h1 h2) hC₂0.le
    have e2 : C₂ * (1 / (16 * C₂ * (Cs + 1))) = 1 / (16 * (Cs + 1)) := by field_simp
    have e3 : 1 / (16 * (Cs + 1)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hCs0]
    linarith only [e1, e2, e3]
  have hr1' : C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) ≤ 1 / 24 := by
    refine hr1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hCs0]
  -- the one-step inequality
  have hone : ∀ k, n₁ + k₀ ≤ k → k + 1 ≤ mt - 1 → ∀ p : Vec d, ∃ p' : Vec d,
      Φ (k - k₀) p' ≤ 1 / 2 * Φ (k + 1) p +
        (C₂ * max (δ k) 0 + C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) * ((3 : ℝ)⁻¹) ^ (mt - k)) * ‖p‖ +
          C₂ * (G1 + max ((s k)⁻¹ * (3 : ℝ) ^ k * F) 0 + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) := by
    intro k hk1 hk2 p
    have hk0 : n₁ ≤ k := (Nat.le_add_right n₁ k₀).trans hk1
    have hk3 : k + 2 ≤ mt := lip_det_nat1 hk2
    have hkm : k ≤ mt := (Nat.le_add_right k 2).trans hk3
    obtain ⟨V, hVo, hBV, hVk, hVblk⟩ := hL2 k hk0 hkm
    have hcb : ∀ j, n₁ ≤ j → j ≤ mt → LipCaccBdryS a nu (s k) (4 * Cin) E W z j := by
      intro j hj1 hj2
      have h1 := (hcacc j hj1 hj2).monoC (hs0 j hj1 hj2) (hsk j hj1 hj2) (hsm j hj1 hj2)
        (by linarith only [hCin]) (le_refl (2 * Cin))
      exact h1.monoC (hs0 mt hn₁mt le_rfl) (hsm k hk0 hkm) (hsk k hk0 hkm)
        (by linarith only [hCin]) (by linarith only [hCin])
    have hc1 := hcb (k + 1) (hk0.trans (Nat.le_succ k)) (Nat.le_of_succ_le hk3)
    have hc2 := hcb (k + 2) (hk0.trans (Nat.le_add_right k 2)) hk3
    have hblk' : LipL2Block a nu (s k) (δ k) (4 * Cin) A k V :=
      hVblk.mono_const (hδ0 k hk0 hkm) (by linarith only [hCin])
    have hθ0 : 0 ≤ ((3 : ℝ)⁻¹) ^ (mt - k) := by positivity
    have hθ1 : ((3 : ℝ)⁻¹) ^ (mt - k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hMθ : M₂W * (3 : ℝ) ^ k ≤ MU * ((3 : ℝ)⁻¹) ^ (mt - k) := by
      have e : (3 : ℝ) ^ k = (3 : ℝ) ^ mt * ((3 : ℝ)⁻¹) ^ (mt - k) := by
        have h1 : (3 : ℝ) ^ k * 3 ^ (mt - k) = 3 ^ mt := by rw [← pow_add]; congr 1; exact Nat.add_sub_of_le hkm
        have h2 : (3 : ℝ) ^ (mt - k) * ((3 : ℝ)⁻¹) ^ (mt - k) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow]
        calc (3 : ℝ) ^ k = (3 : ℝ) ^ k * ((3 : ℝ) ^ (mt - k) * ((3 : ℝ)⁻¹) ^ (mt - k)) := by
              rw [h2, mul_one]
          _ = _ := by rw [← mul_assoc, h1]
      rw [e, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hMW hθ0
    have hrW' : rU * (3 : ℝ) ^ k ≤ rW :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hkm) hrU.le) hrW
    have hx₀' : ‖x₀ - z‖ ≤ (3 : ℝ) ^ (k - k₀) / 2 := hx₀j (k - k₀) (Nat.le_sub_of_add_le hk1)
    have hell' : IsEllipticFieldOn lam Lam (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) a :=
      hell.mono (hDo (k + 2)).measurableSet (hDmono (k + 2) mt hk3)
    have hsol' := IsWeakSolutionOn.restrict' hsol (hDo (k + 2)) (hDmono (k + 2) mt hk3)
    have hagree : (shiftCube z (mt : ℤ) ∩ W) ∩ shiftCube z ((k + 2 : ℕ) : ℤ) =
        (shiftCube z ((k + 2 : ℕ) : ℤ) ∩ W) ∩ shiftCube z ((k + 2 : ℕ) : ℤ) := by
      ext x
      constructor
      · rintro ⟨⟨_, hw⟩, hq⟩; exact ⟨⟨hq, hw⟩, hq⟩
      · rintro ⟨⟨hq, hw⟩, _⟩; exact ⟨⟨lip_bdry_approx_cube_mono z hk3 hq, hw⟩, hq⟩
    have hz' := lip_localized_restrict (hDo (k + 2)) (lip_bdry_approx_isOpen_cube z (k + 2))
      (hDmono (k + 2) mt hk3) (lip_bdry_approx_cube_mono z hk3) hagree hz
    obtain ⟨p', hp'⟩ := hstep2 a W V rW M₂W DW nu (s k) (δ k) E ((3 : ℝ)⁻¹ ^ (mt - k)) lam Lam z x₀ k
      hnu (hs1 k hk0 hkm) (hδ0 k hk0 hkm) ((hδc k hk0 hkm).trans (hcle.trans (by norm_num))) hE hθ0
      hθ1 (lip_det_nat12 hn₁ hk1) (hP1 k hk0 hkm) (hP2 k hk0 hkm) hW hrW' hMθ hzW hfr hx₀' hVo hBV hVk hell'
      hlam hblk' hc1 hc2 f g F G1 G2 (u.restrict (hDo (k + 2)) (hDmono (k + 2) mt hk3)) hg hF0 hG1
      hG2 (fun x hx => hDg x (lip_bdry_approx_cube_mono z hk3 hx))
      (fun x hx => hD2g x (lip_bdry_approx_cube_mono z hk3 hx))
      (ae_restrict_of_ae_restrict_of_subset (hDmono (k + 2) mt hk3) hFae) hsol' hz' p
    refine ⟨p', ?_⟩
    rw [hΦ, hΦ]
    have hΦ0' : 0 ≤ lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p := by
      rw [← hΦ]; exact hΦ0 _ _
    have hδk := hδ0 k hk0 hkm
    have hcoef : C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) + C₂ * δ k ≤ 1 / 2 := by
      have := hC₂δ k hk0 hkm
      linarith only [hr1', this]
    have hmax : max (δ k) 0 = δ k := max_eq_left hδk
    have hp'' := hp'
    have hfin := mul_le_mul_of_nonneg_right hcoef hΦ0'
    have hmx : (s k)⁻¹ * (3 : ℝ) ^ k * F ≤ max ((s k)⁻¹ * (3 : ℝ) ^ k * F) 0 := le_max_left _ _
    rw [hmax]
    have hCm := mul_le_mul_of_nonneg_left hmx hC₂0.le
    have hp3 : lipPin (shiftCube z (((k - k₀ : ℕ)) : ℤ) ∩ W) (k - k₀) x₀ (g x₀) u.toFun p' ≤
        (C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) + C₂ * δ k) *
            lipPin (shiftCube z ((k + 1 : ℕ) : ℤ) ∩ W) (k + 1) x₀ (g x₀) u.toFun p +
          (C₂ * δ k + C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) * ((3 : ℝ)⁻¹) ^ (mt - k)) * ‖p‖ +
            C₂ * (G1 + (s k)⁻¹ * (3 : ℝ) ^ k * F + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) := hp''
    nlinarith only [hp3, hfin, hCm]
  clear hstep2 hstep hL2 hP1 hP2 hfr hMW hrW hslope hrestr hinner
  -- the errors
  have hnM : n₁ ≤ mt - 1 ∨ n₁ = mt := lip_det_nat3 hn₁mt
  have hS : ∀ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1), n₁ ≤ k ∧ k + 2 ≤ mt := fun k hk => by
    exact lip_det_nat4 hn₁ (Finset.mem_Icc.1 hk)
  have hSr : Finset.Icc (n₁ + k₀) (mt - 1 - 1) ⊆ Finset.range mt := fun k hk => by
    exact Finset.mem_range.2 (lip_det_nat5 (hS k hk).2)
  have hgeom := lip_int_det_geom mt _ hSr
  have hthe : ∑ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1), ((3 : ℝ)⁻¹) ^ (mt - k) ≤ 1 := by
    have e : ∀ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1),
        ((3 : ℝ)⁻¹) ^ (mt - k) = ((3 : ℝ)⁻¹) ^ mt * (3 : ℝ) ^ k := by
      intro k hk
      have hk' := hS k hk
      have h1 : ((3 : ℝ)⁻¹) ^ mt = ((3 : ℝ)⁻¹) ^ (mt - k) * ((3 : ℝ)⁻¹) ^ k := by
        rw [← pow_add]; congr 1; exact (Nat.sub_add_cancel (lip_det_nat5 hk'.2).le).symm
      have h2 : ((3 : ℝ)⁻¹) ^ k * (3 : ℝ) ^ k = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
      calc ((3 : ℝ)⁻¹) ^ (mt - k) = ((3 : ℝ)⁻¹) ^ (mt - k) * (((3 : ℝ)⁻¹) ^ k * (3 : ℝ) ^ k) := by
            rw [h2, mul_one]
        _ = (((3 : ℝ)⁻¹) ^ (mt - k) * ((3 : ℝ)⁻¹) ^ k) * (3 : ℝ) ^ k := by ring
        _ = _ := by rw [← h1]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have h3 : ((3 : ℝ)⁻¹) ^ mt * (3 : ℝ) ^ mt = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
    calc ((3 : ℝ)⁻¹) ^ mt * ∑ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1), (3 : ℝ) ^ k
        ≤ ((3 : ℝ)⁻¹) ^ mt * (3 : ℝ) ^ mt :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 1 := h3
  have hδsum : ∑ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1), max (δ k) 0 ≤ 1 / (16 * C₂ * (Cs + 1)) := by
    have e : ∀ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1), max (δ k) 0 = δ k := fun k hk =>
      max_eq_left (hδ0 k (hS k hk).1 ((Nat.le_add_right k 2).trans (hS k hk).2))
    rw [Finset.sum_congr rfl e]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i hi _ => ?_)) hsum
    · intro k hk
      have := hS k hk
      exact Finset.mem_Icc.2 ⟨this.1, (Nat.le_add_right k 2).trans this.2⟩
    · rw [Finset.mem_Icc] at hi
      exact hδ0 i hi.1 hi.2
  have hsmall : (∑ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1),
      (C₂ * max (δ k) 0 + C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) * ((3 : ℝ)⁻¹) ^ (mt - k))) *
        (8 * (Cs + 1)) ≤ 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have e1 : C₂ * (1 / (16 * C₂ * (Cs + 1))) * (8 * (Cs + 1)) = 1 / 2 := by field_simp; ring
    have e2 : 1 / (24 * (Cs + 1)) * (8 * (Cs + 1)) = 1 / 3 := by field_simp; ring
    have h1 := mul_le_mul_of_nonneg_left hδsum hC₂0.le
    have h2 := mul_le_mul_of_nonneg_left hthe (by positivity : 0 ≤ C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁))
    have h3 : (C₂ * ∑ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1), max (δ k) 0 +
        C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) * ∑ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1),
          ((3 : ℝ)⁻¹) ^ (mt - k)) ≤ C₂ * (1 / (16 * C₂ * (Cs + 1))) + 1 / (24 * (Cs + 1)) := by
      linarith only [h1, h2, hr1, mul_one (C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁))]
    have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ 8 * (Cs + 1))
    simp only [add_mul] at h4
    rw [e1, e2] at h4
    linarith only [h4]
  -- the sum of the data terms
  obtain ⟨Pg, hPg⟩ : ∃ x : ℝ, x = ((mt : ℝ) - (n₁ : ℝ) + 1) * G1 := ⟨_, rfl⟩
  obtain ⟨Fm, hFm⟩ : ∃ x : ℝ, x = (s mt)⁻¹ * (3 : ℝ) ^ mt * F := ⟨_, rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ x : ℝ, x = (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 := ⟨_, rfl⟩
  have hn₁0 : (0 : ℝ) < n₁ := by exact_mod_cast lip_det_nat6 hn₁
  have hPg0 : 0 ≤ Pg := by
    rw [hPg]
    have : (n₁ : ℝ) ≤ mt := by exact_mod_cast hn₁mt
    exact mul_nonneg (by linarith only [this]) hG1
  have hFm0 : 0 ≤ Fm := by
    rw [hFm]
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 (hs0 mt hn₁mt le_rfl).le)
      (pow_nonneg (by norm_num) _)) hF0
  have hGm0 : 0 ≤ Gm := by
    rw [hGm]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (pow_nonneg (by norm_num) _)) hG2
  have hsumA : ∑ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1),
      C₂ * (G1 + max ((s k)⁻¹ * (3 : ℝ) ^ k * F) 0 + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) ≤
        2 * C₂ * (Pg + Fm + Gm) := by
    have hterm : ∀ k ∈ Finset.Icc (n₁ + k₀) (mt - 1 - 1),
        C₂ * (G1 + max ((s k)⁻¹ * (3 : ℝ) ^ k * F) 0 + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2) ≤
          C₂ * G1 + (2 * C₂ * ((s mt)⁻¹ * F)) * (3 : ℝ) ^ k +
            (C₂ * ((n₁ : ℝ) ^ (-E) * G2)) * (3 : ℝ) ^ k := by
      intro k hk
      have hk' := hS k hk
      have hkm : k ≤ mt := (Nat.le_add_right k 2).trans hk'.2
      have hsk0 := hs0 k hk'.1 hkm
      have hmt0 := hs0 mt hn₁mt le_rfl
      have hinv : (s k)⁻¹ ≤ 2 * (s mt)⁻¹ := lip_inv_le hmt0 (hsm k hk'.1 hkm)
      have hpos : 0 ≤ (3 : ℝ) ^ k * F := mul_nonneg (pow_nonneg (by norm_num) k) hF0
      have h1 : max ((s k)⁻¹ * (3 : ℝ) ^ k * F) 0 ≤ 2 * (s mt)⁻¹ * F * (3 : ℝ) ^ k := by
        rw [max_eq_left (mul_nonneg (mul_nonneg (inv_nonneg.2 hsk0.le) (pow_nonneg (by norm_num) k)) hF0)]
        calc (s k)⁻¹ * (3 : ℝ) ^ k * F = (s k)⁻¹ * ((3 : ℝ) ^ k * F) := by ring
          _ ≤ (2 * (s mt)⁻¹) * ((3 : ℝ) ^ k * F) := mul_le_mul_of_nonneg_right hinv hpos
          _ = _ := by ring
      have hk0 : (0 : ℝ) < n₁ := hn₁0
      have h2 : (k : ℝ) ^ (-E) ≤ (n₁ : ℝ) ^ (-E) :=
        Real.rpow_le_rpow_of_nonpos hk0 (by exact_mod_cast hk'.1) (by linarith only [hE])
      have h3 : (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2 ≤ (n₁ : ℝ) ^ (-E) * G2 * (3 : ℝ) ^ k := by
        calc (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2 = ((k : ℝ) ^ (-E) * G2) * (3 : ℝ) ^ k := by ring
          _ ≤ ((n₁ : ℝ) ^ (-E) * G2) * (3 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hG2)
                (pow_nonneg (by norm_num) k)
      have h4 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (le_refl G1) h1) h3) hC₂0.le
      calc _ ≤ _ := h4
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
      ← Finset.mul_sum, nsmul_eq_mul]
    have hcard : ((Finset.Icc (n₁ + k₀) (mt - 1 - 1)).card : ℝ) ≤ (mt : ℝ) - n₁ + 1 := by
      rw [Nat.card_Icc]
      have : (mt - 1 - 1 + 1 - (n₁ + k₀) : ℕ) + n₁ ≤ mt + 1 := lip_det_nat7 hn₁mt
      have h2 : ((mt - 1 - 1 + 1 - (n₁ + k₀) : ℕ) : ℝ) + n₁ ≤ mt + 1 := by exact_mod_cast this
      linarith only [h2]
    have e1 := mul_le_mul_of_nonneg_right hcard (mul_nonneg hC₂0.le hG1)
    have hCn : 0 ≤ C₂ * ((n₁ : ℝ) ^ (-E) * G2) :=
      mul_nonneg hC₂0.le (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hG2)
    have e2 := mul_le_mul_of_nonneg_left hgeom (mul_nonneg (mul_nonneg zero_le_two hC₂0.le)
      (mul_nonneg (inv_nonneg.2 (hs0 mt hn₁mt le_rfl).le) hF0))
    have e3 := mul_le_mul_of_nonneg_left hgeom hCn
    have hCP : 0 ≤ C₂ * ((mt - n₁ + 1 : ℝ) * G1) := by
      have := hPg0; rw [hPg] at this; exact mul_nonneg hC₂0.le this
    have hCG : 0 ≤ C₂ * ((n₁ : ℝ) ^ (-E) * G2) * (3 : ℝ) ^ mt :=
      mul_nonneg hCn (pow_nonneg (by norm_num) _)
    rw [hPg, hFm, hGm]
    linarith only [e1, e2, e3, hCP, hCG]
  clear hthe hδsum hSr hS hgeom hδc hC₂δ hcle hr1 hr1'
  have hBrnn : 0 ≤ Φ mt 0 + Pg + Fm + Gm := by linarith only [hΦ0 mt 0, hPg0, hFm0, hGm0]
  have hosc_all : ∀ j, n₁ ≤ j → j ≤ mt → Φ j 0 ≤ K * (Φ mt 0 + Pg + Fm + Gm) := by
    intro j hj1 hj2
    by_cases hjm : j = mt
    · subst hjm
      calc Φ j 0 ≤ Φ j 0 + Pg + Fm + Gm := by linarith only [hPg0, hFm0, hGm0]
        _ ≤ K * (Φ j 0 + Pg + Fm + Gm) := le_mul_of_one_le_left hBrnn hK1
    · have hjM : j ≤ mt - 1 := lip_det_nat8 hj2 hjm
      have hnM' : n₁ ≤ mt - 1 := hj1.trans hjM
      have hit' := hit (P := Vec d) (fun p => ‖p‖) n₁ (mt - 1) Φ (fun j => Φ j 0)
        (fun k => C₂ * (G1 + max ((s k)⁻¹ * (3 : ℝ) ^ k * F) 0 + (k : ℝ) ^ (-E) * (3 : ℝ) ^ k * G2))
        (fun k => C₂ * max (δ k) 0 + C₁ * ((Real.sqrt 3)⁻¹) ^ (k₀ - a₁) * ((3 : ℝ)⁻¹) ^ (mt - k))
        0 hnM' hΦ0 (fun p => norm_nonneg p)
        (fun k => lip_det_a_nonneg hC₂0.le hG1 hG2) (fun k => lip_det_b_nonneg hC₁0.le hC₂0.le) hone
        (fun j hj1 hj2 p q => hslope' j hj1 (hj2.trans (Nat.sub_le mt 1)) p q)
        (fun j hj1 hj2 p => hrestr' j hj1 (hj2.trans (Nat.sub_le mt 1)) p)
        (fun j hj1 hj2 p => hosc' j hj1 (hj2.trans (Nat.sub_le mt 1)) p) hsmall j hj1 hjM
      have htop := hrestr' (mt - 1) hnM' (Nat.sub_add_cancel (lip_det_nat10 hn₁ hn₁mt)).le 0
      rw [Nat.sub_add_cancel (lip_det_nat10 hn₁ hn₁mt)] at htop
      have h0 : ‖(0 : Vec d)‖ = 0 := norm_zero
      simp only [h0, add_zero] at hit'
      have hR : 0 ≤ Pg + Fm + Gm := by linarith only [hPg0, hFm0, hGm0]
      have h1 : Φ j 0 ≤ Cit * (Cr * Φ mt 0 + 2 * C₂ * (Pg + Fm + Gm)) := by
        refine hit'.trans (mul_le_mul_of_nonneg_left ?_ (by linarith only [hCit]))
        linarith only [htop, hsumA]
      have hp0 := hΦ0 mt 0
      have h2 : Cr * Φ mt 0 + 2 * C₂ * (Pg + Fm + Gm) ≤
          (Cr + 2 * C₂) * (Φ mt 0 + Pg + Fm + Gm) := by
        nlinarith only [mul_nonneg hC₂0.le hp0, mul_nonneg (by linarith only [hCr1] : 0 ≤ Cr) hR]
      calc Φ j 0 ≤ Cit * (Cr * Φ mt 0 + 2 * C₂ * (Pg + Fm + Gm)) := h1
        _ ≤ Cit * ((Cr + 2 * C₂) * (Φ mt 0 + Pg + Fm + Gm)) :=
            mul_le_mul_of_nonneg_left h2 (by linarith only [hCit])
        _ = K * (Φ mt 0 + Pg + Fm + Gm) := by rw [hK]; ring
  have hCfin : K ≤ 2 * Cin * (K + 3) := by nlinarith only [hCin, hK1]
  have hBr : Φ mt 0 + Pg + Fm + Gm = lipPin (shiftCube z (mt : ℤ) ∩ W) mt x₀ (g x₀) u.toFun 0 +
      ((mt : ℝ) - (n₁ : ℝ) + 1) * G1 + (s mt)⁻¹ * (3 : ℝ) ^ mt * F +
        (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 := by
    rw [hΦ, hPg, hFm, hGm]
  rw [← hBr]
  clear hone hslope' hrestr' hosc' hit hsmall hsumA
  intro j hj1 hj2
  refine ⟨?_, fun hjr => ?_⟩
  · rw [← hΦ]
    exact (hosc_all j hj1 hj2).trans (mul_le_mul_of_nonneg_right hCfin hBrnn)
  · have hcc2 : LipCaccBdryS a nu (s mt) (2 * Cin) E W z (j + 1) :=
      (hcacc (j + 1) (hj1.trans (Nat.le_succ j)) hjr).monoC (hs0 (j + 1) (hj1.trans (Nat.le_succ j)) hjr)
        (hsk (j + 1) (hj1.trans (Nat.le_succ j)) hjr) (hsm (j + 1) (hj1.trans (Nat.le_succ j)) hjr) (by linarith only [hCin]) le_rfl
    have hgr := lip_bdry_det_grad (a := a) (nu := nu) (s := s mt) (Cin := 2 * Cin) (E := E)
      (lam := lam) (Lam := Lam) (W := W) (z := z) (x₀ := x₀) (k := j) (m := mt) hjr hnu hsmt
      (by linarith only [hCin]) hE (lip_det_nat11 hn₁ hj1) hW.1 (hx₀j j hj1) hell hcc2 (hvol j hj2) f g F G1 G2
      u hg hF0 hG1 hG2 hDg hD2g hFae hsol hz 0
    refine hgr.trans ?_
    have hmt0 := hs0 mt hn₁mt le_rfl
    have hj3 : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ mt := pow_le_pow_right₀ (by norm_num) (Nat.le_of_succ_le hjr)
    have hΦj : lipPin (shiftCube z ((j + 1 : ℕ) : ℤ) ∩ W) (j + 1) x₀ (g x₀) u.toFun 0 ≤
        K * (Φ mt 0 + Pg + Fm + Gm) := by
      rw [← hΦ]; exact hosc_all (j + 1) (hj1.trans (Nat.le_succ j)) hjr
    have e1 : G1 ≤ Pg := by
      rw [hPg]
      have : (1 : ℝ) ≤ (mt : ℝ) - n₁ + 1 := by
        have : (n₁ : ℝ) ≤ mt := by exact_mod_cast hn₁mt
        linarith only [this]
      calc G1 = 1 * G1 := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right this hG1
    have e2 : (s mt)⁻¹ * (3 : ℝ) ^ j * F ≤ Fm := by
      rw [hFm]
      have h0 : 0 ≤ (s mt)⁻¹ * F := mul_nonneg (inv_nonneg.2 hmt0.le) hF0
      calc (s mt)⁻¹ * (3 : ℝ) ^ j * F = ((s mt)⁻¹ * F) * (3 : ℝ) ^ j := by ring
        _ ≤ ((s mt)⁻¹ * F) * (3 : ℝ) ^ mt := mul_le_mul_of_nonneg_left hj3 h0
        _ = _ := by ring
    have e3 : (j : ℝ) ^ (-E) * (3 : ℝ) ^ j * G2 ≤ Gm := by
      rw [hGm]
      have h2 : (j : ℝ) ^ (-E) ≤ (n₁ : ℝ) ^ (-E) :=
        Real.rpow_le_rpow_of_nonpos hn₁0 (by exact_mod_cast hj1) (by linarith only [hE])
      calc (j : ℝ) ^ (-E) * (3 : ℝ) ^ j * G2 ≤ (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 := by
            have h3 : (j : ℝ) ^ (-E) * (3 : ℝ) ^ j ≤ (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt :=
              mul_le_mul h2 hj3 (pow_nonneg (by norm_num) j)
                (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            exact mul_le_mul_of_nonneg_right h3 hG2
        _ = _ := rfl
    have hin : lipPin (shiftCube z ((j + 1 : ℕ) : ℤ) ∩ W) (j + 1) x₀ (g x₀) u.toFun 0 +
        (d : ℝ) * ‖(0 : Vec d)‖ + 2 * G1 + 3 * ((s mt)⁻¹ * (3 : ℝ) ^ j * F) +
          3 * ((j : ℝ) ^ (-E) * (3 : ℝ) ^ j * G2) ≤ (K + 3) * (Φ mt 0 + Pg + Fm + Gm) := by
      have h0 : ‖(0 : Vec d)‖ = 0 := norm_zero
      rw [h0, mul_zero, add_zero]
      nlinarith only [hΦj, e1, e2, e3, hPg0, hFm0, hGm0, hΦ0 mt 0]
    calc _ ≤ _ := mul_le_mul_of_nonneg_left hin (by linarith only [hCin] : (0 : ℝ) ≤ 2 * Cin)
      _ = _ := by ring

theorem lip_bdry_det_euclid_frontier [NeZero d] :
    ∃ x₀ : Vec d, x₀ ∈ frontier (Section6.euclidBall (d := d) 1) ∧ ‖x₀‖ ≤ 1 := by
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
  exact ⟨x₀, hx₀, hbd x₀ (frontier_subset_closure hx₀)⟩

/-- Witness: the numerical and geometric hypotheses of `lip_bdry_det` hold together on the unit
ball, with one scale and a frontier point. -/
example [NeZero d] (k₀ : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ (M₁ MU rU : ℝ) (W : Set (Vec d)) (rW M₂W DW nu E : ℝ) (s δ : ℕ → ℝ) (z x₀ : Vec d)
      (n₁ mt A : ℕ), 0 < rU ∧ 0 ≤ MU ∧ 0 < nu ∧ 0 ≤ E ∧ k₀ + 3 ≤ n₁ ∧ n₁ ≤ mt ∧
      (∀ k, n₁ ≤ k → k ≤ mt →
        1 ≤ s k ∧ s mt ≤ 2 * s k ∧ s k ≤ 2 * s mt ∧ 0 ≤ δ k ∧
          ((k : ℝ) ^ A)⁻¹ * Real.sqrt (s k) ≤ δ k * Real.sqrt nu ∧
          ((k : ℝ) ^ A)⁻¹ * s k ≤ 1) ∧
      ∑ k ∈ Finset.Icc n₁ mt, δ k ≤ c ∧
      IsUniformC11Domain W rW M₁ M₂W DW ∧ rU * (3 : ℝ) ^ mt ≤ rW ∧ M₂W * (3 : ℝ) ^ mt ≤ MU ∧
      z ∈ W ∧ x₀ ∈ frontier W ∧ ‖x₀ - z‖ ≤ (3 : ℝ) ^ n₁ / 2 := by
  obtain ⟨r, M₁, M₂, D, h⟩ := isUniformC11Domain_euclidBall (d := d)
  have hr : 0 < r := h.2.1
  obtain ⟨x₀, hx₀, hx₀n⟩ := lip_bdry_det_euclid_frontier (d := d)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max (k₀ + 3) (⌈1 / c⌉₊ + 1) := ⟨_, rfl⟩
  have hN1 : k₀ + 3 ≤ N := hN ▸ le_max_left _ _
  have hN2 : 1 / c ≤ (N : ℝ) := by
    have h1 : ⌈1 / c⌉₊ + 1 ≤ N := hN ▸ le_max_right _ _
    have h2 : (⌈1 / c⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast h1
    linarith only [h2, Nat.le_ceil (1 / c)]
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have h3 : (3 : ℝ) ≤ 3 ^ N := by
    calc (3 : ℝ) = 3 ^ 1 := (pow_one _).symm
      _ ≤ 3 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨M₁, |M₂| * 3 ^ N, r / 3 ^ N, Section6.euclidBall (d := d) 1, r, M₂, D, 1, 0,
    fun _ => 1, fun k => ((k : ℝ) ^ 1)⁻¹, 0, x₀, N, N, 1, by positivity, by positivity, one_pos,
    le_rfl, hN1, le_rfl, ?_, ?_, h, ?_, ?_, Section6.zero_mem_euclidBall one_pos, hx₀, ?_⟩
  · intro k hk1 hk2
    have hk : k = N := le_antisymm hk2 hk1
    subst hk
    have hk1' : (1 : ℝ) ≤ k := hNpos
    refine ⟨le_rfl, by norm_num, by norm_num, by positivity, by simp, ?_⟩
    simpa using inv_le_one_of_one_le₀ hk1'
  · rw [Finset.Icc_self, Finset.sum_singleton, pow_one]
    rw [inv_le_comm₀ (by linarith only [hNpos]) hc]
    simpa using hN2
  · rw [div_mul_cancel₀ _ (by positivity)]
  · exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  · simp only [sub_zero]
    linarith only [hx₀n, h3]

end SuperdiffusionCLT.Section7
