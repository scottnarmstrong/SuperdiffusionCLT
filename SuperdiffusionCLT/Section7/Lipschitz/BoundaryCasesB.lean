/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryCases

/-!
# The boundary estimate at one centre, all cases

`lip_bdry_cases`: if the cube `z + □_mt` lies in the domain the interior estimate applies;
otherwise the nearest scale `n₀` at which the frontier is met splits the range: the boundary
engine above `n₀`, one boundary Caccioppoli step at `n₀ - 1`, the interior estimate below.  The
conclusion carries the gradient term, the oscillation about the average and, when the cube meets
the complement of the domain, the oscillation about the datum.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

private theorem lip_cases_nat_max {n n₀ n₁ mt : ℕ} (h : n₁ = max n₀ n) (h1 : n₀ ≤ mt)
    (h2 : n < mt) : n ≤ n₁ ∧ n₀ ≤ n₁ ∧ n₁ ≤ mt := by omega

private theorem lip_cases_nat_le {n n₀ n₁ : ℕ} (h : n₁ = max n₀ n) (h1 : n₀ ≤ n) : n₁ ≤ n := by
  omega

private theorem lip_cases_nat_eq {n n₀ n₁ : ℕ} (h : n₁ = max n₀ n) (h1 : n < n₀) : n₁ = n₀ := by
  omega

private theorem lip_cases_nat_pred {n n₀ n₁ mt : ℕ} (h : n + 1 < n₀) (hn1 : n₁ = n₀)
    (hmt : n₀ ≤ mt) : ∃ k : ℕ, n₀ = k + 1 ∧ n ≤ k ∧ n < k ∧ k ≤ mt ∧ k < n₀ ∧ n₁ ≤ k + 1 ∧
      k + 1 ≤ mt :=
  ⟨n₀ - 1, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem lip_cases_nat_succ {n n₀ : ℕ} (h : n₀ ≤ n + 1) (h1 : n < n₀) : n₀ = n + 1 := by
  omega

private theorem lip_cases_nat_one {k₀ n : ℕ} (h : k₀ + 3 ≤ n) : 1 ≤ n := by omega

private theorem lip_cases_b2a {gr os Pn Cd TT C : ℝ} (hgr : gr ≤ 3 * Cd * TT) (hox : os ≤ 2 * Pn)
    (hΦ : Pn ≤ 3 * Cd * TT) (hK : 9 * Cd ≤ C) (hTT : 0 ≤ TT) : gr + os ≤ C * TT := by
  have h1 : gr + os ≤ 9 * Cd * TT := by linarith only [hgr, hox, hΦ]
  exact h1.trans (mul_le_mul_of_nonneg_right hK hTT)

private theorem lip_cases_b2b {dat Pn G1 Cd TT C : ℝ} (h1 : dat ≤ Pn + G1) (hΦ : Pn ≤ 3 * Cd * TT)
    (hG1 : G1 ≤ TT) (hK : 3 * Cd + 1 ≤ C) (hTT : 0 ≤ TT) : dat ≤ C * TT := by
  calc dat ≤ 3 * Cd * TT + TT := by linarith only [h1, hΦ, hG1]
    _ = (3 * Cd + 1) * TT := by ring
    _ ≤ C * TT := mul_le_mul_of_nonneg_right hK hTT

private theorem lip_cases_osc_step {p0 p1 Lk Lk1 Lav q Cd TT : ℝ} (hp : p0 = 3 * p1) (hp0 : 0 ≤ p0)
    (hq : 1 ≤ q) (hox : p0 * Lav ≤ 2 * (p0 * Lk)) (hmk : Lk ≤ q * Lk1)
    (hΦ : p1 * Lk1 ≤ 3 * Cd * TT) : p0 * Lav ≤ 6 * q * (3 * Cd) * TT := by
  have h1 : p0 * Lk ≤ 3 * q * (p1 * Lk1) :=
    calc p0 * Lk ≤ p0 * (q * Lk1) := mul_le_mul_of_nonneg_left hmk hp0
      _ = 3 * q * (p1 * Lk1) := by rw [hp]; ring
  have h2 : 3 * q * (p1 * Lk1) ≤ 3 * q * (3 * Cd * TT) :=
    mul_le_mul_of_nonneg_left hΦ (by linarith only [hq])
  linarith only [hox, h1, h2]

private theorem lip_cases_Fk {x y P Q F TT : ℝ} (hs2 : x ≤ 2 * y) (hy : 0 ≤ y) (hP : 0 ≤ P)
    (hPQ : P ≤ Q) (hF : 0 ≤ F) (hFT : y * Q * F ≤ TT) : x * P * F ≤ 2 * TT :=
  calc x * P * F = x * (P * F) := by ring
    _ ≤ (2 * y) * (Q * F) :=
        mul_le_mul hs2 (mul_le_mul_of_nonneg_right hPQ hF) (mul_nonneg hP hF)
          (mul_nonneg zero_le_two hy)
    _ = 2 * (y * Q * F) := by ring
    _ ≤ 2 * TT := by linarith only [hFT]

private theorem lip_cases_scale_mono {a P Q F : ℝ} (hPQ : P ≤ Q) (ha : 0 ≤ a) (hF : 0 ≤ F) :
    a * P * F ≤ a * Q * F :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPQ ha) hF

private theorem lip_cases_gr_mono {a b c G : ℝ} (hs1 : a ≤ 2 * b) (hcG : 0 ≤ c * G) :
    a * c * G ≤ 2 * (b * c * G) :=
  calc a * c * G = a * (c * G) := by ring
    _ ≤ (2 * b) * (c * G) := mul_le_mul_of_nonneg_right hs1 hcG
    _ = 2 * (b * c * G) := by ring

private theorem lip_cases_b3 {grm grk on ok Fk Cin Cd q TT C : ℝ} (hgs : grm ≤ 2 * grk)
    (hon : 0 ≤ on) (hint : grk + on ≤ Cin * (ok + Fk))
    (hosc : ok ≤ 6 * q * (3 * Cd) * TT) (hFk : Fk ≤ 2 * TT) (hCin : 0 ≤ Cin)
    (hK : 2 * Cin * (6 * q * (3 * Cd) + 2) ≤ C) (hTT : 0 ≤ TT) : grm + on ≤ C * TT := by
  have h1 : grm + on ≤ 2 * (grk + on) := by linarith only [hgs, hon]
  have h2 : Cin * (ok + Fk) ≤ Cin * (6 * q * (3 * Cd) * TT + 2 * TT) :=
    mul_le_mul_of_nonneg_left (by linarith only [hosc, hFk]) hCin
  calc grm + on ≤ 2 * (Cin * (6 * q * (3 * Cd) * TT + 2 * TT)) := by
        linarith only [h1, hint, h2]
    _ = (2 * Cin * (6 * q * (3 * Cd) + 2)) * TT := by ring
    _ ≤ C * TT := mul_le_mul_of_nonneg_right hK hTT

private theorem lip_cases_b4 {grm on pin G1 a b Cin Cd q TT C dd : ℝ} (hgr : grm ≤ 2 * Cin * (pin +
      dd + 2 * G1 + 3 * a + 3 * b)) (hdd : dd = 0) (hpin : pin ≤ 3 * Cd * TT + 2 * G1)
    (hG1 : G1 ≤ TT) (ha : a ≤ TT) (hb : b ≤ TT) (hosc : on ≤ 6 * q * (3 * Cd) * TT)
    (hCin : 0 ≤ Cin) (hK : 2 * Cin * (3 * Cd + 10) + 6 * q * (3 * Cd) ≤ C) (hTT : 0 ≤ TT) :
    grm + on ≤ C * TT := by
  have hin : pin + dd + 2 * G1 + 3 * a + 3 * b ≤ (3 * Cd + 10) * TT := by
    calc pin + dd + 2 * G1 + 3 * a + 3 * b ≤ 3 * Cd * TT + 10 * TT := by
          linarith only [hdd, hpin, hG1, ha, hb, hTT]
      _ = (3 * Cd + 10) * TT := by ring
  have h2 : 2 * Cin * (pin + dd + 2 * G1 + 3 * a + 3 * b) ≤ 2 * Cin * ((3 * Cd + 10) * TT) :=
    mul_le_mul_of_nonneg_left hin (by linarith only [hCin])
  calc grm + on ≤ 2 * Cin * ((3 * Cd + 10) * TT) + 6 * q * (3 * Cd) * TT := by
        linarith only [hgr, h2, hosc]
    _ = (2 * Cin * (3 * Cd + 10) + 6 * q * (3 * Cd)) * TT := by ring
    _ ≤ C * TT := mul_le_mul_of_nonneg_right hK hTT

private theorem lip_cases_mul3 {x Y TT Cd : ℝ} (h : x ≤ Cd * Y) (hY : Y ≤ 3 * TT)
    (hCd : 0 ≤ Cd) : x ≤ 3 * Cd * TT :=
  h.trans (calc Cd * Y ≤ Cd * (3 * TT) := mul_le_mul_of_nonneg_left hY hCd
    _ = 3 * Cd * TT := by ring)

private theorem lip_cases_mul_two {p A B : ℝ} (h : A ≤ 2 * B) (hp : 0 ≤ p) :
    p * A ≤ 2 * (p * B) :=
  calc p * A ≤ p * (2 * B) := mul_le_mul_of_nonneg_left h hp
    _ = 2 * (p * B) := by ring

private theorem lip_cases_h4 {m n n1 G1 : ℝ} (hc : n ≤ n1) (hmn : 1 ≤ m - n) (hG : 0 ≤ G1) :
    (m - n1 + 1) * G1 ≤ 2 * ((m - n) * G1) :=
  calc (m - n1 + 1) * G1 ≤ (2 * (m - n)) * G1 :=
        mul_le_mul_of_nonneg_right (by linarith only [hc, hmn]) hG
    _ = 2 * ((m - n) * G1) := by ring

private theorem lip_cases_Yb {pin P Lg Lavg G1 X Y sF W Ga TT : ℝ} (h1 : pin ≤ P * Lg + G1)
    (h3 : X ≤ Ga) (h4 : Y ≤ 2 * W) (hT : TT = P * Lavg + P * Lg + sF + W + Ga)
    (hPavg : 0 ≤ P * Lavg) (hPg : 0 ≤ P * Lg) (ha2 : 0 ≤ sF) (ha3 : G1 ≤ W) (ha4 : 0 ≤ Ga) :
    pin + Y + sF + X ≤ 3 * TT := by
  linarith only [h1, h3, h4, hT, hPavg, hPg, ha2, ha3, ha4]

/-- **The boundary estimate at one centre, all cases**: the
cube is interior, or the frontier is first met at a top scale, or the boundary iteration runs
down to `n ∨ n₀` and the interior estimate takes over below `n₀ - 1`. -/
theorem lip_bdry_cases (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cin M₁ MU rU : ℝ) (hCin : 1 ≤ Cin)
    (hrU : 0 < rU) (hMU : 0 ≤ MU) (ag A : ℕ) :
    ∃ (C c : ℝ) (N₀ : ℕ), 1 ≤ C ∧ 0 < c ∧
      ∀ (a : CoeffField d) (W : Set (Vec d)) (rW M₂W DW nu E lam Lam : ℝ) (s δ : ℕ → ℝ)
        (z : Vec d) (n mt : ℕ),
        0 < nu → 0 ≤ E → N₀ ≤ n → n < mt →
        (∀ k, n ≤ k → k ≤ mt →
          1 ≤ s k ∧ s mt ≤ 2 * s k ∧ s k ≤ 2 * s mt ∧ 0 ≤ δ k ∧
            ((k : ℝ) ^ A)⁻¹ * Real.sqrt (s k) ≤ δ k * Real.sqrt nu ∧
            ((k : ℝ) ^ A)⁻¹ * s k ≤ 1) →
        ∑ k ∈ Finset.Icc n mt, δ k ≤ c →
        IsUniformC11Domain W rW M₁ M₂W DW → rU * (3 : ℝ) ^ mt ≤ rW →
        M₂W * (3 : ℝ) ^ mt ≤ MU → z ∈ W →
        IsEllipticFieldOn lam Lam (shiftCube z (mt : ℤ) ∩ W) a → 0 < lam →
        (∀ k, n ≤ k → k ≤ mt → LipCaccBdryS a nu (s k) Cin E W z k) →
        (∀ k, n ≤ k → k ≤ mt → ∃ V : Set (Vec d), IsOpen V ∧
          Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V ∧
          V ⊆ Metric.ball z ((3 : ℝ) ^ k / 2) ∩ W ∧ LipL2Block a nu (s k) (δ k) Cin A k V) →
        (∀ l k, n ≤ l → l < k → k ≤ mt → shiftCube z (k : ℤ) ⊆ W →
          LipIntAt a nu (s k) Cin z l k) →
        ∀ (f g : Vec d → ℝ) (F G1 G2 : ℝ) (u : H1Function (shiftCube z (mt : ℤ) ∩ W)),
          ContDiff ℝ 2 g → 0 ≤ F → 0 ≤ G1 → 0 ≤ G2 →
          (∀ x ∈ shiftCube z (mt : ℤ), ‖fderiv ℝ g x‖ ≤ G1) →
          (∀ x ∈ shiftCube z (mt : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) →
          (∀ᵐ x ∂volume.restrict (shiftCube z (mt : ℤ) ∩ W), |f x| ≤ F) →
          IsWeakSolutionOn a (shiftCube z (mt : ℤ) ∩ W) u f (fun _ => 0) →
          LocalizedZeroTraceFunctionOn (shiftCube z (mt : ℤ) ∩ W) (shiftCube z (mt : ℤ))
            (fun x => u.toFun x - g x) →
          AEStronglyMeasurable f (volume.restrict (shiftCube z (mt : ℤ) ∩ W)) →
          ∀ R : ℝ,
            R = C * (((3 : ℝ)⁻¹) ^ mt *
                (lipL2 (shiftCube z (mt : ℤ) ∩ W)
                    (fun x => u.toFun x - ⨍ w in shiftCube z (mt : ℤ) ∩ W, u.toFun w) +
                  lipL2 (shiftCube z (mt : ℤ) ∩ W) (fun x => u.toFun x - g x)) +
              (s mt)⁻¹ * (3 : ℝ) ^ mt * F + ((mt : ℝ) - (n : ℝ)) * G1 +
              (n : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2) →
          (Real.sqrt (s mt))⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (n : ℤ) ∩ W) u.grad +
              ((3 : ℝ)⁻¹) ^ n * lipL2 (shiftCube z (n : ℤ) ∩ W)
                (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ W, u.toFun w) ≤ R ∧
            (¬ shiftCube z (n : ℤ) ⊆ W →
              ((3 : ℝ)⁻¹) ^ n * lipL2 (shiftCube z (n : ℤ) ∩ W) (fun x => u.toFun x - g x) ≤ R) := by
  classical
  obtain ⟨Cd, c, k₀, hCd, hc, hdet⟩ := lip_bdry_det d hd Cin M₁ MU rU hCin hrU hMU ag A
  have hq1 : (1 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ d) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = Real.sqrt ((3 : ℝ) ^ d) := ⟨_, rfl⟩
  rw [← hqdef] at hq1
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 2 * Cin * (27 * Cd * q + 30) := ⟨_, rfl⟩
  have hCdq : 1 ≤ Cd * q := by nlinarith only [hCd, hq1]
  have hC1 : 1 ≤ C := by rw [hCdef]; nlinarith only [hCin, hCdq]
  have hCinC : Cin ≤ C := by rw [hCdef]; nlinarith only [hCin, hCdq]
  have hK1 : 9 * Cd ≤ C := by rw [hCdef]; nlinarith only [hCin, hCdq, hCd, hq1]
  have hK1' : 3 * Cd + 1 ≤ C := by rw [hCdef]; nlinarith only [hCin, hCdq, hCd, hq1]
  have hCd0 : (0 : ℝ) ≤ Cd := by linarith only [hCd]
  have hCin0 : (0 : ℝ) ≤ Cin := by linarith only [hCin]
  have hq0 : (0 : ℝ) ≤ q := by linarith only [hq1]
  have hh1 : 0 ≤ Cin * (Cd * q - Cd) := mul_nonneg hCin0 (by nlinarith only [hCd0, hq1])
  have hh2 : 0 ≤ Cd * q * (Cin - 1) := mul_nonneg (by linarith only [hCdq]) (by linarith only [hCin])
  have hK2 : 2 * Cin * (3 * Cd + 10) + 6 * q * (3 * Cd) ≤ C := by
    rw [hCdef]; nlinarith only [hh1, hh2, hCin, hCdq]
  have hK3 : 2 * Cin * (6 * q * (3 * Cd) + 2) ≤ C := by
    rw [hCdef]; nlinarith only [hCin, hh1, hh2, mul_nonneg hCin0 (by linarith only [hCdq] : (0 : ℝ) ≤ Cd * q)]
  refine ⟨C, c, k₀ + 3, hC1, hc, ?_⟩
  intro a W rW M₂W DW nu E lam Lam s δ z n mt hnu hE hN hnmt hs hsum hU hrU' hMU' hzW hell hlam
    hcacc hblk hint f g F G1 G2 u hg hF hG1 hG2 hDg hD2g hFae hsol hz hfm R hR
  have hWo : IsOpen W := hU.1
  have hsmt : 1 ≤ s mt := (hs mt hnmt.le le_rfl).1
  have hsmt0 : 0 < s mt := by linarith only [hsmt]
  have hball : ∀ j : ℕ, shiftCube z (j : ℤ) = Metric.ball z ((3 : ℝ) ^ j / 2) := fun j =>
    lip_bdry_approx_shiftCube_eq_ball z j
  have hDmono : ∀ j j' : ℕ, j ≤ j' → shiftCube z (j : ℤ) ∩ W ⊆ shiftCube z (j' : ℤ) ∩ W :=
    fun j j' h => Set.inter_subset_inter_left _ (lip_bdry_approx_cube_mono z h)
  have hDo : ∀ j : ℕ, IsOpen (shiftCube z (j : ℤ) ∩ W) := fun j =>
    (lip_bdry_approx_isOpen_cube z j).inter hWo
  have hDm : ∀ j : ℕ, MeasurableSet (shiftCube z (j : ℤ) ∩ W) := fun j => (hDo j).measurableSet
  have hzD : ∀ j : ℕ, z ∈ shiftCube z (j : ℤ) ∩ W := fun j =>
    ⟨by rw [hball]; exact Metric.mem_ball_self (half_pos (pow_pos (by norm_num) j)), hzW⟩
  have hDv0 : ∀ j : ℕ, volume (shiftCube z (j : ℤ) ∩ W) ≠ 0 := fun j =>
    ((hDo j).measure_pos volume ⟨z, hzD j⟩).ne'
  have hDvT : ∀ j : ℕ, volume (shiftCube z (j : ℤ) ∩ W) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z j) (measure_mono Set.inter_subset_left)
  have hmu : ∀ j : ℕ, j ≤ mt → MemLp u.toFun 2 (volume.restrict (shiftCube z (j : ℤ) ∩ W)) :=
    fun j hj => u.memL2.mono_measure (Measure.restrict_mono (hDmono j mt hj) le_rfl)
  have hfinD : ∀ j : ℕ, IsFiniteMeasure (volume.restrict (shiftCube z (j : ℤ) ∩ W)) := fun j =>
    ⟨by simpa using (hDvT j).lt_top⟩
  have h3pow : ∀ j j' : ℕ, j ≤ j' → (3 : ℝ) ^ j ≤ 3 ^ j' := fun j j' h =>
    pow_le_pow_right₀ (by norm_num) h
  -- the datum `g` is Lipschitz about the centre
  have hgc : ∀ y, ‖y - z‖ ≤ (3 : ℝ) ^ mt / 2 → |g y - g z| ≤ G1 * ‖y - z‖ :=
    lip_cases_g_close hg (half_pos (pow_pos (by norm_num) mt)) (fun x hx => hDg x (by rw [hball]; exact hx))
  have hgp : ∀ x y, ‖x - z‖ ≤ (3 : ℝ) ^ mt / 2 → ‖y - z‖ ≤ (3 : ℝ) ^ mt / 2 →
      |g x - g y| ≤ G1 * (‖x - z‖ + ‖y - z‖) := fun x y hx hy => by
    have h1 := hgc x hx
    have h2 := hgc y hy
    calc |g x - g y| = |(g x - g z) - (g y - g z)| := by ring_nf
      _ ≤ |g x - g z| + |g y - g z| := abs_sub _ _
      _ ≤ _ := by linarith only [h1, h2]
  have hgmem : MemLp g 2 (volume.restrict (shiftCube z (mt : ℤ) ∩ W)) := by
    have := hfinD mt
    refine MemLp.of_bound hg.continuous.aestronglyMeasurable (|g z| + G1 * ((3 : ℝ) ^ mt / 2))
      ((ae_restrict_iff' (hDm mt)).2 (Filter.Eventually.of_forall fun x hx => ?_))
    have hx' : ‖x - z‖ ≤ (3 : ℝ) ^ mt / 2 := by
      have := hx.1
      rw [hball, Metric.mem_ball, dist_eq_norm] at this
      exact this.le
    have h1 := hgc x hx'
    have h2 := mul_le_mul_of_nonneg_left hx' hG1
    rw [Real.norm_eq_abs]
    calc |g x| = |(g x - g z) + g z| := by ring_nf
      _ ≤ |g x - g z| + |g z| := abs_add_le _ _
      _ ≤ _ := by linarith only [h1, h2]
  -- the flatness about the datum and about its value at a point
  have hshA : ∀ j : ℕ, j ≤ mt → ∀ x₀ : Vec d, ‖x₀ - z‖ ≤ (3 : ℝ) ^ j / 2 →
      ((3 : ℝ)⁻¹) ^ j * lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x₀) ≤
          ((3 : ℝ)⁻¹) ^ j * lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x) + G1 ∧
        ((3 : ℝ)⁻¹) ^ j * lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x) ≤
          ((3 : ℝ)⁻¹) ^ j * lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x₀) + G1 := by
    intro j hj x₀ hx₀
    have hjm := h3pow j mt hj
    have hB0 : 0 ≤ G1 * (3 : ℝ) ^ j := mul_nonneg hG1 (pow_nonneg (by norm_num) j)
    have hb : ∀ x ∈ shiftCube z (j : ℤ) ∩ W, |g x - g x₀| ≤ G1 * (3 : ℝ) ^ j := by
      intro x hx
      have hx' : ‖x - z‖ ≤ (3 : ℝ) ^ j / 2 := by
        have := hx.1
        rw [hball, Metric.mem_ball, dist_eq_norm] at this
        exact this.le
      have := hgp x x₀ (by linarith only [hx', hjm]) (by linarith only [hx₀, hjm])
      have h2 : G1 * (‖x - z‖ + ‖x₀ - z‖) ≤ G1 * (3 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left (by linarith only [hx', hx₀]) hG1
      linarith only [this, h2]
    have hb' : ∀ x ∈ shiftCube z (j : ℤ) ∩ W, |g x₀ - g x| ≤ G1 * (3 : ℝ) ^ j := fun x hx => by
      rw [abs_sub_comm]; exact hb x hx
    have hgj : MemLp g 2 (volume.restrict (shiftCube z (j : ℤ) ∩ W)) :=
      hgmem.mono_measure (Measure.restrict_mono (hDmono j mt hj) le_rfl)
    have hfj := hfinD j
    have e : ((3 : ℝ)⁻¹) ^ j * (G1 * (3 : ℝ) ^ j) = G1 := by
      rw [inv_pow]; field_simp
    have h1 : lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x₀) ≤
        lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x) + G1 * (3 : ℝ) ^ j :=
      lip_cases_shift (hDm j) (hDv0 j) (hDvT j) (u := u.toFun) (h := g) (h' := fun _ => g x₀)
        hg.continuous continuous_const ((hmu j hj).sub hgj) hB0 hb
    have h2 : lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x) ≤
        lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x₀) + G1 * (3 : ℝ) ^ j :=
      lip_cases_shift (hDm j) (hDv0 j) (hDvT j) (u := u.toFun) (h := fun _ => g x₀) (h' := g)
        continuous_const hg.continuous ((hmu j hj).sub (memLp_const _)) hB0 hb'
    have hp : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ j := pow_nonneg (by norm_num) j
    constructor
    · calc _ ≤ ((3 : ℝ)⁻¹) ^ j * (lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x) +
            G1 * (3 : ℝ) ^ j) := mul_le_mul_of_nonneg_left h1 hp
        _ = _ := by rw [mul_add, e]
    · calc _ ≤ ((3 : ℝ)⁻¹) ^ j * (lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x₀) +
            G1 * (3 : ℝ) ^ j) := mul_le_mul_of_nonneg_left h2 hp
        _ = _ := by rw [mul_add, e]
  clear hgc hgp hgmem
  obtain ⟨Lavg, hLavg⟩ : ∃ L : ℝ, lipL2 (shiftCube z (mt : ℤ) ∩ W)
      (fun x => u.toFun x - ⨍ w in shiftCube z (mt : ℤ) ∩ W, u.toFun w) = L := ⟨_, rfl⟩
  obtain ⟨Lg, hLg⟩ : ∃ L : ℝ, lipL2 (shiftCube z (mt : ℤ) ∩ W) (fun x => u.toFun x - g x) = L :=
    ⟨_, rfl⟩
  rw [hLavg, hLg] at hR
  obtain ⟨TT, hTT⟩ : ∃ TT : ℝ, TT = ((3 : ℝ)⁻¹) ^ mt * Lavg + ((3 : ℝ)⁻¹) ^ mt * Lg +
      (s mt)⁻¹ * (3 : ℝ) ^ mt * F + ((mt : ℝ) - (n : ℝ)) * G1 +
        (n : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 := ⟨_, rfl⟩
  have hRT : R = C * TT := by rw [hR, hTT]; ring
  have hLavg0 : 0 ≤ Lavg := by rw [← hLavg]; exact ENNReal.toReal_nonneg
  have hLg0 : 0 ≤ Lg := by rw [← hLg]; exact ENNReal.toReal_nonneg
  have hp3 : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ mt := pow_nonneg (by norm_num) mt
  have hPavg : 0 ≤ ((3 : ℝ)⁻¹) ^ mt * Lavg := mul_nonneg hp3 hLavg0
  have hPg : 0 ≤ ((3 : ℝ)⁻¹) ^ mt * Lg := mul_nonneg hp3 hLg0
  have ha2 : 0 ≤ (s mt)⁻¹ * (3 : ℝ) ^ mt * F :=
    mul_nonneg (mul_nonneg (inv_nonneg.2 hsmt0.le) (pow_nonneg (by norm_num) mt)) hF
  have hmn : (1 : ℝ) ≤ (mt : ℝ) - (n : ℝ) := by
    have : n + 1 ≤ mt := hnmt
    have h2 : ((n + 1 : ℕ) : ℝ) ≤ (mt : ℝ) := by exact_mod_cast this
    push_cast at h2
    linarith only [h2]
  have ha3 : G1 ≤ ((mt : ℝ) - (n : ℝ)) * G1 := by nlinarith only [hmn, hG1]
  have ha3' : 0 ≤ ((mt : ℝ) - (n : ℝ)) * G1 := by linarith only [ha3, hG1]
  have ha4 : 0 ≤ (n : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 := by
    have : 0 ≤ (n : ℝ) ^ (-E) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    exact mul_nonneg (mul_nonneg this (pow_nonneg (by norm_num) mt)) hG2
  have hTT0 : 0 ≤ TT := by rw [hTT]; linarith only [hPavg, hPg, ha2, ha3', ha4]
  have hG1T : G1 ≤ TT := by rw [hTT]; linarith only [hPavg, hPg, ha2, ha3, ha4]
  have hFT : (s mt)⁻¹ * (3 : ℝ) ^ mt * F ≤ TT := by rw [hTT]; linarith only [hPavg, hPg, ha3', ha4]
  have hGT : (n : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 ≤ TT := by
    rw [hTT]; linarith only [hPavg, hPg, ha2, ha3']
  rw [hRT]
  by_cases hA : shiftCube z (mt : ℤ) ⊆ W
  · -- the cube lies in the domain: the interior estimate
    clear hdet hsum hU hrU' hMU' hblk hcacc hell hlam hz hfm
    have hint' := lip_cases_int (n := n) (k := mt) (m := mt) hnmt.le le_rfl hA
      (hint n mt le_rfl hnmt le_rfl hA) hF f u hsol hFae
    have key : ∀ v : Vec d → ℝ, lipL2 (shiftCube z (mt : ℤ)) (fun x => v x - ⨍ w in shiftCube z (mt : ℤ), v w) =
        lipL2 (shiftCube z (mt : ℤ) ∩ W) (fun x => v x - ⨍ w in shiftCube z (mt : ℤ) ∩ W, v w) :=
      fun v => by rw [Set.inter_eq_left.2 hA]
    rw [key u.toFun, hLavg] at hint'
    refine ⟨?_, fun hn => absurd ((lip_bdry_approx_cube_mono z hnmt.le).trans hA) hn⟩
    calc _ ≤ Cin * (((3 : ℝ)⁻¹) ^ mt * Lavg + (s mt)⁻¹ * (3 : ℝ) ^ mt * F) := by
          exact hint'
      _ ≤ Cin * TT := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hCin])
          rw [hTT]; linarith only [hPg, ha3', ha4]
      _ ≤ C * TT := mul_le_mul_of_nonneg_right hCinC hTT0
  · -- the frontier is met inside the top cube
    have hpos : ∀ m : ℕ, (0 : ℝ) < (3 : ℝ) ^ m / 2 := fun m => half_pos (pow_pos (by norm_num) m)
    have hex : ∃ m : ℕ, ∃ x ∈ frontier W, ‖x - z‖ ≤ (3 : ℝ) ^ m / 2 := by
      obtain ⟨x, hxf, hxd⟩ := lip_cases_frontier hWo hzW (hpos mt) (by rw [← hball mt]; exact hA)
      exact ⟨mt, x, hxf, hxd.le⟩
    obtain ⟨n₀, hn₀sp, hn₀mt, hn₀min⟩ : ∃ n₀ : ℕ, (∃ x ∈ frontier W, ‖x - z‖ ≤ (3 : ℝ) ^ n₀ / 2) ∧
        n₀ ≤ mt ∧ ∀ m : ℕ, m < n₀ → shiftCube z (m : ℤ) ⊆ W := by
      refine ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex ?_, fun m hm => ?_⟩
      · obtain ⟨x, hxf, hxd⟩ := lip_cases_frontier hWo hzW (hpos mt) (by rw [← hball mt]; exact hA)
        exact ⟨x, hxf, hxd.le⟩
      · by_contra hnot
        obtain ⟨y, hyf, hyd⟩ := lip_cases_frontier hWo hzW (hpos m) (by rw [← hball m]; exact hnot)
        exact Nat.find_min hex hm ⟨y, hyf, hyd.le⟩
    obtain ⟨x₀, hx₀f, hx₀d⟩ := hn₀sp
    obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, n₁ = max n₀ n := ⟨_, rfl⟩
    obtain ⟨hn₁a, hn₁b, hn₁mt⟩ := lip_cases_nat_max hn₁ hn₀mt hnmt
    have hx₀n₁ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ n₁ / 2 := by
      have := h3pow n₀ n₁ hn₁b
      linarith only [hx₀d, this]
    have hsum' : ∑ k ∈ Finset.Icc n₁ mt, δ k ≤ c := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hn₁a)
        (fun k hk _ => ?_)) hsum
      have hk := Finset.mem_Icc.1 hk
      exact (hs k hk.1 hk.2).2.2.2.1
    have hD := hdet a W rW M₂W DW nu E lam Lam s δ z x₀ n₁ mt hnu hE (hN.trans hn₁a) hn₁mt
      (fun k h1 h2 => hs k (hn₁a.trans h1) h2) hsum' hU hrU' hMU' hzW hx₀f hx₀n₁ hell hlam
      (fun k h1 h2 => hcacc k (hn₁a.trans h1) h2) (fun k h1 h2 => hblk k (hn₁a.trans h1) h2) f g F G1 G2 u hg
      hF hG1 hG2 hDg hD2g hFae hsol hz
    -- the bound of the engine by the target
    have hx₀mt : ‖x₀ - z‖ ≤ (3 : ℝ) ^ mt / 2 := hx₀n₁.trans (by
      have := h3pow n₁ mt hn₁mt
      linarith only [this])
    clear hdet hsum hsum' hU hrU' hMU' hblk hlam hx₀f hx₀n₁
    have hYb : lipPin (shiftCube z (mt : ℤ) ∩ W) mt x₀ (g x₀) u.toFun 0 +
        ((mt : ℝ) - (n₁ : ℝ) + 1) * G1 + (s mt)⁻¹ * (3 : ℝ) ^ mt * F +
          (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 ≤ 3 * TT := by
      have h1' : lipPin (shiftCube z (mt : ℤ) ∩ W) mt x₀ (g x₀) u.toFun 0 ≤
          ((3 : ℝ)⁻¹) ^ mt * Lg + G1 := by
        rw [lip_cases_pin0, ← hLg]; exact (hshA mt le_rfl x₀ hx₀mt).1
      have h2 : (n₁ : ℝ) ^ (-E) ≤ (n : ℝ) ^ (-E) :=
        Real.rpow_le_rpow_of_nonpos (by exact_mod_cast lip_cases_nat_one hN)
          (by exact_mod_cast hn₁a) (neg_nonpos.2 hE)
      have h3 : (n₁ : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 ≤ (n : ℝ) ^ (-E) * (3 : ℝ) ^ mt * G2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (pow_nonneg (by norm_num) mt)) hG2
      have h4 := lip_cases_h4 (m := (mt : ℝ)) (n := (n : ℝ)) (n1 := (n₁ : ℝ)) (G1 := G1) (by exact_mod_cast hn₁a) hmn hG1
      exact lip_cases_Yb h1' h3 h4 hTT hPavg hPg ha2 ha3 ha4
    have hΦ : ∀ j : ℕ, n₁ ≤ j → j ≤ mt →
        lipPin (shiftCube z (j : ℤ) ∩ W) j x₀ (g x₀) u.toFun 0 ≤ 3 * Cd * TT := fun j hj1 hj2 =>
      lip_cases_mul3 (hD j hj1 hj2).1 hYb hCd0
    have hGr : ∀ j : ℕ, n₁ ≤ j → j + 1 ≤ mt →
        (Real.sqrt (s mt))⁻¹ * Real.sqrt nu * lipGradL2 (shiftCube z (j : ℤ) ∩ W) u.grad ≤
          3 * Cd * TT := fun j hj1 hj2 =>
      lip_cases_mul3 ((hD j hj1 (Nat.le_of_succ_le hj2)).2 hj2) hYb hCd0
    -- the flatness about the average on a cube of the engine
    have hOsc : ∀ j : ℕ, j ≤ mt →
        ((3 : ℝ)⁻¹) ^ j * lipL2 (shiftCube z (j : ℤ) ∩ W)
            (fun x => u.toFun x - ⨍ w in shiftCube z (j : ℤ) ∩ W, u.toFun w) ≤
          2 * (((3 : ℝ)⁻¹) ^ j * lipL2 (shiftCube z (j : ℤ) ∩ W) (fun x => u.toFun x - g x₀)) := by
      intro j hj
      exact lip_cases_mul_two (lip_cases_avg_le (hDm j) (hDv0 j) (hDvT j) (hmu j hj) (g x₀))
        (pow_nonneg (by norm_num) j)
    have hmono : ∀ j : ℕ, j + 1 ≤ mt → shiftCube z (j : ℤ) ⊆ W → ∀ f' : Vec d → ℝ,
        MemLp f' 2 (volume.restrict (shiftCube z ((j + 1 : ℕ) : ℤ) ∩ W)) →
        lipL2 (shiftCube z (j : ℤ) ∩ W) f' ≤ q * lipL2 (shiftCube z ((j + 1 : ℕ) : ℤ) ∩ W) f' := by
      intro j hj hcj f' hf'
      rw [hqdef]
      refine lipL2_mono_set (pow_nonneg (by norm_num) d) (hDmono j (j + 1) (Nat.le_succ j)) (hDv0 j) (hDvT (j + 1))
        ?_ hf'
      calc volume (shiftCube z ((j + 1 : ℕ) : ℤ) ∩ W) ≤ volume (shiftCube z ((j + 1 : ℕ) : ℤ)) :=
            measure_mono Set.inter_subset_left
        _ = ENNReal.ofReal ((3 : ℝ) ^ d) * volume (shiftCube z (j : ℤ)) := lip_cases_vol_succ z j
        _ = ENNReal.ofReal ((3 : ℝ) ^ d) * volume (shiftCube z (j : ℤ) ∩ W) := by
            rw [Set.inter_eq_left.2 hcj]
    have hgrnn : ∀ j : ℕ, 0 ≤ (Real.sqrt (s mt))⁻¹ * Real.sqrt nu *
        lipGradL2 (shiftCube z (j : ℤ) ∩ W) u.grad := fun j =>
      mul_nonneg (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
        ENNReal.toReal_nonneg
    have hpow : ∀ j : ℕ, ((3 : ℝ)⁻¹) ^ j = 3 * ((3 : ℝ)⁻¹) ^ (j + 1) := fun j => by
      rw [pow_succ]; field_simp
    rcases le_or_gt n₀ n with hn0n | hnn0
    · -- the frontier is met at or above the scale `n`
      have hΦn := hΦ n (lip_cases_nat_le hn₁ hn0n) hnmt.le
      rw [lip_cases_pin0] at hΦn
      have hgr := hGr n (lip_cases_nat_le hn₁ hn0n) hnmt
      have hox := hOsc n hnmt.le
      have hx₀n : ‖x₀ - z‖ ≤ (3 : ℝ) ^ n / 2 := by
        have := h3pow n₀ n hn0n
        linarith only [hx₀d, this]
      refine ⟨?_, fun _ => ?_⟩
      · exact lip_cases_b2a hgr hox hΦn hK1 hTT0
      · exact lip_cases_b2b (hshA n hnmt.le x₀ hx₀n).2 hΦn hG1T hK1' hTT0
    · -- the frontier is first met above the scale `n`
      have hcn : shiftCube z (n : ℤ) ⊆ W := hn₀min n hnn0
      refine ⟨?_, fun hn => absurd hcn hn⟩
      have hn1 : n₁ = n₀ := lip_cases_nat_eq hn₁ hnn0
      rcases Nat.lt_or_ge (n + 1) n₀ with hlt | hge
      · -- `n + 1 < n₀`: the interior estimate up to `n₀ - 1`
        obtain ⟨k, hk, hnk, hnk', hkmt, hkn0, hk1, hk2⟩ := lip_cases_nat_pred hlt hn1 hn₀mt
        have hck : shiftCube z (k : ℤ) ⊆ W := hn₀min k hkn0
        have hsk := hs k hnk hkmt
        have hsk0 : 0 < s k := by linarith only [hsk.1]
        have hI := hint n k le_rfl hnk' hkmt hck
        have hint'' := lip_cases_int (n := n) (k := k) (m := mt) hnk hkmt hck hI hF f u hsol hFae
        have key : ∀ v : Vec d → ℝ, lipL2 (shiftCube z (k : ℤ)) (fun x => v x - ⨍ w in shiftCube z (k : ℤ), v w) =
            lipL2 (shiftCube z (k : ℤ) ∩ W) (fun x => v x - ⨍ w in shiftCube z (k : ℤ) ∩ W, v w) :=
          fun v => by rw [Set.inter_eq_left.2 hck]
        rw [key u.toFun] at hint''
        have hΦk := hΦ (k + 1) hk1 hk2
        rw [lip_cases_pin0] at hΦk
        have hox := hOsc k hkmt
        have hmk := hmono k hk2 hck (fun x => u.toFun x - g x₀)
          ((hmu (k + 1) hk2).sub (memLp_const _))
        have hpk := hpow k
        have hp0 : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ k := pow_nonneg (by norm_num) k
        have hosc := lip_cases_osc_step hpk hp0 hq1 hox hmk hΦk
        have hs1 : (Real.sqrt (s mt))⁻¹ ≤ 2 * (Real.sqrt (s k))⁻¹ :=
          lip_inv_sqrt_le hsmt0 hsk0 (by linarith only [hsk.2.2.1, hsmt0])
        have hs2 : (s k)⁻¹ ≤ 2 * (s mt)⁻¹ := lip_inv_le hsmt0 hsk.2.1
        have hFk := lip_cases_Fk hs2 (inv_nonneg.2 hsmt0.le) (pow_nonneg (by norm_num) k)
          (h3pow k mt hkmt) hF hFT
        have hg0 : 0 ≤ Real.sqrt nu * lipGradL2 (shiftCube z (n : ℤ) ∩ W) u.grad :=
          mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
        have hgs := lip_cases_gr_mono hs1 hg0
        have hosn : 0 ≤ ((3 : ℝ)⁻¹) ^ n * lipL2 (shiftCube z (n : ℤ) ∩ W)
            (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ W, u.toFun w) :=
          mul_nonneg (pow_nonneg (by norm_num) n) ENNReal.toReal_nonneg
        exact lip_cases_b3 hgs hosn hint'' hosc hFk hCin0 hK3 hTT0
      · -- `n₀ = n + 1`: one Caccioppoli step
        have hn0 : n₀ = n + 1 := lip_cases_nat_succ hge hnn0
        have hsn := hs (n + 1) (Nat.le_succ n) hnmt
        have hcc2 : LipCaccBdryS a nu (s mt) (2 * Cin) E W z (n + 1) :=
          (hcacc (n + 1) (Nat.le_succ n) hnmt).monoC (by linarith only [hsn.1]) hsn.2.2.1 hsn.2.1
            (by linarith only [hCin]) le_rfl
        have hgr := lip_bdry_det_grad (a := a) (nu := nu) (s := s mt) (Cin := 2 * Cin) (E := E)
          (lam := lam) (Lam := Lam) (W := W) (z := z) (x₀ := z) (k := n) (m := mt) hnmt hnu hsmt
          (by linarith only [hCin]) hE (lip_cases_nat_one hN) hWo (by rw [sub_self, norm_zero]; exact (hpos n).le) hell hcc2 (hDv0 n) f g F G1 G2 u hg
          hF hG1 hG2 hDg hD2g hFae hsol hz 0
        have hx₀n : ‖x₀ - z‖ ≤ (3 : ℝ) ^ (n + 1) / 2 := by rw [← hn0]; exact hx₀d
        have hΦk := hΦ (n + 1) (le_of_eq (hn1.trans hn0)) hnmt
        rw [lip_cases_pin0] at hΦk
        have hz1 := (hshA (n + 1) hnmt z (by rw [sub_self, norm_zero]; exact (hpos (n + 1)).le)).1
        have hz2 := (hshA (n + 1) hnmt x₀ hx₀n).2
        have hΦz : lipPin (shiftCube z ((n + 1 : ℕ) : ℤ) ∩ W) (n + 1) z (g z) u.toFun 0 ≤
            3 * Cd * TT + 2 * G1 := by
          rw [lip_cases_pin0]
          linarith only [hz1, hz2, hΦk]
        have hmk := hmono n hnmt hcn (fun x => u.toFun x - g x₀)
          ((hmu (n + 1) hnmt).sub (memLp_const _))
        have hpk := hpow n
        have hp0 : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ n := pow_nonneg (by norm_num) n
        have hosc := lip_cases_osc_step hpk hp0 hq1 (hOsc n hnmt.le) hmk hΦk
        have hF3 := lip_cases_scale_mono (h3pow n mt hnmt.le) (inv_nonneg.2 hsmt0.le) hF
        have hG3 := lip_cases_scale_mono (h3pow n mt hnmt.le)
          (Real.rpow_nonneg (Nat.cast_nonneg n) (-E)) hG2
        exact lip_cases_b4 hgr (by rw [norm_zero, mul_zero]) hΦz hG1T (hF3.trans hFT)
          (hG3.trans hGT) hosc hCin0 hK2 hTT0

/-- Witness: the numerical and geometric hypotheses of `lip_bdry_cases` hold together on the
unit ball, with the scales `N` and `N + 1` and a frontier point within the top cube. -/
example [NeZero d] (N₀ : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ (M₁ MU rU : ℝ) (W : Set (Vec d)) (rW M₂W DW nu E : ℝ) (s δ : ℕ → ℝ) (z : Vec d)
      (n mt A : ℕ), 0 < rU ∧ 0 ≤ MU ∧ 0 < nu ∧ 0 ≤ E ∧ N₀ ≤ n ∧ n < mt ∧
      (∀ k, n ≤ k → k ≤ mt →
        1 ≤ s k ∧ s mt ≤ 2 * s k ∧ s k ≤ 2 * s mt ∧ 0 ≤ δ k ∧
          ((k : ℝ) ^ A)⁻¹ * Real.sqrt (s k) ≤ δ k * Real.sqrt nu ∧
          ((k : ℝ) ^ A)⁻¹ * s k ≤ 1) ∧
      ∑ k ∈ Finset.Icc n mt, δ k ≤ c ∧
      IsUniformC11Domain W rW M₁ M₂W DW ∧ rU * (3 : ℝ) ^ mt ≤ rW ∧ M₂W * (3 : ℝ) ^ mt ≤ MU ∧
      z ∈ W ∧ (∃ x₀ ∈ frontier W, ‖x₀ - z‖ ≤ (3 : ℝ) ^ mt / 2) := by
  obtain ⟨r, M₁, M₂, D, h⟩ := isUniformC11Domain_euclidBall (d := d)
  have hr : 0 < r := h.2.1
  obtain ⟨x₀, hx₀, hx₀n⟩ := lip_bdry_det_euclid_frontier (d := d)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max N₀ (⌈2 / c⌉₊ + 1) := ⟨_, rfl⟩
  have hN1 : N₀ ≤ N := hN ▸ le_max_left _ _
  have hN2 : 2 / c ≤ (N : ℝ) := by
    have h1 : ⌈2 / c⌉₊ + 1 ≤ N := hN ▸ le_max_right _ _
    have h2 : (⌈2 / c⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast h1
    linarith only [h2, Nat.le_ceil (2 / c)]
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have h3 : (3 : ℝ) ≤ 3 ^ (N + 1) := by
    calc (3 : ℝ) = 3 ^ 1 := (pow_one _).symm
      _ ≤ 3 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨M₁, |M₂| * 3 ^ (N + 1), r / 3 ^ (N + 1), Section6.euclidBall (d := d) 1, r, M₂, D, 1, 0,
    fun _ => 1, fun k => ((k : ℝ) ^ 1)⁻¹, 0, N, N + 1, 1, by positivity, by positivity, one_pos,
    le_rfl, hN1, Nat.lt_succ_self N, ?_, ?_, h, ?_, ?_, Section6.zero_mem_euclidBall one_pos,
    ⟨x₀, hx₀, ?_⟩⟩
  · intro k hk1 hk2
    have hk1' : (1 : ℝ) ≤ k := le_trans hNpos (by exact_mod_cast hk1)
    refine ⟨le_rfl, by norm_num, by norm_num, by positivity, by simp, ?_⟩
    simpa using inv_le_one_of_one_le₀ hk1'
  · rw [Finset.sum_Icc_succ_top (Nat.le_succ N), Finset.Icc_self, Finset.sum_singleton]
    have hN3 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith only [hNpos]
    have e1 : (((N : ℝ) ^ 1)⁻¹) ≤ c / 2 := by
      rw [pow_one, inv_le_comm₀ (by linarith only [hNpos]) (by linarith only [hc])]
      have : 2 / c = (c / 2)⁻¹ := by rw [inv_div]
      rw [← this]; exact hN2
    have e2 : ((((N + 1 : ℕ) : ℝ) ^ 1)⁻¹) ≤ ((N : ℝ) ^ 1)⁻¹ := by
      rw [pow_one, pow_one]
      exact inv_anti₀ (by linarith only [hNpos]) (by push_cast; linarith only)
    linarith only [e1, e2]
  · rw [div_mul_cancel₀ _ (by positivity)]
  · exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  · have : (3 : ℝ) ^ (N + 1) / 2 ≥ 3 / 2 := by linarith only [h3]
    simp only [sub_zero]
    linarith only [hx₀n, this]

end SuperdiffusionCLT.Section7
