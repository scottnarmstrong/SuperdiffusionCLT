/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.HolderRootD
public import SuperdiffusionCLT.Section7.MinimalScale.GridMax
public import SuperdiffusionCLT.Section7.MinimalScale.RootScalesC

/-!
# The large-scale Hölder estimate: deterministic core

Given the interior estimate at one sample (at all admissible translated cubes), the sharp window
for `σ̄_m`, and the minimal scale `m⋆`, the large-scale Hölder estimate holds at radii at least
`12 √d 3^{m⋆}`, with a constant depending only on `d, γ, C₀, N_γ` and the window constant.
-/

@[expose] public section

open MeasureTheory Homogenization SuperdiffusionCLT.Section6
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The constant `B` with `log R ≤ B mT`. -/
noncomputable def hr_B (d : ℕ) : ℝ := 2 * Real.log 3 + Real.log d / 2

theorem hr_B_pos [NeZero d] : 0 < hr_B d := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  have := Real.log_nonneg h1
  unfold hr_B; positivity

/-- The source weight at the top scale is `≲ (log R)^{-1/2} R²`. -/
theorem hr_G_bound [NeZero d] {aσ R s : ℝ} {mT : ℕ} (haσ : 0 < aσ) (hs : aσ / 2 * Real.sqrt mT ≤ s)
    (hmT1 : 1 ≤ mT) (h3 : Real.sqrt d * (3 : ℝ) ^ mT ≤ 2 * R)
    (h4 : 2 * R < Real.sqrt d * (3 : ℝ) ^ (mT + 1)) (hR : 1 < R) :
    3 * (s⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ))) ≤
      24 * Real.sqrt (hr_B d) / aσ * (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) := by
  have hsd := h1_sqrt_d_pos (d := d)
  have hB := hr_B_pos (d := d)
  have hmT1' : (1 : ℝ) ≤ mT := by exact_mod_cast hmT1
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hR0 : 0 < R := by linarith only [hR]
  have hsm : 0 < Real.sqrt mT := Real.sqrt_pos.2 (by linarith only [hmT1'])
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  -- log R ≤ B mT
  have hlogle : Real.log R ≤ hr_B d * mT := by
    have h5 : R ≤ Real.sqrt d * (3 : ℝ) ^ (mT + 1) := by
      nlinarith only [h4, hsd, pow_pos (by norm_num : (0 : ℝ) < 3) (mT + 1), hR0]
    have h6 := Real.log_le_log hR0 h5
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_sqrt (by positivity)]
      at h6
    have h1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne d))
    have hld := Real.log_nonneg h1
    have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    unfold hr_B
    push_cast at h6
    nlinarith only [h6, hld, hl3, hmT1']
  -- shom⁻¹ ≤ 2/(aσ √mT)
  have hsinv : s⁻¹ ≤ 2 / (aσ * Real.sqrt mT) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hs0 (by positivity)]
    nlinarith only [hs]
  -- 3^(2 mT) ≤ 4 R²
  have h33 : (3 : ℝ) ^ (2 * (mT : ℝ)) = ((3 : ℝ) ^ mT) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have h3m : (3 : ℝ) ^ mT ≤ 2 * R := by
    have : (1 : ℝ) * (3 : ℝ) ^ mT ≤ Real.sqrt d * (3 : ℝ) ^ mT :=
      mul_le_mul_of_nonneg_right hsd (by positivity)
    linarith only [this, h3]
  have h3sq : (3 : ℝ) ^ (2 * (mT : ℝ)) ≤ 4 * R ^ 2 := by
    rw [h33]
    nlinarith only [h3m, pow_pos (by norm_num : (0 : ℝ) < 3) mT]
  -- 1 / √mT ≤ √B (log R)^{-1/2}
  have hrp : Real.log R ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (Real.log R) := by
    rw [Real.rpow_neg hlogR.le, ← Real.sqrt_eq_rpow, one_div]
  have hsq : 1 / Real.sqrt mT ≤ Real.sqrt (hr_B d) * (1 / Real.sqrt (Real.log R)) := by
    have : Real.sqrt (Real.log R) ≤ Real.sqrt (hr_B d) * Real.sqrt mT := by
      rw [← Real.sqrt_mul hB.le]; exact Real.sqrt_le_sqrt hlogle
    have hl : 0 < Real.sqrt (Real.log R) := Real.sqrt_pos.2 hlogR
    rw [mul_one_div, div_le_div_iff₀ hsm hl]
    linarith only [this]
  have hA1 : s⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)) ≤
      2 / aσ * (1 / Real.sqrt mT) * (4 * R ^ 2) := by
    calc s⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)) ≤ 2 / (aσ * Real.sqrt mT) * (4 * R ^ 2) :=
          mul_le_mul hsinv h3sq (by positivity) (by positivity)
      _ = _ := by field_simp
  rw [hrp]
  calc 3 * (s⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ))) ≤ 3 * (2 / aσ * (1 / Real.sqrt mT) * (4 * R ^ 2)) :=
        mul_le_mul_of_nonneg_left hA1 (by norm_num)
    _ ≤ 3 * (2 / aσ * (Real.sqrt (hr_B d) * (1 / Real.sqrt (Real.log R))) * (4 * R ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)) (by norm_num)
    _ = _ := by field_simp; ring

/-- The cut `nK` is the cut `ms_e` past the threshold. -/
theorem hr_nK_eq {N : ℝ} (hN : 0 ≤ N) {n : ℕ} (hn : ms_j0 N ≤ n) :
    ((nK N n : ℕ) : ℤ) = ms_e N n := by
  have hK : (4 * N + 2) ^ 2 ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hc := ceil_le_half hN hK
  have hc' : ⌈N * Real.log (n : ℝ)⌉₊ ≤ n := by
    have : (⌈N * Real.log (n : ℝ)⌉₊ : ℝ) ≤ n := by linarith only [hc, (Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈N * Real.log (n : ℝ)⌉₊)]
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ n := by nlinarith only [sq_nonneg N, hK, hN]
  have hlog : 0 ≤ N * Real.log (n : ℝ) := mul_nonneg hN (Real.log_nonneg h1)
  unfold nK ms_e
  rw [Nat.cast_sub hc', Int.natCast_ceil_eq_ceil hlog]

/-- The cut is at most `n`. -/
theorem hr_nK_le (N : ℝ) (n : ℕ) : nK N n ≤ n := Nat.sub_le _ _

/-- The constant in front of the cube estimate. -/
noncomputable def hr_C1 (γ C0 : ℝ) (Nγ : ℕ) : ℝ := 2 * C0 * (3 : ℝ) ^ (γ * (Nγ : ℝ))

/-- The constant of the ball estimate. -/
noncomputable def hr_const (d : ℕ) (γ C0 : ℝ) (Nγ : ℕ) (aσ : ℝ) : ℝ :=
  2 * (hr_C1 γ C0 Nγ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + hr_C1 γ C0 Nγ) *
    (9 * Real.sqrt d) ^ γ * max 1 (24 * Real.sqrt (hr_B d) / aσ)

/-- **Deterministic core of the large-scale Hölder estimate.** -/
theorem hr_core [NeZero d] {a : CoeffField d} {shom : ℕ → ℝ} {C0 c N Lhat X0 ε ρ γ aσ : ℝ}
    {A mstar k0 m1 Nγ : ℕ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hC0 : 1 ≤ C0) (hε : 0 < ε) (hNγ : 1 ≤ Nγ)
    (hq : C0 * (3 : ℝ) ^ (-(Nγ : ℤ)) ≤ 1 / 2 * (3 : ℝ) ^ (-γ * (Nγ : ℝ)))
    (hA : 7 * Real.sqrt d ≤ (3 : ℝ) ^ A) (hm1 : 1 ≤ m1) (haσ : 0 < aσ)
    (hIP : ∀ m n : ℕ, n < m →
      ((m : ℝ) - (n : ℝ)) * (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
      Lhat ≤ (nK N n : ℝ) → X0 ≤ (3 : ℝ) ^ nK N n →
      ∀ y ∈ gridPts d ((nK N n : ℤ) - 3) ((3 : ℝ) ^ (n + A)),
        ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube y (m : ℤ))),
          IsWeakSolutionOn a (shiftCube y (m : ℤ)) u f (fun _ => 0) →
          eLpNorm (fun x => u.toFun x - ⨍ z in shiftCube y (n : ℤ), u.toFun z) ⊤
              (volume.restrict (shiftCube y (n : ℤ))) ≤
            ENNReal.ofReal (C0 * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
              (lpBar (shiftCube y (m : ℤ)) 2
                  (fun x => u.toFun x - ⨍ z in shiftCube y (m : ℤ), u.toFun z) +
                ENNReal.ofReal ((shom m)⁻¹ * (3 : ℝ) ^ (2 * (m : ℝ))) *
                  eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))))
    (hthr : ∀ n : ℕ, mstar ≤ n → Lhat ≤ (nK N n : ℝ) ∧ X0 ≤ (3 : ℝ) ^ nK N n ∧ k0 ≤ n ∧ m1 ≤ n)
    (hδk : ∀ k : ℕ, k0 ≤ k →
      (Nγ : ℝ) * (ε * (k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ)) ≤ c)
    (hsig : ∀ k : ℕ, m1 ≤ k → aσ / 2 * Real.sqrt k ≤ shom k ∧ shom k ≤ 3 * aσ / 2 * Real.sqrt k) :
    ∀ R r : ℝ, 12 * Real.sqrt d * (3 : ℝ) ^ mstar ≤ r → r ≤ R / 2 →
      ∀ (f : Vec d → ℝ) (u : H1Function (euclidBall (d := d) R)),
        IsWeakSolutionOn a (euclidBall (d := d) R) u f (fun _ => 0) →
        ∀ C : ℝ, hr_const d γ C0 Nγ aσ ≤ C →
          eLpNorm (fun x => u.toFun x - ∫ y, u.toFun y ∂(ballMeasure (d := d) r)) ⊤
              (volume.restrict (euclidBall (d := d) r)) ≤
            ENNReal.ofReal (C * (r / R) ^ γ) *
              (ballL2 R (fun x => u.toFun x - ∫ y, u.toFun y ∂(ballMeasure (d := d) R)) +
                ENNReal.ofReal (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) *
                  eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R))) := by
  intro R r hr0 hrR f u hu C hC
  have hsd := h1_sqrt_d_pos (d := d)
  have h3m : (1 : ℝ) ≤ (3 : ℝ) ^ mstar := one_le_pow₀ (by norm_num)
  have hr12 : 12 ≤ r := by nlinarith only [hr0, hsd, h3m]
  have hrpos : 0 < r := by linarith only [hr12]
  have hR24 : 24 ≤ R := by linarith only [hrR, hr12]
  have hR : 0 < R := by linarith only [hR24]
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith only [hR24])
  have hC1 := hr_C1 γ C0 Nγ
  have hC₁pos : 0 < hr_C1 γ C0 Nγ := by unfold hr_C1; positivity
  have hKd : 1 ≤ (24 * Real.sqrt d) ^ d := one_le_pow₀ (by linarith only [hsd])
  have hconst0 : 0 < hr_const d γ C0 Nγ aσ := by
    unfold hr_const
    have : 0 < max 1 (24 * Real.sqrt (hr_B d) / aσ) := lt_of_lt_of_le one_pos (le_max_left _ _)
    positivity
  have hCpos : 0 < C := lt_of_lt_of_le hconst0 hC
  by_cases hfT : eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R)) = ⊤
  · rw [hfT]
    have hy : 0 < Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2 := by positivity
    have hx : 0 < C * (r / R) ^ γ := by positivity
    rw [ENNReal.mul_top (by simpa using hy), add_top, ENNReal.mul_top (by simpa using hx)]
    exact le_top
  have hu2 : MemLp u.toFun 2 (volume.restrict (euclidBall (d := d) R)) := u.memL2
  set φ : ℝ := (eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R))).toReal with hφ
  have hφ0 : 0 ≤ φ := ENNReal.toReal_nonneg
  -- the top scale
  set mT : ℕ := ⌊Real.logb 3 (2 * R / Real.sqrt d)⌋₊ with hmTdef
  have hmT : ∀ m : ℕ, Real.sqrt d * (3 : ℝ) ^ m ≤ 2 * R → m ≤ mT := by
    intro m hm
    refine Nat.le_floor ?_
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    rw [Real.rpow_natCast, le_div_iff₀ (by linarith only [hsd])]
    linarith only [hm, mul_comm (Real.sqrt d) ((3 : ℝ) ^ m)]
  have hmstar2 : Real.sqrt d * (3 : ℝ) ^ mstar ≤ 2 * R := by
    nlinarith only [hr0, hrR, hsd, h3m]
  have hmstarT : mstar ≤ mT := hmT mstar hmstar2
  have hmstar1 : 1 ≤ mstar := hm1.trans (hthr mstar le_rfl).2.2.2
  have hquot : 1 ≤ 2 * R / Real.sqrt d := by
    rw [le_div_iff₀ (by linarith only [hsd])]
    have : Real.sqrt d ≤ Real.sqrt d * (3 : ℝ) ^ mstar := by nlinarith only [h3m, hsd]
    linarith only [this, hmstar2]
  have hlb0 : 0 ≤ Real.logb 3 (2 * R / Real.sqrt d) := Real.logb_nonneg (by norm_num) hquot
  have hmT3 : Real.sqrt d * (3 : ℝ) ^ mT ≤ 2 * R := by
    have h1 : (mT : ℝ) ≤ Real.logb 3 (2 * R / Real.sqrt d) := Nat.floor_le hlb0
    have h2 := (Real.le_logb_iff_rpow_le (by norm_num) (by positivity)).1 h1
    rw [Real.rpow_natCast, le_div_iff₀ (by linarith only [hsd])] at h2
    linarith only [h2, mul_comm (Real.sqrt d) ((3 : ℝ) ^ mT)]
  have hmT4 : 2 * R < Real.sqrt d * (3 : ℝ) ^ (mT + 1) := by
    have h1 : Real.logb 3 (2 * R / Real.sqrt d) < (mT : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 := (Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)).1 h1
    rw [show (mT : ℝ) + 1 = ((mT + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      div_lt_iff₀ (by linarith only [hsd])] at h2
    linarith only [h2, mul_comm (Real.sqrt d) ((3 : ℝ) ^ (mT + 1))]
  -- the window for shom and the ratio
  have hpos : ∀ k : ℕ, mstar ≤ k → 0 < shom k := by
    intro k hk
    have hk1 := (hthr k hk).2.2.2
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hm1.trans hk1
    have := (hsig k hk1).1
    have : 0 < aσ / 2 * Real.sqrt k := by
      have : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 (by linarith only [hk1'])
      positivity
    linarith only [this, (hsig k hk1).1]
  have hrat : ∀ k m : ℕ, mstar ≤ k → k ≤ m → shom m ≤ 3 * (1 + ((m : ℝ) - k)) * shom k := by
    intro k m hk hkm
    have hk1 := (hthr k hk).2.2.2
    have hm1' := (hthr m (hk.trans hkm)).2.2.2
    exact hr_ratio haσ (hm1.trans hk1) hkm (hsig k hk1).1 (hsig m hm1').2
  -- one block for the centred cubes, with the bound `φ` for the source
  have hstep0 : ∀ n k : ℕ, mstar ≤ n → n < k → k - n ≤ Nγ →
      h1_cube (0 : Vec d) k ⊆ euclidBall (d := d) R →
      MemLp u.toFun ⊤ (volume.restrict (h1_cube (0 : Vec d) n)) ∧
        h1_linf (h1_cube (0 : Vec d) n) u.toFun (h1_avg (h1_cube (0 : Vec d) n) u.toFun) ≤
          C0 * (3 : ℝ) ^ (-((k : ℤ) - (n : ℤ))) *
            (h1_l2 (h1_cube (0 : Vec d) k) u.toFun + (shom k)⁻¹ * (3 : ℝ) ^ (2 * (k : ℝ)) * φ) := by
    intro n k hn hnk hkn hsub
    obtain ⟨hL, hX, hk0n, hm1n⟩ := hthr n hn
    have hnk' : n ≤ k := hnk.le
    have hs := hpos k (hn.trans hnk')
    have hδ : ((k : ℝ) - (n : ℝ)) * (ε * (k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ)) ≤ c := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hm1.trans (hm1n.trans hnk')
      have hnn : 0 ≤ ε * (k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ) :=
        mul_nonneg (mul_nonneg hε.le (Real.rpow_nonneg (by linarith only [hk1]) _))
          (Real.log_nonneg hk1)
      have h2 : ((k : ℝ) - n) ≤ Nγ := by
        have : ((k - n : ℕ) : ℝ) ≤ Nγ := by exact_mod_cast hkn
        rwa [Nat.cast_sub hnk'] at this
      exact (mul_le_mul_of_nonneg_right h2 hnn).trans (hδk k (hk0n.trans hnk'))
    obtain ⟨hM, hb⟩ := hr_step hIP hR hnk hδ hL hX hs (y := 0)
      ((mem_gridPts (by positivity) _).2 ⟨fun _ => 0, fun i => by simp, fun i => by simp⟩) hsub
      (by linarith only [hC0]) hfT u hu
    refine ⟨hM, hb.trans ?_⟩
    have hfk : (eLpNorm f ⊤ (volume.restrict (h1_cube (0 : Vec d) k))).toReal ≤ φ :=
      ENNReal.toReal_mono hfT (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))
    have hsk : 0 ≤ (shom k)⁻¹ * (3 : ℝ) ^ (2 * (k : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hfk hsk) _)
      (by positivity)
  have hshT := hpos mT hmstarT
  have hFg : ∀ k : ℕ, mstar ≤ k → k ≤ mT →
      (shom k)⁻¹ * (3 : ℝ) ^ (2 * (k : ℝ)) ≤ 3 * ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ))) := by
    intro k hk hkm
    have h := hr_F_bound hγ1.le hkm (hpos k hk) hshT (hrat k mT hk hkm)
    refine h.trans ?_
    have : (3 : ℝ) ^ (-γ * ((mT : ℝ) - k)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (k : ℝ) ≤ mT := by exact_mod_cast hkm
      nlinarith only [this, hγ0]
    have hp : 0 ≤ (shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)) := by positivity
    nlinarith only [this, hp]
  set C₁ := hr_C1 γ C0 Nγ with hC₁def
  set G : ℝ := 3 * ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)) * φ) with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hball := hr_ball_holder (R := R) (r := r) (γ := γ) (C₁ := C₁) (G := G) (m₀ := mstar)
    (mT := mT) (A := A) (u := u.toFun) (lv := fun n => (nK N n : ℤ) - 3) hR hu2 hγ0.le hC₁pos.le
    hG0 hr0 hrR (fun n => by have := hr_nK_le N n; omega) hA hmT
    (fun n m hn hnm hcube hmTm => by
      obtain ⟨hmem, hle⟩ := hr_iterate (u := u.toFun) (R := R) hγ0.le hγ1.le hC0 hφ0 hNγ hq hpos
        hrat hstep0 hn hnm hmTm hcube
      refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
      rw [hC₁def, hGdef]; unfold hr_C1; ring)
    (fun n hn y hylat hyb hsub hmTn => by
      obtain ⟨hL, hX, hk0n, hm1n⟩ := hthr n hn
      have hs := hpos (n + 1) (hn.trans (Nat.le_succ n))
      have hδ : (((n + 1 : ℕ) : ℝ) - (n : ℝ)) * (ε * ((n + 1 : ℕ) : ℝ) ^ (-((1 - ρ) / 2)) *
          Real.log ((n + 1 : ℕ) : ℝ)) ≤ c := by
        have hk1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
        have hnn : 0 ≤ ε * ((n + 1 : ℕ) : ℝ) ^ (-((1 - ρ) / 2)) * Real.log ((n + 1 : ℕ) : ℝ) :=
          mul_nonneg (mul_nonneg hε.le (Real.rpow_nonneg (by linarith only [hk1]) _))
            (Real.log_nonneg hk1)
        have h2 : (((n + 1 : ℕ) : ℝ) - (n : ℝ)) = 1 := by push_cast; ring
        have h3 : (1 : ℝ) ≤ Nγ := by exact_mod_cast hNγ
        rw [h2, one_mul]
        exact (le_mul_of_one_le_left hnn h3).trans (hδk (n + 1) (hk0n.trans (Nat.le_succ n)))
      choose kk hkk using hylat
      obtain ⟨hM, hb⟩ := hr_step hIP hR (Nat.lt_succ_self n) hδ hL hX hs (y := y)
        ((mem_gridPts (by positivity) y).2 ⟨kk, hkk, hyb⟩) hsub (by linarith only [hC0]) hfT u hu
      refine ⟨hM, hb.trans ?_⟩
      have hfk : (eLpNorm f ⊤ (volume.restrict (h1_cube y (n + 1)))).toReal ≤ φ :=
        ENNReal.toReal_mono hfT (eLpNorm_mono_measure f (Measure.restrict_mono hsub le_rfl))
      have h31 : (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) - (n : ℤ))) ≤ 1 := by
        apply zpow_le_one_of_nonpos₀ (by norm_num); push_cast; omega
      have hC0C1 : C0 ≤ C₁ := by
        have : (1 : ℝ) ≤ (3 : ℝ) ^ (γ * (Nγ : ℝ)) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        rw [hC₁def]; unfold hr_C1; nlinarith only [this, hC0]
      have hterm : (shom (n + 1))⁻¹ * (3 : ℝ) ^ (2 * ((n + 1 : ℕ) : ℝ)) *
          (eLpNorm f ⊤ (volume.restrict (h1_cube y (n + 1)))).toReal ≤ G := by
        have := hFg (n + 1) (hn.trans (Nat.le_succ n)) hmTn
        rw [hGdef]
        calc _ ≤ (shom (n + 1))⁻¹ * (3 : ℝ) ^ (2 * ((n + 1 : ℕ) : ℝ)) * φ :=
              mul_le_mul_of_nonneg_left hfk (by positivity)
          _ ≤ 3 * ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ))) * φ :=
              mul_le_mul_of_nonneg_right this hφ0
          _ = _ := by ring
      have hl2 : 0 ≤ h1_l2 (h1_cube y (n + 1)) u.toFun := Real.sqrt_nonneg _
      have hCn : 0 ≤ C0 * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) - (n : ℤ))) := by positivity
      calc _ ≤ C0 * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ) - (n : ℤ))) * (h1_l2 (h1_cube y (n + 1)) u.toFun + G) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hterm _) hCn
        _ ≤ C₁ * (h1_l2 (h1_cube y (n + 1)) u.toFun + G) := by
            refine mul_le_mul ?_ le_rfl (by linarith only [hl2, hG0]) hC₁pos.le
            nlinarith only [h31, hC0C1, hC0])
  obtain ⟨hmemr, hineq⟩ := hball
  -- the source weight
  have hGb := hr_G_bound (d := d) (aσ := aσ) (R := R) (s := shom mT) (mT := mT) haσ
    (hsig mT (hthr mT hmstarT).2.2.2).1 (hmstar1.trans hmstarT) hmT3 hmT4
    (by linarith only [hR24])
  set Cg : ℝ := 24 * Real.sqrt (hr_B d) / aσ with hCg
  set Z : ℝ := Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2 with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hGZ : G ≤ Cg * Z * φ := by
    rw [hGdef]
    calc 3 * ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ)) * φ) =
          3 * ((shom mT)⁻¹ * (3 : ℝ) ^ (2 * (mT : ℝ))) * φ := by ring
      _ ≤ Cg * Z * φ := mul_le_mul_of_nonneg_right hGb hφ0
  have hl2B : 0 ≤ h1_l2 (euclidBall (d := d) R) u.toFun := Real.sqrt_nonneg _
  have hMx : h1_l2 (euclidBall (d := d) R) u.toFun + G ≤
      max 1 Cg * (h1_l2 (euclidBall (d := d) R) u.toFun + Z * φ) := by
    have h1 : 1 ≤ max 1 Cg := le_max_left _ _
    have h2 : Cg ≤ max 1 Cg := le_max_right _ _
    have hZφ : 0 ≤ Z * φ := mul_nonneg hZ0 hφ0
    nlinarith only [h1, h2, hGZ, hZφ, hl2B, mul_le_mul_of_nonneg_right h2 hZφ]
  have hrR0 : 0 ≤ (r / R) ^ γ := by positivity
  have hreal : h1_linf (euclidBall (d := d) r) u.toFun (h1_avg (euclidBall (d := d) r) u.toFun) ≤
      C * (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u.toFun + Z * φ) := by
    refine hineq.trans ?_
    have hbase : 0 ≤ 2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁) *
        (9 * Real.sqrt d) ^ γ := by positivity
    have hconst : hr_const d γ C0 Nγ aσ = 2 * (C₁ * (24 * Real.sqrt d) ^ d +
        (24 * Real.sqrt d) ^ d + C₁) * (9 * Real.sqrt d) ^ γ * max 1 Cg := by
      unfold hr_const; rfl
    have hsum : 0 ≤ h1_l2 (euclidBall (d := d) R) u.toFun + Z * φ :=
      add_nonneg hl2B (mul_nonneg hZ0 hφ0)
    calc 2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁) * (9 * Real.sqrt d) ^ γ *
          (r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u.toFun + G)
        ≤ 2 * (C₁ * (24 * Real.sqrt d) ^ d + (24 * Real.sqrt d) ^ d + C₁) *
            (9 * Real.sqrt d) ^ γ * (r / R) ^ γ *
            (max 1 Cg * (h1_l2 (euclidBall (d := d) R) u.toFun + Z * φ)) :=
          mul_le_mul_of_nonneg_left hMx (mul_nonneg hbase hrR0)
      _ = hr_const d γ C0 Nγ aσ * ((r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u.toFun + Z * φ)) := by
          rw [hconst]; ring
      _ ≤ C * ((r / R) ^ γ * (h1_l2 (euclidBall (d := d) R) u.toFun + Z * φ)) :=
          mul_le_mul_of_nonneg_right hC (mul_nonneg hrR0 hsum)
      _ = _ := by ring
  -- back to the extended reals
  have hvr := h1_vol_ball_ne_top (d := d) hrpos
  have hmem' := hr_memLp_sub hmemr hvr (h1_avg (euclidBall (d := d) r) u.toFun)
  have hne : eLpNorm (fun x => u.toFun x - h1_avg (euclidBall (d := d) r) u.toFun) ⊤
      (volume.restrict (euclidBall (d := d) r)) ≠ ⊤ := hmem'.eLpNorm_ne_top
  have hfe : eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) R)) = ENNReal.ofReal φ :=
    (ENNReal.ofReal_toReal hfT).symm
  rw [hr_ballL2_osc hR hu2, hr_ballAvg r, hfe, ← ENNReal.ofReal_mul hZ0,
    ← ENNReal.ofReal_add hl2B (mul_nonneg hZ0 hφ0), ← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal (by simpa only [h1_linf] using hreal)

/-- The block length. -/
theorem hr_Ngamma {γ C0 : ℝ} (hγ : γ < 1) (hC0 : 1 ≤ C0) :
    ∃ N : ℕ, 1 ≤ N ∧ C0 * (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 / 2 * (3 : ℝ) ^ (-γ * (N : ℝ)) := by
  have h1γ : 0 < 1 - γ := by linarith only [hγ]
  have hC : 0 < 2 * C0 := by linarith only [hC0]
  refine ⟨⌈Real.logb 3 (2 * C0) / (1 - γ)⌉₊ + 1, by omega, ?_⟩
  set N : ℕ := ⌈Real.logb 3 (2 * C0) / (1 - γ)⌉₊ + 1 with hNdef
  have hN : Real.logb 3 (2 * C0) ≤ (1 - γ) * N := by
    have h1 : Real.logb 3 (2 * C0) / (1 - γ) ≤ (N : ℝ) := by
      have := Nat.le_ceil (Real.logb 3 (2 * C0) / (1 - γ))
      rw [hNdef]; push_cast; linarith only [this]
    rw [div_le_iff₀ h1γ] at h1
    linarith only [h1, mul_comm (N : ℝ) (1 - γ)]
  have ht : 2 * C0 ≤ (3 : ℝ) ^ ((1 - γ) * (N : ℝ)) := by
    calc 2 * C0 = (3 : ℝ) ^ (Real.logb 3 (2 * C0)) := (Real.rpow_logb (by norm_num) (by norm_num) hC).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hN
  have e1 : (3 : ℝ) ^ (-(N : ℤ)) = (3 : ℝ) ^ (-γ * (N : ℝ)) * ((3 : ℝ) ^ ((1 - γ) * (N : ℝ)))⁻¹ := by
    rw [← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num), ← Real.rpow_intCast]
    congr 1; push_cast; ring
  rw [e1]
  have htp : 0 < (3 : ℝ) ^ ((1 - γ) * (N : ℝ)) := by positivity
  have h3 : 0 < (3 : ℝ) ^ (-γ * (N : ℝ)) := by positivity
  have : C0 * ((3 : ℝ) ^ ((1 - γ) * (N : ℝ)))⁻¹ ≤ 1 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ htp]; linarith only [ht]
  calc C0 * ((3 : ℝ) ^ (-γ * (N : ℝ)) * ((3 : ℝ) ^ ((1 - γ) * (N : ℝ)))⁻¹) =
        (3 : ℝ) ^ (-γ * (N : ℝ)) * (C0 * ((3 : ℝ) ^ ((1 - γ) * (N : ℝ)))⁻¹) := by ring
    _ ≤ (3 : ℝ) ^ (-γ * (N : ℝ)) * (1 / 2) := mul_le_mul_of_nonneg_left this h3.le
    _ = _ := by ring

/-- The cut `ms_e` is at most `n`. -/
theorem hr_ms_e_le {N : ℝ} (hN : 0 ≤ N) {n : ℕ} (hn : 1 ≤ n) : ms_e N n ≤ n := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ ⌈N * Real.log (n : ℝ)⌉ := Int.ceil_nonneg (mul_nonneg hN (Real.log_nonneg h1))
  unfold ms_e; omega

/-- **The large-scale Hölder estimate from the interior estimate and the sharp bounds.** -/
theorem hr_large_scale_holder (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hIP :

      ∃ C c N : ℝ, 1 ≤ C ∧ 0 < c ∧ 0 ≤ N ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∀ ε ρ : ℝ, 0 < ε → ε ≤ 1 → 0 < ρ → ρ < 1 →
                ∀ A : ℕ,
                  ∃ Lhat : ℝ, 1 ≤ Lhat ∧
                    ∀ (P : MeasureTheory.ProbabilityMeasure
                          (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                      (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                      (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                      (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                      SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                      SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                      SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                          hPrefix hJ2 hJ3 →
                      ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                        Measurable X ∧ (∀ omega, 1 ≤ X omega) ∧
                        Homogenization.IndependentSums.IsBigO P.toMeasure
                          (Homogenization.IndependentSums.gammaSigma ρ)
                          (fun omega => Real.log (X omega)) Lhat ∧
                        ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                            ∂P.toMeasure,
                          ∀ m n : ℕ,
                            n < m →
                            ((m : ℝ) - (n : ℝ)) *
                                (ε * (m : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (m : ℝ)) ≤ c →
                            Lhat ≤ (SuperdiffusionCLT.Section7.nK N n : ℝ) →
                            X omega ≤ (3 : ℝ) ^ SuperdiffusionCLT.Section7.nK N n →
                            ∀ y ∈ SuperdiffusionCLT.Section7.gridPts d
                                ((SuperdiffusionCLT.Section7.nK N n : ℤ) - 3)
                                ((3 : ℝ) ^ (n + A)),
                              ∀ (f : Homogenization.Vec d → ℝ)
                                (u : Homogenization.H1Function
                                  (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))),
                                SuperdiffusionCLT.Section7.IsWeakSolutionOn
                                    (SuperdiffusionCLT.Section6.fullCoefficientRecentered
                                      nu omega)
                                    (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ))
                                    u f (fun _ => 0) →
                                -- e.Dir.new.interior.pointwise
                                MeasureTheory.eLpNorm
                                    (fun x => u.toFun x -
                                      ⨍ z in SuperdiffusionCLT.Section7.shiftCube y (n : ℤ),
                                        u.toFun z)
                                    ⊤
                                    (MeasureTheory.volume.restrict
                                      (SuperdiffusionCLT.Section7.shiftCube y (n : ℤ))) ≤
                                  ENNReal.ofReal (C * (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) *
                                    (SuperdiffusionCLT.Section7.lpBar
                                        (SuperdiffusionCLT.Section7.shiftCube y (m : ℤ)) 2
                                        (fun x => u.toFun x -
                                          ⨍ z in SuperdiffusionCLT.Section7.shiftCube y
                                              (m : ℤ),
                                            u.toFun z) +
                                      ENNReal.ofReal
                                          ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                              nu m P)⁻¹ *
                                            (3 : ℝ) ^ (2 * (m : ℝ))) *
                                        MeasureTheory.eLpNorm f ⊤
                                          (MeasureTheory.volume.restrict
                                            (SuperdiffusionCLT.Section7.shiftCube y
                                              (m : ℤ)))))
    (hSigma :

      ∃ C : ℝ, 1 ≤ C ∧
        ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
          ∀ cStar : ℝ, 0 < cStar →
            ∀ K : ℝ,
              ∃ M : ℕ,
                ∀ (P : MeasureTheory.ProbabilityMeasure
                      (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                  SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                      hPrefix hJ2 hJ3 →
                    ∀ m : ℕ, M ≤ m →
                      |SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P -
                          (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
                        C * cStar⁻¹ * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) :

    ∀ γ σ : ℝ, 0 < γ → γ < 1 → 0 < σ → σ < 1 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ C : ℝ, 1 ≤ C ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                  Measurable X ∧ (∀ omega, 2 ≤ X omega) ∧
                  -- e.large.scale.Holder.X
                  (∀ t : ℝ, 2 ≤ t →
                    P.toMeasure.real {omega | t < X omega} ≤
                      C * Real.exp (-(C⁻¹ * Real.log t ^ σ))) ∧
                  ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    -- Liouville theorem, e.Liouville.Calpha
                    (∀ (u : Homogenization.Vec d → ℝ)
                        (G : Homogenization.Vec d → Homogenization.Vec d),
                      SuperdiffusionCLT.Section6.IsEntireSolution
                          (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                          u G →
                      Filter.liminf
                          (fun r : ℝ => ENNReal.ofReal (r ^ (-γ)) *
                            SuperdiffusionCLT.Section6.ballL2 r u)
                          Filter.atTop = 0 →
                      ∃ c : ℝ, u =ᵐ[MeasureTheory.volume] fun _ => c) ∧
                    -- e.large.scale.Holder
                    (∀ R : ℝ, X omega ≤ R →
                      ∀ (f : Homogenization.Vec d → ℝ)
                        (u : Homogenization.H1Function
                          (SuperdiffusionCLT.Section6.euclidBall (d := d) R)),
                        SuperdiffusionCLT.Section7.IsWeakSolutionOn
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            (SuperdiffusionCLT.Section6.euclidBall R) u f (fun _ => 0) →
                        ∀ r : ℝ, X omega ≤ r → r ≤ R / 2 →
                          MeasureTheory.eLpNorm
                              (fun x => u.toFun x -
                                ∫ y, u.toFun y ∂SuperdiffusionCLT.Section6.ballMeasure r)
                              ⊤
                              (MeasureTheory.volume.restrict
                                (SuperdiffusionCLT.Section6.euclidBall r)) ≤
                            ENNReal.ofReal (C * (r / R) ^ γ) *
                              (SuperdiffusionCLT.Section6.ballL2 R
                                  (fun x => u.toFun x -
                                    ∫ y, u.toFun y
                                      ∂SuperdiffusionCLT.Section6.ballMeasure R) +
                                ENNReal.ofReal (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) *
                                  MeasureTheory.eLpNorm f ⊤
                                    (MeasureTheory.volume.restrict
                                      (SuperdiffusionCLT.Section6.euclidBall R)))) := by
  intro γ σ hγ0 hγ1 hσ0 hσ1 nu hnu0 hnu1 cStar hcs K
  obtain ⟨C0, c, N, hC0, hc, hN, hIPc⟩ := hIP
  obtain ⟨Cs, hCs, hSigc⟩ := hSigma
  obtain ⟨Mσ, hMσ⟩ := hSigc nu hnu0 hnu1 cStar hcs K
  have hsd := h1_sqrt_d_pos (d := d)
  set ρ : ℝ := (σ + 1) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith only [hσ0]
  have hρ1 : ρ < 1 := by rw [hρ]; linarith only [hσ1]
  have hσρ : σ ≤ ρ := by rw [hρ]; linarith only [hσ1]
  set A : ℕ := ⌈7 * Real.sqrt d⌉₊ with hAdef
  have hA : 7 * Real.sqrt d ≤ (3 : ℝ) ^ A := by
    have h1 : 7 * Real.sqrt d ≤ (A : ℝ) := Nat.le_ceil _
    have h2 : A < 3 ^ A := Nat.lt_pow_self (by norm_num)
    have h3 : (A : ℝ) ≤ (3 : ℝ) ^ A := by exact_mod_cast h2.le
    linarith only [h1, h3]
  obtain ⟨Lhat, hL1, hLaw⟩ := hIPc nu hnu0 hnu1 cStar hcs K 1 ρ one_pos le_rfl hρ0 hρ1 A
  obtain ⟨aσ, haσ, m1, hm1, hwin⟩ := hr_sigma_window (K := K) hcs hCs
  obtain ⟨Nγ, hNγ, hq⟩ := hr_Ngamma hγ1 hC0
  have hNγ0 : (0 : ℝ) < Nγ := by exact_mod_cast hNγ
  obtain ⟨k0, hk01, hk0⟩ := hr_small_delta (β := (1 - ρ) / 2) (c := c / Nγ)
    (by linarith only [hρ1]) (by positivity)
  set m1' : ℕ := max m1 Mσ with hm1'
  set L : ℝ := max Lhat (max (k0 : ℝ) (m1' : ℝ)) with hLdef
  have hL0 : 0 ≤ L := le_trans (by linarith only [hL1]) (le_max_left _ _)
  have hC12 : 1 ≤ 12 * Real.sqrt d := by linarith only [hsd]
  obtain ⟨Ct, hCt1, hCt⟩ := hr_scale_tail (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (Λ := Lhat) (ρ := ρ) (σ := σ) (N₀ := N) (L := L) (C₀ := 12 * Real.sqrt d)
    (by linarith only [hL1]) hσ0 hσρ hN hL0 hC12
  set Cfin : ℝ := max Ct (hr_const d γ C0 Nγ aσ) with hCfin
  have hCfin1 : 1 ≤ Cfin := le_trans hCt1 (le_max_left _ _)
  refine ⟨Cfin, hCfin1, ?_⟩
  intro P hPrefix hJ2 hJ3 h1 h4 h5
  obtain ⟨X0, hmeas, hX1, hbigO, hae⟩ := hLaw P hPrefix hJ2 hJ3 h1 h4 h5
  have hSigP := hMσ P hPrefix hJ2 hJ3 h1 h4 h5
  have hmst := ms_star_measurable (N₀ := N) (L := L) hN hX1 hmeas
  refine ⟨fun ω => 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω), ?_, ?_, ?_, ?_⟩
  · exact measurable_const.mul ((measurable_from_top (f := fun n : ℕ => (3 : ℝ) ^ n)).comp hmst)
  · intro ω
    have : (1 : ℝ) ≤ (3 : ℝ) ^ ms_star N L (X0 ω) := one_le_pow₀ (by norm_num)
    show 2 ≤ 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω)
    have h12 : (12 : ℝ) ≤ 12 * Real.sqrt d := by linarith only [hsd]
    have := mul_le_mul h12 this (by norm_num) (by positivity)
    linarith only [this]
  · intro t ht
    have ht1 : (1 : ℝ) ≤ t := by linarith only [ht]
    have h := hCt P.toMeasure X0 hX1 hbigO t ht1
    have hsub : {ω | t < 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω)} ⊆
        {ω | t ≤ 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω)} := fun ω (hω : t < _) => (le_of_lt hω : t ≤ _)
    refine (measureReal_mono hsub).trans (h.trans ?_)
    have hv : 0 ≤ Real.log t ^ σ := Real.rpow_nonneg (Real.log_nonneg ht1) _
    have hCt0 : 0 < Ct := by linarith only [hCt1]
    have hle : Cfin⁻¹ ≤ Ct⁻¹ := inv_anti₀ hCt0 (le_max_left _ _)
    have h2 : Real.exp (-(Ct⁻¹ * Real.log t ^ σ)) ≤ Real.exp (-(Cfin⁻¹ * Real.log t ^ σ)) :=
      Real.exp_le_exp.2 (by nlinarith only [hle, hv])
    calc Ct * Real.exp (-(Ct⁻¹ * Real.log t ^ σ)) ≤ Cfin * Real.exp (-(Cfin⁻¹ * Real.log t ^ σ)) :=
          mul_le_mul (le_max_left _ _) h2 (Real.exp_pos _).le (by linarith only [hCfin1])
      _ = _ := rfl
  · filter_upwards [hae] with ω hω
    have hX2 : 2 ≤ 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω) := by
      have : (1 : ℝ) ≤ (3 : ℝ) ^ ms_star N L (X0 ω) := one_le_pow₀ (by norm_num)
      have h12 : (12 : ℝ) ≤ 12 * Real.sqrt d := by linarith only [hsd]
      have := mul_le_mul h12 this (by norm_num) (by positivity)
      linarith only [this]
    have hHold : ∀ R : ℝ, 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω) ≤ R →
        ∀ (f : Homogenization.Vec d → ℝ)
          (u : Homogenization.H1Function (SuperdiffusionCLT.Section6.euclidBall (d := d) R)),
          IsWeakSolutionOn
            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu ω)
            (SuperdiffusionCLT.Section6.euclidBall R) u f (fun _ => 0) →
          ∀ r : ℝ, 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω) ≤ r → r ≤ R / 2 →
            eLpNorm (fun x => u.toFun x -
                ∫ y, u.toFun y ∂SuperdiffusionCLT.Section6.ballMeasure r) ⊤
              (volume.restrict (SuperdiffusionCLT.Section6.euclidBall r)) ≤
            ENNReal.ofReal (Cfin * (r / R) ^ γ) *
              (SuperdiffusionCLT.Section6.ballL2 R
                  (fun x => u.toFun x - ∫ y, u.toFun y
                    ∂SuperdiffusionCLT.Section6.ballMeasure R) +
                ENNReal.ofReal (Real.log R ^ (-(1 / 2 : ℝ)) * R ^ 2) *
                  eLpNorm f ⊤ (volume.restrict (SuperdiffusionCLT.Section6.euclidBall R))) := by
      intro R _ f u hu r hr hrR
      refine hr_core (shom := fun m => SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P)
        (C0 := C0) (c := c) (N := N) (Lhat := Lhat) (X0 := X0 ω) (ε := 1) (ρ := ρ) (γ := γ)
        (aσ := aσ) (A := A) (mstar := ms_star N L (X0 ω)) (k0 := k0) (m1 := m1') (Nγ := Nγ)
        hγ0 hγ1 hC0 one_pos hNγ hq hA (hm1.trans (le_max_left _ _)) haσ hω ?_ ?_ ?_ R r hr hrR f u hu
        Cfin (le_max_right _ _)
      · intro n hn
        obtain ⟨hj0, hLe, hXe⟩ := ms_star_persist hN (hX1 ω) hn
        have hn1 : 1 ≤ n := le_trans (ms_j0_ge_one hN) hj0
        have hnK := hr_nK_eq hN hj0
        have hnKr : (nK N n : ℝ) = ((ms_e N n : ℤ) : ℝ) := by rw [← hnK]; simp
        have hle : (ms_e N n : ℝ) ≤ n := by exact_mod_cast hr_ms_e_le hN hn1
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hnKr]; exact (le_max_left _ _).trans hLe
        · rw [← hnK, zpow_natCast] at hXe; exact hXe
        · have : (k0 : ℝ) ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (hLe.trans hle)
          exact_mod_cast this
        · have : (m1' : ℝ) ≤ n :=
            le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (hLe.trans hle)
          exact_mod_cast this
      · intro k hk
        have h2 := hk0 k hk
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk01.trans hk
        have hnn : 0 ≤ (k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ) :=
          mul_nonneg (Real.rpow_nonneg (by linarith only [hk1]) _) (Real.log_nonneg hk1)
        rw [one_mul]
        calc (Nγ : ℝ) * ((k : ℝ) ^ (-((1 - ρ) / 2)) * Real.log (k : ℝ)) ≤ Nγ * (c / Nγ) :=
              mul_le_mul_of_nonneg_left h2 hNγ0.le
          _ = c := by field_simp
      · intro k hk
        refine hwin k ((le_max_left _ _).trans hk) _ (hSigP k ((le_max_right _ _).trans hk))
    exact ⟨fun u G hu hlim => hr_liouville (X := 12 * Real.sqrt d * (3 : ℝ) ^ ms_star N L (X0 ω))
      (by linarith only [hX2]) (by linarith only [hCfin1]) hHold u G hu hlim, hHold⟩

end SuperdiffusionCLT.Section7
