/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Finite

/-!
# Finite-volume estimate: one block and the iteration over blocks
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- One block: a solution `r` on `□_m` is reduced at scale `j` by a global corrected affine. -/
theorem eb5b_step [NeZero d] {a : CoeffField d} {C5 Ct c4 η κ : ℝ} {δ : ℕ → ℝ} {Hb mstar : ℕ}
    (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)) (hCt : 0 ≤ Ct) (hCtc4 : Ct * c4 ≤ 1)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
        ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c4)
    (hblock : ∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
        ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
          ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
            ∀ k : ℕ, l ≤ k → k ≤ j →
              cubeFlat k (fun x => w x - V j e x) ≤
                C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w)
    (htrans : ∀ m j l : ℕ, mstar ≤ j → j ≤ m → l ≤ j → j ≤ l + Hb → ∀ p : Vec d,
        ∃ pt : Vec d,
          engNorm pt ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p ∧
            ∀ k : ℕ, l ≤ k → k ≤ j →
              cubeFlat k (fun x => V m pt x - V j p x) ≤
                Ct * δ j * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * engNorm p)
    {m j l : ℕ} (hj : mstar ≤ j) (hjm : j ≤ m) (hlj : l ≤ j) (hjl : j ≤ l + Hb)
    {r : Vec d → ℝ} (hr : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) r g) :
    ∃ pt : Vec d,
      engNorm pt ≤ Ct * C5 * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * cubeFlat j r ∧
        ∀ k : ℕ, l ≤ k → k ≤ j →
          cubeFlat k (fun x => r x - V m pt x) ≤
            2 * C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j r := by
  obtain ⟨p, hp1, hp2⟩ := hblock j l hj hlj hjl r (eb5b_restrict (hell j) hjm hr)
  obtain ⟨pt, ht1, ht2⟩ := htrans m j l hj hjm hlj hjl p
  have hp0 := engNorm_nonneg p
  have hΩ0 := cubeFlat_nonneg j r
  refine ⟨pt, ?_, ?_⟩
  · calc engNorm pt ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p := ht1
      _ ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * (C5 * cubeFlat j r) :=
          mul_le_mul_of_nonneg_left hp1 (mul_nonneg hCt (Real.rpow_nonneg (by norm_num) _))
      _ = Ct * C5 * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * cubeFlat j r := by ring
  · intro k hlk hkj
    have hkm : k ≤ m := hkj.trans hjm
    have hfm : MemLp (fun x => r x - V j p x) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      (eb5b_memLp (hell k) hkm hr).sub (eb5b_memLp (hell k) hkj (hVsol j hj p))
    have hgm : MemLp (fun x => V m pt x - V j p x) 2
        (normalizedCubeMeasure (originCube d (k : ℤ))) :=
      (eb5b_memLp (hell k) hkm (hVsol m (hj.trans hjm) pt)).sub
        (eb5b_memLp (hell k) hkj (hVsol j hj p))
    have hsub := eb5b_flat_sub_le hfm hgm
    have e : (fun x => r x - V m pt x) =
        fun x => (r x - V j p x) - (V m pt x - V j p x) := by
      funext x; ring
    rw [e]
    have h1 := hp2 k hlk hkj
    have h2 := ht2 k hlk hkj
    obtain ⟨hδ0, hδ1⟩ := hδ j hj
    have hδc : δ j ≤ c4 := by
      have : (0 : ℝ) ≤ (Hb : ℝ) := Nat.cast_nonneg _
      nlinarith only [hδ0, hδ1, this]
    have hE : 0 ≤ (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) := Real.rpow_nonneg (by norm_num) _
    have hCtδ : Ct * δ j ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hδc hCt
      linarith only [this, hCtc4]
    have h3 : Ct * δ j * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * engNorm p ≤
        1 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * (C5 * cubeFlat j r) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hCtδ hE) hp1 hp0 (by positivity)
    linarith only [hsub, h1, h2, h3]

theorem eb5b_J_succ_le (k0 m Hb i : ℕ) : max k0 (m - (i + 1) * Hb) ≤ max k0 (m - i * Hb) := by
  have : m - (i + 1) * Hb = m - i * Hb - Hb := by rw [Nat.succ_mul, Nat.sub_add_eq]
  rw [this]
  generalize m - i * Hb = X
  omega

theorem eb5b_J_le_succ (k0 m Hb i : ℕ) : max k0 (m - i * Hb) ≤ max k0 (m - (i + 1) * Hb) + Hb := by
  have : m - (i + 1) * Hb = m - i * Hb - Hb := by rw [Nat.succ_mul, Nat.sub_add_eq]
  rw [this]
  generalize m - i * Hb = X
  omega

theorem eb5b_J_le (k0 m Hb i : ℕ) (h : k0 ≤ m) : max k0 (m - i * Hb) ≤ m := by
  omega

theorem eb5b_J_gap (k0 m Hb i : ℕ) (h : k0 < max k0 (m - i * Hb)) :
    (m : ℝ) - ((max k0 (m - i * Hb) : ℕ) : ℝ) = (i : ℝ) * Hb := by
  have h1 : i * Hb ≤ m := by omega
  have h2 : max k0 (m - i * Hb) = m - i * Hb := by omega
  rw [h2, Nat.cast_sub h1]
  push_cast
  ring

theorem eb5b_cb_pow {Cb κ : ℝ} {Hb : ℕ} (h0 : 0 ≤ Cb) (h : Cb ≤ (3 : ℝ) ^ (κ * (Hb : ℝ))) (i : ℕ) :
    Cb ^ i ≤ (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) := by
  calc Cb ^ i ≤ ((3 : ℝ) ^ (κ * (Hb : ℝ))) ^ i := pow_le_pow_left₀ h0 h i
    _ = (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1; ring

/-- One step of the iteration: the increment and its two bounds. -/
theorem eb5b_iter_step [NeZero d] {a : CoeffField d} {C5 Ct c4 η κ : ℝ} {δ : ℕ → ℝ}
    {Hb mstar : ℕ} (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)) (hC5 : 1 ≤ C5) (hCt : 0 ≤ Ct)
    (hCtc4 : Ct * c4 ≤ 1) (hCb : 2 * C5 ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
        ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c4)
    (hblock : ∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
        ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
          ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
            ∀ k : ℕ, l ≤ k → k ≤ j →
              cubeFlat k (fun x => w x - V j e x) ≤
                C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w)
    (htrans : ∀ m j l : ℕ, mstar ≤ j → j ≤ m → l ≤ j → j ≤ l + Hb → ∀ p : Vec d,
        ∃ pt : Vec d,
          engNorm pt ≤ Ct * (3 : ℝ) ^ (κ * ((m : ℝ) - (j : ℝ))) * engNorm p ∧
            ∀ k : ℕ, l ≤ k → k ≤ j →
              cubeFlat k (fun x => V m pt x - V j p x) ≤
                Ct * δ j * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * engNorm p)
    {m k0 : ℕ} (hk0 : mstar ≤ k0) (hkm : k0 ≤ m)
    {w : Vec d → ℝ} (hw : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) w g) (i : ℕ) (e : Vec d)
    (hAi : cubeFlat (max k0 (m - i * Hb)) (fun x => w x - V m e x) ≤
      (2 * C5) ^ i * (3 : ℝ) ^ (-(η * ((m : ℝ) - ((max k0 (m - i * Hb) : ℕ) : ℝ)))) *
        cubeFlat m w) :
    ∃ pt : Vec d,
      (∀ k : ℕ, max k0 (m - (i + 1) * Hb) ≤ k → k ≤ max k0 (m - i * Hb) →
        cubeFlat k (fun x => w x - V m (e + pt) x) ≤
          (2 * C5) ^ (i + 1) * (3 : ℝ) ^ (-(η * ((m : ℝ) - (k : ℝ)))) * cubeFlat m w) ∧
      engNorm pt ≤ Ct * C5 * (3 : ℝ) ^ (-((η - 2 * κ) * ((i : ℝ) * Hb))) * cubeFlat m w := by
  have hΩm := cubeFlat_nonneg m w
  have hC2 : 1 ≤ 2 * C5 := by linarith only [hC5]
  have hrsol : ∃ g : Vec d → Vec d, IsSolOn a (engCube d m) (fun x => w x - V m e x) g :=
    eb5b_sol_sub (hell m) hw (hVsol m (hk0.trans hkm) e)
  set J := max k0 (m - i * Hb) with hJ
  have hk0J : k0 ≤ J := le_max_left _ _
  have hJm : J ≤ m := eb5b_J_le k0 m Hb i hkm
  have hE : 0 ≤ (3 : ℝ) ^ (-(η * ((m : ℝ) - (J : ℝ)))) := Real.rpow_nonneg (by norm_num) _
  by_cases hcase : k0 < J
  · obtain ⟨pt, hp1, hp2⟩ := eb5b_step V hCt hCtc4 hell hVsol hδ hblock htrans
      (j := J) (l := max k0 (m - (i + 1) * Hb)) (hk0.trans hk0J) hJm
      (eb5b_J_succ_le k0 m Hb i) (eb5b_J_le_succ k0 m Hb i) hrsol
    refine ⟨pt, ?_, ?_⟩
    · intro k hk1 hk2
      have h := hp2 k hk1 hk2
      have e1 : (fun x => w x - V m (e + pt) x) = fun x => (w x - V m e x) - V m pt x := by
        funext x; simp only [map_add, Pi.add_apply]; ring
      rw [e1]
      have hE2 : 0 ≤ (3 : ℝ) ^ (-(η * ((J : ℝ) - (k : ℝ)))) := Real.rpow_nonneg (by norm_num) _
      have hsplit : (3 : ℝ) ^ (-(η * ((J : ℝ) - (k : ℝ)))) *
          (3 : ℝ) ^ (-(η * ((m : ℝ) - (J : ℝ)))) = (3 : ℝ) ^ (-(η * ((m : ℝ) - (k : ℝ)))) := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1; ring
      have h2 : 2 * C5 * (3 : ℝ) ^ (-(η * ((J : ℝ) - (k : ℝ)))) *
          cubeFlat J (fun x => w x - V m e x) ≤
          2 * C5 * (3 : ℝ) ^ (-(η * ((J : ℝ) - (k : ℝ)))) *
            ((2 * C5) ^ i * (3 : ℝ) ^ (-(η * ((m : ℝ) - (J : ℝ)))) * cubeFlat m w) :=
        mul_le_mul_of_nonneg_left hAi (by positivity)
      calc _ ≤ _ := h
        _ ≤ _ := h2
        _ = (2 * C5) ^ (i + 1) * ((3 : ℝ) ^ (-(η * ((J : ℝ) - (k : ℝ)))) *
              (3 : ℝ) ^ (-(η * ((m : ℝ) - (J : ℝ))))) * cubeFlat m w := by ring
        _ = _ := by rw [hsplit]
    · have hgap := eb5b_J_gap k0 m Hb i hcase
      have hu : (0 : ℝ) ≤ (i : ℝ) * Hb := by positivity
      have hY : cubeFlat J (fun x => w x - V m e x) ≤
          (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) *
            ((3 : ℝ) ^ (-(η * ((i : ℝ) * Hb))) * cubeFlat m w) := by
        rw [hgap] at hAi
        have hb := eb5b_cb_pow (by linarith only [hC2]) hCb i
        calc _ ≤ _ := hAi
          _ ≤ (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) * (3 : ℝ) ^ (-(η * ((i : ℝ) * Hb))) *
                cubeFlat m w := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb
                (Real.rpow_nonneg (by norm_num) _)) hΩm
          _ = _ := by ring
      have hX : (3 : ℝ) ^ (κ * ((m : ℝ) - (J : ℝ))) = (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) := by
        rw [hgap]
      have hsum : (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) * ((3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) *
          (3 : ℝ) ^ (-(η * ((i : ℝ) * Hb)))) = (3 : ℝ) ^ (-((η - 2 * κ) * ((i : ℝ) * Hb))) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
        congr 1; ring
      have hCC : 0 ≤ Ct * C5 := mul_nonneg hCt (by linarith only [hC5])
      have hXn : 0 ≤ (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) := Real.rpow_nonneg (by norm_num) _
      calc engNorm pt ≤ Ct * C5 * (3 : ℝ) ^ (κ * ((m : ℝ) - (J : ℝ))) *
            cubeFlat J (fun x => w x - V m e x) := hp1
        _ ≤ Ct * C5 * (3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) *
            ((3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) *
              ((3 : ℝ) ^ (-(η * ((i : ℝ) * Hb))) * cubeFlat m w)) := by
            rw [hX]
            exact mul_le_mul_of_nonneg_left hY (mul_nonneg hCC hXn)
        _ = Ct * C5 * ((3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) * ((3 : ℝ) ^ (κ * ((i : ℝ) * Hb)) *
              (3 : ℝ) ^ (-(η * ((i : ℝ) * Hb))))) * cubeFlat m w := by ring
        _ = _ := by rw [hsum]
  · refine ⟨0, ?_, ?_⟩
    · intro k hk1 hk2
      have hkJ : k = J := by omega
      subst hkJ
      have e1 : (fun x => w x - V m (e + 0) x) = fun x => w x - V m e x := by
        funext x; simp
      rw [e1]
      refine hAi.trans ?_
      have hp : (2 * C5) ^ i ≤ (2 * C5) ^ (i + 1) := pow_le_pow_right₀ hC2 (Nat.le_succ i)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hE) hΩm
    · rw [eb5b_engNorm_zero]
      have : 0 ≤ Ct * C5 := mul_nonneg hCt (by linarith only [hC5])
      positivity

end SuperdiffusionCLT.Section6
