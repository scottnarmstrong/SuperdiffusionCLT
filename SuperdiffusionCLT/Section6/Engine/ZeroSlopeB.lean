/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.CubeNorms

/-!
# Zero bottom slope forces decay: the key estimate

Elementary lemmas on the Euclidean length and the affine slope, and the key estimate: if the
bottom slope of `V m f + R` vanishes and `R` decays towards the bottom scale, then `f` is small
and `V m f + R` decays.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb6a_memLp_mono {k m : ℕ} (hkm : k ≤ m) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (m : ℤ)))) :
    MemLp f 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := by
  induction m, hkm using Nat.le_induction with
  | base => exact hf
  | succ m _ ih => exact ih (e0b_memLp_step hf).1

theorem eb6a_engNorm_neg (x : Vec d) : engNorm (-x) = engNorm x := by
  have h := engNorm_smul (-1 : ℝ) x
  simpa using h

theorem eb6a_engNorm_sub_le (x y : Vec d) : engNorm (x - y) ≤ engNorm x + engNorm y := by
  have h := engNorm_add_le x (-y)
  rwa [← sub_eq_add_neg, eb6a_engNorm_neg] at h

theorem eb6a_norm_le_add (x y : Vec d) : engNorm y ≤ engNorm x + engNorm (x - y) := by
  have h := eb6a_engNorm_sub_le x (x - y)
  rwa [show x - (x - y) = y by abel] at h

theorem eb6a_norm_le_add' (x y : Vec d) : engNorm x ≤ engNorm y + engNorm (x - y) := by
  have h := engNorm_add_le y (x - y)
  rwa [show y + (x - y) = x by abel] at h

theorem eb6a_engNorm_sub_comm (x y : Vec d) : engNorm (x - y) = engNorm (y - x) := by
  rw [← neg_sub, eb6a_engNorm_neg]

theorem eb6a_tri (x y z : Vec d) : engNorm (x - z) ≤ engNorm (x - y) + engNorm (y - z) := by
  have h := engNorm_add_le (x - y) (y - z)
  rwa [show x - y + (y - z) = x - z by abel] at h

theorem eb6a_slope_sub [NeZero d] {n : ℕ} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ))))
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    affSlope n (fun x => f x - g x) = affSlope n f - affSlope n g := by
  have h1 : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by
    funext x
    ring
  have hg' : MemLp (fun x => (-1 : ℝ) * g x) 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
    hg.const_mul (-1)
  rw [h1, affSlope_add hf hg', affSlope_const_mul]
  simp [sub_eq_add_neg]

theorem eb6a_slope_le [NeZero d] {n : ℕ} {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    engNorm (affSlope n f) ≤ 4 * cubeFlat n f := by
  have h := engNorm_affSlope_le hf
  have h3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have h0 := cubeFlat_nonneg n f
  nlinarith only [h, h3, h0]

theorem eb6a_flat_of_chain [NeZero d] {k : ℕ} {g h : Vec d → ℝ}
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (k : ℤ))))
    (hh : MemLp h 2 (normalizedCubeMeasure (originCube d (k : ℤ)))) {q : Vec d}
    {dk K Cc : ℝ}
    (h1 : cubeFlat k (fun x => g x - h x) ≤ Cc * dk * engNorm q)
    (h2 : cubeFlat k (fun x => h x - vecDot (affSlope k h) x) ≤ K * dk * engNorm q)
    (h3 : engNorm (affSlope k h - q) ≤ K * dk * engNorm q)
    (hK : K * dk ≤ 1 / 4) (hC : Cc * dk ≤ 1) :
    cubeFlat k g ≤ 2 * engNorm q := by
  have hl := e0c_memLp k (e0c_continuous_vecDot (affSlope k h))
  have hsub : MemLp (fun x => g x - h x) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    hg.sub hh
  have hsub2 : MemLp (fun x => h x - vecDot (affSlope k h) x) 2
      (normalizedCubeMeasure (originCube d (k : ℤ))) := hh.sub hl
  have e1 : cubeFlat k g ≤ cubeFlat k (fun x => g x - h x) + cubeFlat k h := by
    calc cubeFlat k g = cubeFlat k (fun x => (g x - h x) + h x) := by
          congr 1
          funext x
          ring
      _ ≤ _ := cubeFlat_add_le hsub hh
  have e2 : cubeFlat k h ≤ cubeFlat k (fun x => h x - vecDot (affSlope k h) x) +
      cubeFlat k (fun x => vecDot (affSlope k h) x) := by
    calc cubeFlat k h = cubeFlat k (fun x => (h x - vecDot (affSlope k h) x) +
          vecDot (affSlope k h) x) := by
          congr 1
          funext x
          ring
      _ ≤ _ := cubeFlat_add_le hsub2 hl
  rw [cubeFlat_vecDot] at e2
  have hq0 := engNorm_nonneg q
  have hs0 := engNorm_nonneg (affSlope k h)
  have e3 := eb6a_norm_le_add' (affSlope k h) q
  have h3' : 3 ≤ 2 * Real.sqrt 3 := by
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hs' := Real.sqrt_nonneg 3
    nlinarith only [hs, hs']
  have e4 : engNorm (affSlope k h) / (2 * Real.sqrt 3) ≤ engNorm (affSlope k h) / 3 :=
    div_le_div_of_nonneg_left hs0 (by norm_num) h3'
  have a1 : Cc * dk * engNorm q ≤ engNorm q := by nlinarith only [hC, hq0]
  have a2 : K * dk * engNorm q ≤ 1 / 4 * engNorm q := by nlinarith only [hK, hq0]
  have a3 : engNorm (affSlope k h) ≤ 5 / 4 * engNorm q := by linarith only [e3, h3, a2]
  have a4 : engNorm (affSlope k h) / 3 ≤ 5 / 12 * engNorm q := by linarith only [a3]
  linarith only [e1, e2, e4, a1, a2, a4, h1, h2, hq0]

theorem eb6a_lower {n m : ℕ} (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)) (f : Vec d)
    {dn K Cc P : ℝ} (hCP : 0 ≤ Cc * P)
    (hKd : K * dn ≤ 1 / 2)
    (hfl : ∀ e : Vec d, engNorm (affSlope n (V n e) - e) ≤ K * dn * engNorm e)
    (hq : ∃ q : Vec d, affSlope n (V n q) = affSlope n (V m f) ∧
      engNorm f ≤ Cc * P * engNorm q) :
    engNorm f ≤ 2 * (Cc * P) * engNorm (affSlope n (V m f)) := by
  obtain ⟨q, hq1, hq2⟩ := hq
  have h1 := eb6a_norm_le_add (affSlope n (V n q)) q
  have h2 := hfl q
  rw [hq1] at h1 h2
  have hq0 := engNorm_nonneg q
  have h3 : K * dn * engNorm q ≤ 1 / 2 * engNorm q := by nlinarith only [hKd, hq0]
  have h4 : engNorm q ≤ 2 * engNorm (affSlope n (V m f)) := by
    linarith only [h1, h2, h3]
  have h5 := mul_le_mul_of_nonneg_left h4 hCP
  linarith only [hq2, h5]

theorem eb6a_rpow_comb {η κ t : ℝ} (ht : 0 ≤ t) (hη : 4 * κ ≤ η) :
    (3 : ℝ) ^ (κ * t) * (3 : ℝ) ^ (-((η - 3 * κ) * t)) ≤ 1 := by
  rw [← Real.rpow_add (by norm_num)]
  refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
  nlinarith only [mul_nonneg (sub_nonneg.2 hη) ht]

theorem eb6a_key [NeZero d] (K Cc : ℝ) (hCc : 1 ≤ Cc) {η κ : ℝ} (hη : 1 / 2 ≤ η)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 24)
    (δ : ℕ → ℝ) (mstar : ℕ) (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ))
    (hsm : ∀ j, mstar ≤ j → 0 ≤ δ j ∧ K * δ j ≤ 1 / 4 ∧ Cc * δ j ≤ 1)
    (hVmem : ∀ j, mstar ≤ j → ∀ e,
      MemLp (V j e) 2 (normalizedCubeMeasure (originCube d (j : ℤ))))
    (hflat0 : ∀ k, mstar ≤ k → ∀ e : Vec d,
      cubeFlat k (fun x => V k e x - vecDot (affSlope k (V k e)) x) ≤ K * δ k * engNorm e ∧
        engNorm (affSlope k (V k e) - e) ≤ K * δ k * engNorm e)
    (hch : ∀ m k : ℕ, mstar ≤ k → k ≤ m → ∀ e : Vec d, ∃ q : Vec d,
      affSlope k (V k q) = affSlope k (V m e) ∧
        cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
        engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
        engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q)
    {n m : ℕ} (hn : mstar ≤ n) (hnm : n ≤ m) (f : Vec d) (R : Vec d → ℝ) (B : ℝ)
    (hRm : MemLp R 2 (normalizedCubeMeasure (originCube d (m : ℤ))))
    (hR : ∀ k : ℕ, n ≤ k → k ≤ m →
      cubeFlat k R ≤ B * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))))
    (hs : affSlope n (fun x => V m f x + R x) = 0) :
    engNorm f ≤ 8 * Cc * B ∧ ∀ k : ℕ, n ≤ k → k ≤ m →
      cubeFlat k (fun x => V m f x + R x) ≤
        (16 * Cc ^ 2 + 1) * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * B := by
  have hB : 0 ≤ B := by
    have h := hR n le_rfl hnm
    have h0 := cubeFlat_nonneg n R
    have hp : 0 < (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (n : ℝ)))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    by_contra hneg
    have hneg := not_le.1 hneg
    have := mul_neg_of_neg_of_pos hneg hp
    linarith only [h, h0, this]
  have hVm : MemLp (V m f) 2 (normalizedCubeMeasure (originCube d (m : ℤ))) :=
    hVmem m (by omega) f
  have hVn := eb6a_memLp_mono hnm hVm
  have hRn := eb6a_memLp_mono hnm hRm
  have h0 : affSlope n (V m f) + affSlope n R = 0 := by
    rw [← affSlope_add hVn hRn]
    exact hs
  have hsl : affSlope n (V m f) = -(affSlope n R) := eq_neg_of_add_eq_zero_left h0
  have hnorm : engNorm (affSlope n (V m f)) ≤
      4 * (B * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (n : ℝ))))) := by
    rw [hsl, eb6a_engNorm_neg]
    have := eb6a_slope_le hRn
    have := hR n le_rfl hnm
    linarith only [this, ‹engNorm (affSlope n R) ≤ 4 * cubeFlat n R›]
  obtain ⟨hs0, hsK, hsC⟩ := hsm n hn
  have hP : 0 ≤ (3 : ℝ) ^ (κ * ((m : ℝ) - (n : ℝ))) := Real.rpow_nonneg (by norm_num) _
  have hlow := eb6a_lower V f (n := n) (m := m) (dn := δ n) (K := K) (Cc := Cc)
    (P := (3 : ℝ) ^ (κ * ((m : ℝ) - (n : ℝ)))) (mul_nonneg (by linarith only [hCc]) hP)
    (by linarith only [hsK]) (fun e => (hflat0 n hn e).2)
    (by
      obtain ⟨q, h1, _, _, h4⟩ := hch m n hn hnm f
      exact ⟨q, h1, h4⟩)
  have hmn : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hnm
    linarith only [this]
  have hηκ : 4 * κ ≤ η := by linarith only [hη, hκ1]
  have hcomb := eb6a_rpow_comb hmn hηκ
  have hp0 : 0 ≤ (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (n : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  have hCc0 : 0 ≤ Cc := by linarith only [hCc]
  -- the bound on `f`
  have hf8 : engNorm f ≤ 8 * Cc * B *
      ((3 : ℝ) ^ (κ * ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (n : ℝ))))) := by
    have h1 := mul_le_mul_of_nonneg_left hnorm (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (mul_nonneg hCc0 hP))
    calc engNorm f ≤ _ := hlow
      _ ≤ _ := h1
      _ = _ := by ring
  have hCB : 0 ≤ 8 * Cc * B := by positivity
  refine ⟨?_, ?_⟩
  · calc engNorm f ≤ _ := hf8
      _ ≤ 8 * Cc * B * 1 := mul_le_mul_of_nonneg_left hcomb hCB
      _ = _ := mul_one _
  · intro k hk hkm
    have hmk : (0 : ℝ) ≤ (m : ℝ) - (k : ℝ) := by
      have : (k : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hkm
      linarith only [this]
    have hnk : (m : ℝ) - (k : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
      have : (n : ℝ) ≤ (k : ℝ) := Nat.cast_le.2 hk
      linarith only [this]
    have hkstar : mstar ≤ k := le_trans hn hk
    have hVk := eb6a_memLp_mono hkm hVm
    have hRk := eb6a_memLp_mono hkm hRm
    obtain ⟨q', h1, h2, h3, h4⟩ := hch m k hkstar hkm f
    obtain ⟨hk0, hkK, hkC⟩ := hsm k hkstar
    have hVkq := hVmem k hkstar q'
    have hA : cubeFlat k (V m f) ≤ 2 * engNorm q' :=
      eb6a_flat_of_chain hVk hVkq h2 (hflat0 k hkstar q').1 (hflat0 k hkstar q').2 hkK hkC
    -- compare the exponents
    have hQ : (3 : ℝ) ^ (κ * ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (n : ℝ)))) ≤
        (3 : ℝ) ^ (-((η - 4 * κ) * ((m : ℝ) - (k : ℝ)))) := by
      rw [← Real.rpow_add (by norm_num)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith only [mul_nonneg (sub_nonneg.2 hηκ) (sub_nonneg.2 hnk)]
    have hE : (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) *
        (3 : ℝ) ^ (-((η - 4 * κ) * ((m : ℝ) - (k : ℝ)))) =
        (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have hRE : (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))) ≤
        (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      nlinarith only [mul_nonneg hκ0.le hmk]
    have ha : 0 ≤ (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) := Real.rpow_nonneg (by norm_num) _
    have hf8' : engNorm f ≤ 8 * Cc * B *
        (3 : ℝ) ^ (-((η - 4 * κ) * ((m : ℝ) - (k : ℝ)))) :=
      hf8.trans (mul_le_mul_of_nonneg_left hQ hCB)
    have hq' : engNorm q' ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm f := h3
    have hCa : 0 ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) := mul_nonneg hCc0 ha
    have hq'' := hq'.trans (mul_le_mul_of_nonneg_left hf8' hCa)
    have hAE : cubeFlat k (V m f) ≤ 16 * Cc ^ 2 *
        (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * B := by
      rw [← hE]
      calc cubeFlat k (V m f) ≤ 2 * engNorm q' := hA
        _ ≤ 2 * (Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) *
            (8 * Cc * B * (3 : ℝ) ^ (-((η - 4 * κ) * ((m : ℝ) - (k : ℝ)))))) := by
          linarith only [hq'']
        _ = _ := by ring
    have hBE : cubeFlat k R ≤ (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) * B := by
      calc cubeFlat k R ≤ B * (3 : ℝ) ^ (-((η - 3 * κ) * ((m : ℝ) - (k : ℝ)))) := hR k hk hkm
        _ ≤ B * (3 : ℝ) ^ (-((η - 5 * κ) * ((m : ℝ) - (k : ℝ)))) :=
          mul_le_mul_of_nonneg_left hRE hB
        _ = _ := mul_comm _ _
    have hadd := cubeFlat_add_le hVk hRk
    have : cubeFlat k (fun x => V m f x + R x) ≤ _ := hadd
    linarith only [this, hAE, hBE]

end SuperdiffusionCLT.Section6
