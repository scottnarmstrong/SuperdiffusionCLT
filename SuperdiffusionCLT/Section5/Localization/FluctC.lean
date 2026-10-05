/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Localization.FluctB
public import SuperdiffusionCLT.Section5.Response.NeumannOscillation

/-!
# `e.crude.Fz.bound`: the energy of the fluctuation `F_z`

This is Step 3 of the proof of `lem.localization`: the subcube average
of the expected energies `E⟪F_z, F_z⟫ = E[⨍_Q F_z · bfA_m F_z]` is small.  The energy is bounded
pointwise by Young's inequality (`FluctB.lean`) by the fourth moments `⨍_Q|k_m|⁴` of the cutoff field
(`E ≤ C (m+1)²`, `Fluct.lean`) and the fourth moments of the oscillations of the two response fields,
which `crude_Fz_bound` (Neumann oscillation by Dirichlet comparison) bounds by
`C σ⁻⁴ (ν⁻¹m)^{-400}`; the Young parameter `(ν⁻¹m)^{-200}` balances the two.

The bound proved here is `C (ν⁻¹ m)^{-190}`, weaker than the printed `C ν⁻⁴ m⁴ (ν⁻¹m)^{-200}` only in
the exponent, which is irrelevant to its use.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

variable {d : ℕ}

theorem loc_fluct_memL2 {U : Set (Vec d)} (Q : TriadicCube d) {g : Vec d → Vec d}
    (hg : MemVectorL2 U g) (hV : openCubeSet Q ⊆ U) :
    MemVectorL2 (openCubeSet Q) (fun x => g x - volumeAverageVec (cubeSet Q) g) :=
  (SuperdiffusionCLT.Section3.Terms.memVectorL2_mono hV hg).sub (memLp_const _)

/-- The scale `n` of the localization is at most `m`, hence at most `Kc`. -/
theorem loc_n_le {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {m h Kc n : ℕ} (hm : 1 ≤ m)
    (hmK : m ≤ Kc)
    (hn : n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊) : n ≤ Kc := by
  have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have h1 : n ≤ m := by
    rw [hn]
    have : (m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3) ≤ (m : ℝ) := by
      have hl : 0 ≤ Real.log (nu⁻¹ * m) / Real.log 3 :=
        div_nonneg (Real.log_nonneg (by nlinarith only [hmpos, hnuinv]))
          (Real.log_pos (by norm_num)).le
      have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      linarith only [hl, hh0]
    calc ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ ≤ ⌊(m : ℝ)⌋₊ :=
          Nat.floor_le_floor this
      _ = m := Nat.floor_natCast m
  omega

/-- The real arithmetic closing `e.crude.Fz.bound` in the energy form. -/
theorem loc_Fz_arith {nu m c kc C5 σ : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hm : 1 ≤ m)
    (hc : 0 ≤ c) (hkc : 0 ≤ kc) (hC5 : 0 ≤ C5) (hσ : 0 < σ) (hσi : σ⁻¹ ≤ c * nu⁻¹)
    (hσu : σ ≤ (1 + c) * (nu⁻¹ * m)) :
    (nu * σ⁻¹ + nu⁻¹ * σ) * ((nu⁻¹ * m) ^ 200)⁻¹ +
      (nu⁻¹ * σ⁻¹ * ((nu⁻¹ * m) ^ 200)⁻¹ * (kc * (m + 1) ^ 2) +
        (nu * σ⁻¹ + nu⁻¹ * σ⁻¹ + nu⁻¹ * σ) * (((nu⁻¹ * m) ^ 200)⁻¹)⁻¹ *
          (C5 * σ⁻¹ ^ 4 * ((nu⁻¹ * m) ^ 400)⁻¹)) ≤
      ((1 + 2 * c) + 4 * c * kc + (1 + 3 * c) * c ^ 4 * C5) * ((nu⁻¹ * m) ^ 190)⁻¹ := by
  set L : ℝ := nu⁻¹ * m with hLdef
  have hnuinv : 1 ≤ nu⁻¹ := one_le_inv₀ hnu |>.2 hnu1
  have hL1 : 1 ≤ L := by rw [hLdef]; nlinarith only [hm, hnuinv]
  have hLpos : 0 < L := by linarith only [hL1]
  have hnL : nu⁻¹ ≤ L := by rw [hLdef]; nlinarith only [hm, hnuinv]
  have hmL : m ≤ L := by rw [hLdef]; nlinarith only [hm, hnuinv]
  have hσinvpos : 0 < σ⁻¹ := inv_pos.2 hσ
  have key : ∀ j e : ℕ, j + 190 ≤ e → L ^ j * (L ^ e)⁻¹ ≤ (L ^ 190)⁻¹ := by
    intro j e hje
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
      ← pow_add]
    exact pow_le_pow_right₀ hL1 hje
  have hsc : σ⁻¹ ≤ c * L := hσi.trans (mul_le_mul_of_nonneg_left hnL hc)
  have hA : nu * σ⁻¹ ≤ c * L := by
    refine le_trans ?_ hsc
    calc nu * σ⁻¹ ≤ 1 * σ⁻¹ := mul_le_mul_of_nonneg_right hnu1 hσinvpos.le
      _ = σ⁻¹ := one_mul _
  have hB : nu⁻¹ * σ ≤ (1 + c) * L ^ 2 := by
    calc nu⁻¹ * σ ≤ L * ((1 + c) * L) := mul_le_mul hnL hσu hσ.le hLpos.le
      _ = (1 + c) * L ^ 2 := by ring
  have hLL : L ≤ L ^ 2 := by nlinarith only [hL1]
  have ha0 : nu * σ⁻¹ + nu⁻¹ * σ ≤ (1 + 2 * c) * L ^ 2 := by
    nlinarith only [hA, hB, hLL, hc]
  have ha1 : nu⁻¹ * σ⁻¹ ≤ c * L ^ 2 := by
    calc nu⁻¹ * σ⁻¹ ≤ L * (c * L) := mul_le_mul hnL hsc hσinvpos.le hLpos.le
      _ = c * L ^ 2 := by ring
  have ha2 : nu * σ⁻¹ + nu⁻¹ * σ⁻¹ + nu⁻¹ * σ ≤ (1 + 3 * c) * L ^ 2 := by
    nlinarith only [hA, hB, ha1, hLL, hc]
  have hm1 : ((m : ℝ) + 1) ^ 2 ≤ 4 * L ^ 2 := by nlinarith only [hm, hmL]
  have hs4 : σ⁻¹ ^ 4 ≤ c ^ 4 * L ^ 4 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hσinvpos.le hsc 4
  have hθ : 0 ≤ ((L ^ 200)⁻¹) := by positivity
  have hθ' : (((L ^ 200)⁻¹)⁻¹) = L ^ 200 := inv_inv _
  have hn200 : 0 ≤ ((L ^ 400)⁻¹) := by positivity
  rw [hθ']
  -- the three terms
  have T1 : (nu * σ⁻¹ + nu⁻¹ * σ) * (L ^ 200)⁻¹ ≤ (1 + 2 * c) * (L ^ 190)⁻¹ := by
    calc _ ≤ ((1 + 2 * c) * L ^ 2) * (L ^ 200)⁻¹ := mul_le_mul_of_nonneg_right ha0 hθ
      _ = (1 + 2 * c) * (L ^ 2 * (L ^ 200)⁻¹) := by ring
      _ ≤ (1 + 2 * c) * (L ^ 190)⁻¹ :=
          mul_le_mul_of_nonneg_left (key 2 200 (by norm_num)) (by linarith only [hc])
  have T2 : nu⁻¹ * σ⁻¹ * (L ^ 200)⁻¹ * (kc * ((m : ℝ) + 1) ^ 2) ≤ 4 * c * kc * (L ^ 190)⁻¹ := by
    calc _ ≤ (c * L ^ 2) * (L ^ 200)⁻¹ * (kc * (4 * L ^ 2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right ha1 hθ) (mul_le_mul_of_nonneg_left hm1 hkc)
            (by positivity) (by positivity)
      _ = 4 * c * kc * (L ^ 4 * (L ^ 200)⁻¹) := by ring
      _ ≤ 4 * c * kc * (L ^ 190)⁻¹ :=
          mul_le_mul_of_nonneg_left (key 4 200 (by norm_num)) (by positivity)
  have T3 : (nu * σ⁻¹ + nu⁻¹ * σ⁻¹ + nu⁻¹ * σ) * L ^ 200 * (C5 * σ⁻¹ ^ 4 * (L ^ 400)⁻¹) ≤
      (1 + 3 * c) * c ^ 4 * C5 * (L ^ 190)⁻¹ := by
    calc _ ≤ ((1 + 3 * c) * L ^ 2) * L ^ 200 * (C5 * (c ^ 4 * L ^ 4) * (L ^ 400)⁻¹) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right ha2 (by positivity))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs4 hC5) hn200)
            (by positivity) (by positivity)
      _ = (1 + 3 * c) * c ^ 4 * C5 * (L ^ 206 * (L ^ 400)⁻¹) := by ring
      _ ≤ (1 + 3 * c) * c ^ 4 * C5 * (L ^ 190)⁻¹ :=
          mul_le_mul_of_nonneg_left (key 206 400 (by norm_num)) (by positivity)
  linarith only [T1, T2, T3]

theorem loc_subcubeAvg_affine {Kc n : ℕ} (hn : n ≤ Kc) (A0 A1 A2 : ℝ≥0∞)
    (X Y : TriadicCube d → ℝ≥0∞) :
    subcubeAvg Kc n (fun Q => A0 + (A1 * X Q + A2 * Y Q)) =
      A0 + (A1 * subcubeAvg Kc n X + A2 * subcubeAvg Kc n Y) := by
  rw [subcubeAvg_add, subcubeAvg_const hn, subcubeAvg_add, subcubeAvg_const_mul,
    subcubeAvg_const_mul]

end SuperdiffusionCLT.Section5
