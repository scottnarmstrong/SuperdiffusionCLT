/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Engine.AffineSlope
public import SuperdiffusionCLT.Section6.Engine.CubeNorms
public import SuperdiffusionCLT.Section6.Engine.Solutions

/-!
# Numerical helpers for the deterministic chain

The choice of the exponents `η`, `κ` from `γ`, of the block length `Hb`, of the single
smallness threshold `c`, and the top-scale bound `hVtop`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem ec5_params (γ : ℝ) (h0 : 0 < γ) (h1 : γ < 1) :
    ∃ η κ : ℝ, 1 / 2 ≤ η ∧ η < 1 ∧ 0 < κ ∧ κ ≤ 1 / 24 ∧ κ ≤ γ ∧ γ + 5 * κ < η ∧
      γ + 7 * κ ≤ η := by
  have m1 : min γ ((1 - γ) / 2) ≤ γ := min_le_left _ _
  have m2 : min γ ((1 - γ) / 2) ≤ (1 - γ) / 2 := min_le_right _ _
  have m3 : 0 < min γ ((1 - γ) / 2) := lt_min h0 (by linarith only [h1])
  refine ⟨(1 + γ) / 2, min γ ((1 - γ) / 2) / 14, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [m1, m2, m3, h0, h1]

theorem ec5_block_length (Cb κ : ℝ) (hCb : 1 ≤ Cb) (hκ : 0 < κ) (n : ℕ) :
    ∃ Hb : ℕ, n ≤ Hb ∧ 1 ≤ Hb ∧ Cb ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) := by
  refine ⟨max (max n 1) ⌈Real.logb 3 Cb / κ⌉₊, ?_, ?_, ?_⟩
  · exact le_trans (le_trans (le_max_left n 1) (le_max_left _ _)) (le_refl _)
  · exact le_trans (le_max_right n 1) (le_trans (le_max_left _ _) (le_refl _))
  · have h1 : Real.logb 3 Cb / κ ≤ ((max (max n 1) ⌈Real.logb 3 Cb / κ⌉₊ : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
    have h2 : Real.logb 3 Cb ≤ κ * ((max (max n 1) ⌈Real.logb 3 Cb / κ⌉₊ : ℕ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 hκ.le
      rwa [mul_div_cancel₀ _ hκ.ne'] at this
    calc Cb = (3 : ℝ) ^ (Real.logb 3 Cb) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by linarith only [hCb])).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2

theorem ec5_min_list (l : List ℝ) (h : ∀ x ∈ l, 0 < x) : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ l, c ≤ x := by
  induction l with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons x l ih =>
    obtain ⟨c, hc, hcl⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨min x c, lt_min (h x (by simp)) hc, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (hcl y hy)

theorem ec5_le_of_mul {δ c ci : ℝ} {Hb : ℕ} (h0 : 0 ≤ δ) (h : δ * ((Hb : ℝ) + 1) ≤ c)
    (hc : c ≤ ci) : δ ≤ ci := by
  have : (0 : ℝ) ≤ Hb := Nat.cast_nonneg _
  nlinarith only [h, hc, h0, this]

theorem ec5_K_le_half {δ c K : ℝ} {Hb : ℕ} (hK : 1 ≤ K)
    (h : δ * ((Hb : ℝ) + 1) ≤ c) (hc : c ≤ 1 / (2 * K)) : K * δ * ((Hb : ℝ) + 1) ≤ 1 / 2 := by
  have hK0 : 0 < K := by linarith only [hK]
  have h1 : K * (δ * ((Hb : ℝ) + 1)) ≤ K * (1 / (2 * K)) :=
    mul_le_mul_of_nonneg_left (le_trans h hc) hK0.le
  have h2 : K * (1 / (2 * K)) = 1 / 2 := by field_simp
  nlinarith only [h1, h2]

theorem ec5_K_le_half' {δ c K : ℝ} {Hb : ℕ} (hK : 1 ≤ K) (h0 : 0 ≤ δ)
    (h : δ * ((Hb : ℝ) + 1) ≤ c) (hc : c ≤ 1 / (2 * K)) : K * δ ≤ 1 / 2 := by
  have h1 := ec5_K_le_half hK h hc
  have : (1 : ℝ) ≤ (Hb : ℝ) + 1 := by
    have : (0 : ℝ) ≤ Hb := Nat.cast_nonneg _
    linarith only [this]
  have hKd : 0 ≤ K * δ := mul_nonneg (by linarith only [hK]) h0
  nlinarith only [h1, this, hKd]

theorem ec5_top [NeZero d] {a : CoeffField d} {Cin : ℝ} {j : ℕ} {Vj : Vec d →ₗ[ℝ] (Vec d → ℝ)}
    {dj : ℝ} (hdj1 : dj ≤ 1 / 2) (hCin : 1 ≤ Cin)
    (hsol : ∀ e : Vec d, ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (Vj e) g)
    (hflat : ∀ e : Vec d, cubeFlat j (fun x => Vj e x - vecDot e x) ≤ Cin * dj * engNorm e)
    (e : Vec d) : cubeFlat j (Vj e) ≤ Cin * engNorm e := by
  have hV : MemLp (Vj e) 2 (normalizedCubeMeasure (originCube d (j : ℤ))) :=
    (hsol e).elim fun g hg => hg.memLp.1
  have hl := e0c_memLp j (e0c_continuous_vecDot e)
  have hVl : MemLp (fun x => Vj e x - vecDot e x) 2
      (normalizedCubeMeasure (originCube d (j : ℤ))) := hV.sub hl
  have h1 := cubeFlat_add_le hl hVl
  have e1 : (fun x => vecDot e x + (Vj e x - vecDot e x)) = Vj e := by funext x; ring
  rw [e1, cubeFlat_vecDot] at h1
  have h3 : (2 : ℝ) ≤ 2 * Real.sqrt 3 := by
    have := Real.one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 3)
    linarith only [this]
  have hn := engNorm_nonneg e
  have h4 : engNorm e / (2 * Real.sqrt 3) ≤ engNorm e / 2 :=
    div_le_div_of_nonneg_left hn (by norm_num) h3
  have h5 := hflat e
  have h6 : Cin * dj * engNorm e ≤ Cin * (1 / 2) * engNorm e := by
    have := mul_le_mul_of_nonneg_left hdj1 (by linarith only [hCin] : 0 ≤ Cin)
    nlinarith only [this, hn]
  nlinarith only [h1, h4, h5, h6, hn, hCin]

end SuperdiffusionCLT.Section6
