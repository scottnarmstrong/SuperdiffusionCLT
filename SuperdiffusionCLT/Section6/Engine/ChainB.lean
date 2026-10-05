/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Chain

/-!
# The chain: a block of scales (growth bookkeeping and the descent from `j = k + Hb`)
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

theorem eb5a_exp_le_rpow {x : ℝ} (hx : 0 ≤ x) : Real.exp x ≤ (3 : ℝ) ^ x := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h1 : (1 : ℝ) ≤ Real.log 3 := by
    have := Real.exp_one_lt_d9
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by simp]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith only [this])
  exact Real.exp_le_exp.2 (by nlinarith only [h1, hx])

theorem eb5a_growth {θ N x : ℝ} (hθ : 0 ≤ θ) (hN : 0 ≤ N) (h : 2 * θ + N ≤ x) :
    (1 + θ) * (1 + N) ≤ (3 : ℝ) ^ x ∧ (1 + 2 * θ) * (1 + N) ≤ (3 : ℝ) ^ x := by
  have hx : 0 ≤ x := by linarith only [hθ, hN, h]
  have hexp := eb5a_exp_le_rpow hx
  have h1 : 1 + θ ≤ Real.exp θ := by linarith only [Real.add_one_le_exp θ]
  have h2 : 1 + 2 * θ ≤ Real.exp (2 * θ) := by linarith only [Real.add_one_le_exp (2 * θ)]
  have h3 : 1 + N ≤ Real.exp N := by linarith only [Real.add_one_le_exp N]
  have h4 : Real.exp (2 * θ + N) ≤ Real.exp x := Real.exp_le_exp.2 h
  have h5 : Real.exp (θ + N) ≤ Real.exp x := Real.exp_le_exp.2 (by linarith only [h, hθ])
  refine ⟨?_, ?_⟩
  · calc (1 + θ) * (1 + N) ≤ Real.exp θ * Real.exp N :=
          mul_le_mul h1 h3 (by linarith only [hN]) (Real.exp_pos _).le
      _ = Real.exp (θ + N) := (Real.exp_add _ _).symm
      _ ≤ _ := h5.trans hexp
  · calc (1 + 2 * θ) * (1 + N) ≤ Real.exp (2 * θ) * Real.exp N :=
          mul_le_mul h2 h3 (by linarith only [hN]) (Real.exp_pos _).le
      _ = Real.exp (2 * θ + N) := (Real.exp_add _ _).symm
      _ ≤ _ := h4.trans hexp

/-- The block gain is eventually at most `1 / 8` after the constant `C5`. -/
theorem eb5a_exists_H0 (C5 : ℝ) (hC5 : 1 ≤ C5) :
    ∃ H0 : ℕ, 1 ≤ H0 ∧ ∀ Hb : ℕ, H0 ≤ Hb →
      C5 * (3 : ℝ) ^ (-((1 : ℝ) / 2 * (Hb : ℝ))) ≤ 1 / 8 := by
  set y : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ)) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
  have hy1 : y < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (8 * C5) by positivity) hy1
  refine ⟨max n 1, le_max_right _ _, fun Hb hHb => ?_⟩
  have hpow : (3 : ℝ) ^ (-((1 : ℝ) / 2 * (Hb : ℝ))) = y ^ Hb := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [hpow]
  have h1 : y ^ Hb ≤ y ^ n := pow_le_pow_of_le_one hy0.le hy1.le ((le_max_left _ _).trans hHb)
  have h2 : y ^ Hb < 1 / (8 * C5) := lt_of_le_of_lt h1 hn
  have hC : 0 < C5 := by linarith only [hC5]
  rw [lt_div_iff₀ (by positivity)] at h2
  linarith only [h2]

/-- Descent over one block: from a good `q` at scale `k + Hb` to a good `q'` at scale `k`. -/
theorem eb5a_down [NeZero d] {K C5 η κ : ℝ} (hK : 1 ≤ K) (hC5 : 1 ≤ C5) (hη : 1 / 2 ≤ η)
    (hκ : 0 < κ) {a : CoeffField d} {δ : ℕ → ℝ} {Hb mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} (hH : 1 ≤ Hb)
    (hHblk : C5 * (3 : ℝ) ^ (-((1 : ℝ) / 2 * (Hb : ℝ))) ≤ 1 / 8)
    (hδ : ∀ j : ℕ, mstar ≤ j →
      0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ 1 / (256 * K * C5) ∧ δ j ≤ 1 / (256 * K * C5) * κ)
    (hanti : ∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hflat : ∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤ K * δ j * engNorm e ∧
        engNorm (affSlope k (V j e) - e) ≤ K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e)
    (hblock : ∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
      ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
        ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
          ∀ k : ℕ, l ≤ k → k ≤ j →
            cubeFlat k (fun x => w x - V j e x) ≤
              C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w)
    {m k : ℕ} (hk : mstar ≤ k) (hkm : k + Hb ≤ m) (e q : Vec d)
    (hq : cubeFlat (k + Hb) (fun x => V m e x - V (k + Hb) q x) ≤
      6 * K * δ (k + Hb) * engNorm q) :
    ∃ q' : Vec d, affSlope k (V k q') = affSlope k (V m e) ∧
      cubeFlat k (fun x => V m e x - V k q' x) ≤ 6 * K * δ k * engNorm q' ∧
      engNorm q' ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) * engNorm q ∧
      engNorm q ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) * engNorm q' := by
  have hK0 : 0 < K := by linarith only [hK]
  have hC0 : 0 < C5 := by linarith only [hC5]
  set c2 : ℝ := 1 / (256 * K * C5) with hc2
  have hc2p : 0 < c2 := by positivity
  have hKC : 256 * K * C5 * c2 = 1 := by rw [hc2]; field_simp
  set j := k + Hb with hj
  have hjm : mstar ≤ j := by omega
  have hHb1 : (1 : ℝ) ≤ (Hb : ℝ) + 1 := by linarith only [(Nat.cast_nonneg Hb : (0 : ℝ) ≤ Hb)]
  have hHbr : (1 : ℝ) ≤ (Hb : ℝ) := by exact_mod_cast hH
  obtain ⟨hδk0, hδk1, hδk2⟩ := hδ k hk
  obtain ⟨hδj0, hδj1, hδj2⟩ := hδ j hjm
  have hmono : δ j ≤ δ k := hanti k j hk (by omega)
  -- the solution `ρ = V m e - V j q` and its block decomposition
  obtain ⟨g1, hg1⟩ := hVsol m (by omega) e
  obtain ⟨g2, hg2⟩ := hVsol j hjm q
  have hρ : IsSolOn a (engCube d j) (fun x => V m e x - V j q x) _ :=
    IsSolOn.sub (hell j) (eb5a_sol_restrict hell (by omega) hg1) hg2
  obtain ⟨p, hp1, hp2⟩ := hblock j k hjm (by omega) (by omega) _ ⟨_, hρ⟩
  have hp3 := hp2 k le_rfl (by omega)
  obtain ⟨g3, hg3⟩ := hVsol j hjm p
  have hRsol : IsSolOn a (engCube d j) (fun x => V m e x - V j q x - V j p x) _ :=
    IsSolOn.sub (hell j) hρ hg3
  have hρ0 : 0 ≤ cubeFlat j (fun x => V m e x - V j q x) := cubeFlat_nonneg _ _
  have hqn := engNorm_nonneg q
  have hpn := engNorm_nonneg p
  -- numerical facts
  set θ := 6 * K * C5 * δ j with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 6 * κ / 256 := by
    have h1 : 6 * K * C5 * δ j ≤ 6 * K * C5 * (c2 * κ) :=
      mul_le_mul_of_nonneg_left hδj2 (by positivity)
    have h2 : 6 * K * C5 * (c2 * κ) = 6 * κ / 256 := by
      have : K * C5 * c2 = 1 / 256 := by linarith only [hKC]
      linear_combination (6 * κ) * this
    linarith only [h1, h2]
  have hθ4 : θ ≤ 1 / 16 := by
    have h1 : 6 * K * C5 * δ j ≤ 6 * K * C5 * c2 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc δ j = δ j * 1 := by ring
        _ ≤ δ j * ((Hb : ℝ) + 1) := mul_le_mul_of_nonneg_left hHb1 hδj0
        _ ≤ c2 := hδj1
    have h2 : 6 * K * C5 * c2 = 6 / 256 := by
      have : K * C5 * c2 = 1 / 256 := by linarith only [hKC]
      linear_combination 6 * this
    linarith only [h1, h2]
  have hpθ : engNorm p ≤ θ * engNorm q := by
    have h1 : C5 * cubeFlat j (fun x => V m e x - V j q x) ≤ C5 * (6 * K * δ j * engNorm q) :=
      mul_le_mul_of_nonneg_left hq hC0.le
    have h2 : C5 * (6 * K * δ j * engNorm q) = θ * engNorm q := by rw [hθ]; ring
    linarith only [hp1, h1, h2]
  have hrq : engNorm q ≤ (1 + 2 * θ) * engNorm (q + p) := by
    have h1 := eb5a_engNorm_le_sub_add q (-p)
    have h2 : engNorm (q - -p) = engNorm (q + p) := by rw [sub_neg_eq_add]
    rw [h2, eb5a_engNorm_neg] at h1
    have h3 : (1 - θ) * engNorm q ≤ engNorm (q + p) := by linarith only [h1, hpθ]
    have h4 : (1 + 2 * θ) * ((1 - θ) * engNorm q) ≤ (1 + 2 * θ) * engNorm (q + p) :=
      mul_le_mul_of_nonneg_left h3 (by linarith only [hθ0])
    have h5 : 0 ≤ engNorm q * (θ * (1 - 2 * θ)) :=
      mul_nonneg hqn (mul_nonneg hθ0 (by linarith only [hθ4]))
    nlinarith only [h4, h5]
  have hrq' : engNorm (q + p) ≤ (1 + θ) * engNorm q := by
    have h1 := engNorm_add_le q p
    linarith only [h1, hpθ]
  have hq43 : engNorm q ≤ 2 * engNorm (q + p) := by
    nlinarith only [hrq, hθ4, hθ0, engNorm_nonneg (q + p)]
  -- the remainder
  have hjk : (j : ℝ) - (k : ℝ) = (Hb : ℝ) := by rw [hj]; push_cast; ring
  have hexp : (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2 * (Hb : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [hjk]
    nlinarith only [hη, hHbr]
  have hRflat : cubeFlat k (fun x => V m e x - V j q x - V j p x) ≤
      1 / 8 * cubeFlat j (fun x => V m e x - V j q x) := by
    refine hp3.trans ?_
    have h1 : C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) ≤ 1 / 8 :=
      (mul_le_mul_of_nonneg_left hexp hC0.le).trans hHblk
    exact mul_le_mul_of_nonneg_right h1 hρ0
  have hmem : ∀ i, mstar ≤ i → k ≤ i → ∀ e' : Vec d,
      MemLp (V i e') 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := fun i hi hki e' =>
    (hVsol i hi e').elim fun g hg => eb5a_memLp hell hki hg
  have hKδ : 0 ≤ K * δ k := mul_nonneg hK0.le hδk0
  have hflat_lj := hflat j k hjm (by omega) le_rfl
  have hflat_ll := hflat k k hk le_rfl (by omega)
  have hr1 : cubeFlat k (fun x => V m e x - V j q x - V j p x) ≤
      3 / 2 * K * δ k * engNorm (q + p) := by
    refine hRflat.trans ?_
    have h1 : 1 / 8 * cubeFlat j (fun x => V m e x - V j q x) ≤
        1 / 8 * (6 * K * δ j * engNorm q) := by linarith only [hq]
    have h2 : K * δ j * engNorm q ≤ K * δ k * engNorm q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hK0.le) hqn
    have h3 : K * δ k * engNorm q ≤ K * δ k * (2 * engNorm (q + p)) :=
      mul_le_mul_of_nonneg_left hq43 hKδ
    nlinarith only [h1, h2, h3]
  have hN64 : 64 * K * δ k * ((Hb : ℝ) + 1) ≤ 1 := by
    have h1 : K * (δ k * ((Hb : ℝ) + 1)) ≤ K * c2 := mul_le_mul_of_nonneg_left hδk1 hK0.le
    have h2 : K * c2 * C5 ≤ 1 / 256 := by linarith only [hKC]
    have h3 : K * c2 ≤ 1 / 256 := by
      have : K * c2 * 1 ≤ K * c2 * C5 := mul_le_mul_of_nonneg_left hC5 (by positivity)
      linarith only [this, h2]
    nlinarith only [h1, h3]
  obtain ⟨q', hq1, hq2, hq3, hq4⟩ := eb5a_step K hK δ Hb k j V (by omega) le_rfl hδk0 hmono hN64
    (hmem k hk le_rfl) (hmem j hjm (by omega)) hflat_lj hflat_ll (V m e)
    (fun x => V m e x - V j q x - V j p x) (q + p)
    (fun x => by rw [map_add]; simp only [Pi.add_apply]; ring)
    (eb5a_memLp hell (by omega) hRsol) hr1
  refine ⟨q', hq1, hq2, ?_, ?_⟩
  · have hN := eb5a_growth hθ0 (by positivity : 0 ≤ 32 * (K * δ k * ((Hb : ℝ) + 1)))
      (x := κ * Hb) (by
        have h1 : K * δ k * ((Hb : ℝ) + 1) ≤ K * (c2 * κ) * ((Hb : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδk2 hK0.le) (by positivity)
        have h2 : K * c2 ≤ 1 / 256 := by
          have : K * c2 * 1 ≤ K * c2 * C5 := mul_le_mul_of_nonneg_left hC5 (by positivity)
          have h3 : K * c2 * C5 ≤ 1 / 256 := by linarith only [hKC]
          linarith only [this, h3]
        have h3 : K * (c2 * κ) * ((Hb : ℝ) + 1) ≤ 1 / 256 * κ * ((Hb : ℝ) + 1) := by
          have : K * (c2 * κ) = (K * c2) * κ := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hκ.le) (by positivity)
        nlinarith only [h1, h3, hθ1, hκ, hHbr])
    calc engNorm q' ≤ (1 + 32 * (K * δ k * ((Hb : ℝ) + 1))) * engNorm (q + p) := hq3
      _ ≤ (1 + 32 * (K * δ k * ((Hb : ℝ) + 1))) * ((1 + θ) * engNorm q) :=
          mul_le_mul_of_nonneg_left hrq' (by positivity)
      _ = ((1 + θ) * (1 + 32 * (K * δ k * ((Hb : ℝ) + 1)))) * engNorm q := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.1 hqn
  · have hN := eb5a_growth hθ0 (by positivity : 0 ≤ 32 * (K * δ k * ((Hb : ℝ) + 1)))
      (x := κ * Hb) (by
        have h1 : K * δ k * ((Hb : ℝ) + 1) ≤ K * (c2 * κ) * ((Hb : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδk2 hK0.le) (by positivity)
        have h2 : K * c2 ≤ 1 / 256 := by
          have : K * c2 * 1 ≤ K * c2 * C5 := mul_le_mul_of_nonneg_left hC5 (by positivity)
          have h3 : K * c2 * C5 ≤ 1 / 256 := by linarith only [hKC]
          linarith only [this, h3]
        have h3 : K * (c2 * κ) * ((Hb : ℝ) + 1) ≤ 1 / 256 * κ * ((Hb : ℝ) + 1) := by
          have : K * (c2 * κ) = (K * c2) * κ := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hκ.le) (by positivity)
        nlinarith only [h1, h3, hθ1, hκ, hHbr])
    have hq'n := engNorm_nonneg q'
    calc engNorm q ≤ (1 + 2 * θ) * engNorm (q + p) := hrq
      _ ≤ (1 + 2 * θ) * ((1 + 32 * (K * δ k * ((Hb : ℝ) + 1))) * engNorm q') :=
          mul_le_mul_of_nonneg_left hq4 (by positivity)
      _ = ((1 + 2 * θ) * (1 + 32 * (K * δ k * ((Hb : ℝ) + 1)))) * engNorm q' := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hN.2 hq'n

theorem eb5a_Kc2 {K C5 : ℝ} (hK : 1 ≤ K) (hC5 : 1 ≤ C5) :
    K * (1 / (256 * K * C5)) ≤ 1 / 256 := by
  have hK0 : 0 < K := by linarith only [hK]
  have hC0 : 0 < C5 := by linarith only [hC5]
  have h : K * (1 / (256 * K * C5)) = 1 / (256 * C5) := by field_simp
  rw [h]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hC5]

theorem eb5a_flat_zero [NeZero d] (n : ℕ) : cubeFlat n (fun _ : Vec d => (0 : ℝ)) = 0 := by
  have h := cubeFlat_const_mul (d := d) n 0 (fun _ => (0 : ℝ))
  simpa using h

/-- The top step: from `V m e` to a good `q` at a scale `k` with `m ≤ k + Hb`. -/
theorem eb5a_top [NeZero d] {K C5 : ℝ} (hK : 1 ≤ K) (hC5 : 1 ≤ C5)
    {a : CoeffField d} {δ : ℕ → ℝ} {Hb mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)}
    (hδ : ∀ j : ℕ, mstar ≤ j → 0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ 1 / (256 * K * C5))
    (hanti : ∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hflat : ∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤ K * δ j * engNorm e ∧
        engNorm (affSlope k (V j e) - e) ≤ K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e)
    {m k : ℕ} (hk : mstar ≤ k) (hkm : k ≤ m) (hmk : m ≤ k + Hb) (e : Vec d) :
    ∃ q : Vec d, affSlope k (V k q) = affSlope k (V m e) ∧
      cubeFlat k (fun x => V m e x - V k q x) ≤ 6 * K * δ k * engNorm q ∧
      engNorm q ≤ 2 * engNorm e ∧ engNorm e ≤ 2 * engNorm q := by
  have hK0 : 0 < K := by linarith only [hK]
  have hHb1 : (1 : ℝ) ≤ (Hb : ℝ) + 1 := by linarith only [(Nat.cast_nonneg Hb : (0 : ℝ) ≤ Hb)]
  obtain ⟨hδk0, hδk1⟩ := hδ k hk
  have hmono : δ m ≤ δ k := hanti k m hk hkm
  have hKc := eb5a_Kc2 hK hC5
  have hmem : ∀ i, mstar ≤ i → k ≤ i → ∀ e' : Vec d,
      MemLp (V i e') 2 (normalizedCubeMeasure (originCube d (k : ℤ))) := fun i hi hki e' =>
    (hVsol i hi e').elim fun g hg => eb5a_memLp hell hki hg
  have hN64 : 64 * K * δ k * ((Hb : ℝ) + 1) ≤ 1 := by
    have h1 : K * (δ k * ((Hb : ℝ) + 1)) ≤ K * (1 / (256 * K * C5)) :=
      mul_le_mul_of_nonneg_left hδk1 hK0.le
    nlinarith only [h1, hKc]
  have hKδ : K * δ k * ((Hb : ℝ) + 1) ≤ 1 / 256 := by
    have h1 : K * (δ k * ((Hb : ℝ) + 1)) ≤ K * (1 / (256 * K * C5)) :=
      mul_le_mul_of_nonneg_left hδk1 hK0.le
    nlinarith only [h1, hKc]
  have hen := engNorm_nonneg e
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := eb5a_step K hK δ Hb k m V hkm hmk hδk0 hmono hN64
    (hmem k hk le_rfl) (hmem m (by omega) hkm) (hflat m k (by omega) hkm hmk)
    (hflat k k hk le_rfl (by omega)) (V m e) (fun _ => 0) e (fun x => by ring)
    (MeasureTheory.MemLp.zero) (by
      rw [eb5a_flat_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0.le) hδk0) hen)
  refine ⟨q, hq1, hq2, ?_, ?_⟩
  · nlinarith only [hq3, hKδ, hen]
  · nlinarith only [hq4, hKδ, engNorm_nonneg q]

/-- Every scale `k` in `[mstar, m]` has a good `q`, by descent in blocks from the top. -/
theorem eb5a_good [NeZero d] {K C5 η κ : ℝ} (hK : 1 ≤ K) (hC5 : 1 ≤ C5) (hη : 1 / 2 ≤ η)
    (hκ : 0 < κ) {a : CoeffField d} {δ : ℕ → ℝ} {Hb mstar : ℕ}
    {V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)} (hH : 1 ≤ Hb)
    (hHblk : C5 * (3 : ℝ) ^ (-((1 : ℝ) / 2 * (Hb : ℝ))) ≤ 1 / 8)
    (hδ : ∀ j : ℕ, mstar ≤ j →
      0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ 1 / (256 * K * C5) ∧ δ j ≤ 1 / (256 * K * C5) * κ)
    (hanti : ∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a)
    (hVsol : ∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
      ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g)
    (hflat : ∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
      cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤ K * δ j * engNorm e ∧
        engNorm (affSlope k (V j e) - e) ≤ K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e)
    (hblock : ∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
      ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
        ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
          ∀ k : ℕ, l ≤ k → k ≤ j →
            cubeFlat k (fun x => w x - V j e x) ≤
              C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w)
    (m : ℕ) (e : Vec d) :
    ∀ n k : ℕ, mstar ≤ k → k ≤ m → m - k = n →
      ∃ q : Vec d, affSlope k (V k q) = affSlope k (V m e) ∧
        cubeFlat k (fun x => V m e x - V k q x) ≤ 6 * K * δ k * engNorm q ∧
        engNorm q ≤ 2 * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
        engNorm e ≤ 2 * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk hkm hn
    have hG : (1 : ℝ) ≤ (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) := by
      refine Real.one_le_rpow (by norm_num) (mul_nonneg hκ.le ?_)
      have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
      linarith only [this]
    by_cases hcase : m ≤ k + Hb
    · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := eb5a_top hK hC5
        (fun j hj => ⟨(hδ j hj).1, (hδ j hj).2.1⟩) hanti hell hVsol hflat hk hkm hcase e
      refine ⟨q, hq1, hq2, ?_, ?_⟩
      · nlinarith only [hq3, hG, engNorm_nonneg e]
      · nlinarith only [hq4, hG, engNorm_nonneg q]
    · have hlt : k + Hb < m := by omega
      obtain ⟨q0, -, hq0f, hq0a, hq0b⟩ :=
        ih (m - (k + Hb)) (by omega) (k + Hb) (by omega) (by omega) rfl
      obtain ⟨q', hq1, hq2, hq3, hq4⟩ := eb5a_down hK hC5 hη hκ hH hHblk hδ hanti hell hVsol
        hflat hblock hk (by omega) e q0 hq0f
      have hsplit : (3 : ℝ) ^ (κ * (Hb : ℝ)) *
          (3 : ℝ) ^ (κ * ((m : ℝ) - ((k + Hb : ℕ) : ℝ))) =
          (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        push_cast
        ring
      have hG1 : 0 ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) := by positivity
      refine ⟨q', hq1, hq2, ?_, ?_⟩
      · calc engNorm q' ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) * engNorm q0 := hq3
          _ ≤ (3 : ℝ) ^ (κ * (Hb : ℝ)) *
              (2 * (3 : ℝ) ^ (κ * ((m : ℝ) - ((k + Hb : ℕ) : ℝ))) * engNorm e) :=
            mul_le_mul_of_nonneg_left hq0a hG1
          _ = 2 * ((3 : ℝ) ^ (κ * (Hb : ℝ)) *
              (3 : ℝ) ^ (κ * ((m : ℝ) - ((k + Hb : ℕ) : ℝ)))) * engNorm e := by ring
          _ = _ := by rw [hsplit]
      · calc engNorm e ≤ 2 * (3 : ℝ) ^ (κ * ((m : ℝ) - ((k + Hb : ℕ) : ℝ))) * engNorm q0 := hq0b
          _ ≤ 2 * (3 : ℝ) ^ (κ * ((m : ℝ) - ((k + Hb : ℕ) : ℝ))) *
              ((3 : ℝ) ^ (κ * (Hb : ℝ)) * engNorm q') :=
            mul_le_mul_of_nonneg_left hq4 (by positivity)
          _ = 2 * ((3 : ℝ) ^ (κ * (Hb : ℝ)) *
              (3 : ℝ) ^ (κ * ((m : ℝ) - ((k + Hb : ℕ) : ℝ)))) * engNorm q' := by ring
          _ = _ := by rw [hsplit]

/-- **E-B5a (chain: a top-scale corrected affine is, at every lower scale, close to a local
corrected affine)**. Replaces `e.sharp.Cone.down.scales`. -/
theorem eng_chain (d : ℕ) [NeZero d] (K C5 : ℝ) (hK : 1 ≤ K) (hC5 : 1 ≤ C5) :
    ∃ (Cc c2 : ℝ) (H0 : ℕ), 1 ≤ Cc ∧ 0 < c2 ∧
      ∀ η κ : ℝ, 1 / 2 ≤ η → η < 1 → 0 < κ → κ ≤ 1 →
        ∀ (a : CoeffField d) (δ : ℕ → ℝ) (Hb mstar : ℕ)
          (V : ℕ → Vec d →ₗ[ℝ] (Vec d → ℝ)),
          H0 ≤ Hb → Hb + 3 ≤ mstar →
          (∀ j : ℕ, mstar ≤ j →
            0 ≤ δ j ∧ δ j * ((Hb : ℝ) + 1) ≤ c2 ∧ δ j ≤ c2 * κ) →
          (∀ i j : ℕ, mstar ≤ i → i ≤ j → δ j ≤ δ i) →
          -- hell
          (∀ n : ℕ, ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (engCube d n) a) →
          -- hVsol
          (∀ j : ℕ, mstar ≤ j → ∀ e : Vec d,
            ∃ g : Vec d → Vec d, IsSolOn a (engCube d j) (V j e) g) →
          -- hflat K
          (∀ j k : ℕ, mstar ≤ j → k ≤ j → j ≤ k + Hb → ∀ e : Vec d,
            cubeFlat k (fun x => V j e x - vecDot (affSlope k (V j e)) x) ≤
                K * δ j * engNorm e ∧
              engNorm (affSlope k (V j e) - e) ≤
                K * δ j * ((j : ℝ) - (k : ℝ) + 1) * engNorm e) →
          -- hblock C5 η
          (∀ j l : ℕ, mstar ≤ j → l ≤ j → j ≤ l + Hb →
            ∀ w : Vec d → ℝ, (∃ g : Vec d → Vec d, IsSolOn a (engCube d j) w g) →
              ∃ e : Vec d, engNorm e ≤ C5 * cubeFlat j w ∧
                ∀ k : ℕ, l ≤ k → k ≤ j →
                  cubeFlat k (fun x => w x - V j e x) ≤
                    C5 * (3 : ℝ) ^ (-(η * ((j : ℝ) - (k : ℝ)))) * cubeFlat j w) →
          -- conclusion: hchain Cc κ
          ∀ m k : ℕ, mstar ≤ k → k ≤ m →
            (∀ e : Vec d, ∃ q : Vec d,
              affSlope k (V k q) = affSlope k (V m e) ∧
                cubeFlat k (fun x => V m e x - V k q x) ≤ Cc * δ k * engNorm q ∧
                engNorm q ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm e ∧
                engNorm e ≤ Cc * (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) * engNorm q) ∧
              ∀ q : Vec d, ∃ e : Vec d, affSlope k (V m e) = affSlope k (V k q) := by
  have hK0 : 0 < K := by linarith only [hK]
  have hC0 : 0 < C5 := by linarith only [hC5]
  obtain ⟨H0, hH01, hH0⟩ := eb5a_exists_H0 C5 hC5
  refine ⟨6 * K, 1 / (256 * K * C5), H0, by linarith only [hK], by positivity, ?_⟩
  intro η κ hη1 hη2 hκ hκ1 a δ Hb mstar V hHb hm hδ hanti hell hVsol hflat hblock m k hk hkm
  have hH1 : 1 ≤ Hb := le_trans hH01 hHb
  have hHblk := hH0 Hb hHb
  have hgood := eb5a_good hK hC5 hη1 hκ hH1 hHblk hδ hanti hell hVsol hflat hblock m
  have hKc := eb5a_Kc2 hK hC5
  set G : ℝ := (3 : ℝ) ^ (κ * ((m : ℝ) - (k : ℝ))) with hGdef
  have hG0 : 0 < G := by positivity
  have hHb1 : (1 : ℝ) ≤ (Hb : ℝ) + 1 := by linarith only [(Nat.cast_nonneg Hb : (0 : ℝ) ≤ Hb)]
  obtain ⟨hδk0, hδk1, -⟩ := hδ k hk
  have hKδ : K * δ k ≤ 1 / 2 := by
    have h1 : K * δ k ≤ K * (δ k * ((Hb : ℝ) + 1)) := by
      calc K * δ k = K * (δ k * 1) := by ring
        _ ≤ K * (δ k * ((Hb : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHb1 hδk0) hK0.le
    have h2 : K * (δ k * ((Hb : ℝ) + 1)) ≤ K * (1 / (256 * K * C5)) :=
      mul_le_mul_of_nonneg_left hδk1 hK0.le
    linarith only [h1, h2, hKc]
  have hone : ∀ q : Vec d, engNorm q ≤ 2 * engNorm (affSlope k (V k q)) := by
    intro q
    have h1 := (hflat k k hk le_rfl (by omega) q).2
    simp only [sub_self, zero_add, mul_one] at h1
    have h2 := eb5a_engNorm_le_sub_add q (affSlope k (V k q))
    rw [eb5a_engNorm_sub_comm] at h2
    have h3 : K * δ k * engNorm q ≤ 1 / 2 * engNorm q :=
      mul_le_mul_of_nonneg_right hKδ (engNorm_nonneg q)
    linarith only [h1, h2, h3]
  have hmemm : ∀ e : Vec d, MemLp (V m e) 2 (normalizedCubeMeasure (originCube d (k : ℤ))) :=
    fun e => (hVsol m (by omega) e).elim fun g hg => eb5a_memLp hell hkm hg
  obtain ⟨T, hT⟩ := eb5a_exists_slopeMap k (V m) hmemm
  have hlow : ∀ e : Vec d, 1 / (4 * G) * engNorm e ≤ engNorm (T e) := by
    intro e
    obtain ⟨q, hq1, -, -, hq4⟩ := hgood e (m - k) k hk hkm rfl
    have h1 : T e = affSlope k (V k q) := by rw [hT e, hq1]
    have h2 := hone q
    rw [← h1] at h2
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith only [hq4, h2, hG0, engNorm_nonneg q]
  have hbij := engNorm_bijective_of_lower T (by positivity : 0 < 1 / (4 * G)) hlow
  refine ⟨fun e => ?_, fun q => ?_⟩
  · obtain ⟨q, hq1, hq2, hq3, hq4⟩ := hgood e (m - k) k hk hkm rfl
    refine ⟨q, hq1, hq2, ?_, ?_⟩
    · nlinarith only [hq3, mul_nonneg (mul_nonneg (by linarith only [hK] : (0 : ℝ) ≤ 6 * K - 2) hG0.le)
        (engNorm_nonneg e)]
    · nlinarith only [hq4, mul_nonneg (mul_nonneg (by linarith only [hK] : (0 : ℝ) ≤ 6 * K - 2) hG0.le)
        (engNorm_nonneg q)]
  · obtain ⟨e, he⟩ := hbij.2 (affSlope k (V k q))
    exact ⟨e, by rw [← hT e]; exact he⟩

/-- The numerical hypotheses of `eng_chain` are satisfiable (`δ = 0`, `Hb = H0`). -/
example (c2 κ : ℝ) (hc2 : 0 < c2) (hκ : 0 < κ) (Hb mstar : ℕ) :
    (∀ j : ℕ, mstar ≤ j → 0 ≤ (fun _ : ℕ => (0 : ℝ)) j ∧
      (fun _ : ℕ => (0 : ℝ)) j * ((Hb : ℝ) + 1) ≤ c2 ∧
      (fun _ : ℕ => (0 : ℝ)) j ≤ c2 * κ) ∧
    (∀ i j : ℕ, mstar ≤ i → i ≤ j → (fun _ : ℕ => (0 : ℝ)) j ≤ (fun _ : ℕ => (0 : ℝ)) i) :=
  ⟨fun _ _ => ⟨le_rfl, by simpa using hc2.le, by positivity⟩, fun _ _ _ _ => le_rfl⟩

end SuperdiffusionCLT.Section6
