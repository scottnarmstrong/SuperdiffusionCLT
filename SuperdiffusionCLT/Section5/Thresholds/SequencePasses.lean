/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Thresholds.ThresholdChain
public import SuperdiffusionCLT.Section5.Thresholds.IterationTelescope

/-!
# Steps 1-6 of the proof of `t.sstar.sharp.bounds` for an abstract real sequence

`s` stands for `shom_·`, `c₃ = c⋆ log 3`, `Λ n = log² n + κ`. Every threshold is produced before the
sequence `s` (it depends on `A`, `κ`, `c⋆` and the constants only).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

theorem one_lt_log_three : 1 < Real.log 3 := by
  have := Real.exp_one_lt_d9
  rw [Real.lt_log_iff_exp_lt (by norm_num)]; linarith only [this]

theorem log_three_le : Real.log 3 ≤ 3 / 2 := by
  have he := Real.exp_one_gt_d9
  have h1 : Real.log (3 / Real.exp 1) ≤ 3 / Real.exp 1 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h1
  have h2 : 3 / Real.exp 1 ≤ 3 / 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num); linarith only [he]
  linarith only [h1, h2]

theorem one_le_log_nat {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.log_le_log (by norm_num) hn3
  linarith only [this, one_lt_log_three]

theorem half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have h2 := Nat.lt_floor_add_one x
  have h3 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
  linarith only [h2, h3]

/-- Step 1: the square-increment estimate at one `(n, h)`. -/
theorem sq_increment_step (Cr cStar K : ℝ) (hCr : 0 ≤ Cr) (hc : 0 < cStar) (hc2 : cStar ≤ 2)
    (hK : 0 ≤ K) (s : ℕ → ℝ) (n h : ℕ) (hn3 : 3 ≤ n) (hs1 : 1 ≤ s n)
    (hΛs : Real.log (n : ℝ) ^ 2 + K ≤ s n ^ 2) (hhs : (h : ℝ) ≤ s n)
    (hrec : 1 ≤ h → |s (n + h) - s n - cStar * Real.log 3 * (s n)⁻¹ * (h : ℝ)| ≤
      Cr * (Real.log (n : ℝ) ^ 2 + K) * (s n)⁻¹) :
    |s (n + h) ^ 2 - s n ^ 2 - 2 * (cStar * Real.log 3) * (h : ℝ)| ≤
      (9 + 8 * Cr + Cr ^ 2) * (Real.log (n : ℝ) ^ 2 + K) := by
  have hu1 := one_le_log_nat hn3
  have hΛ1 : 1 ≤ Real.log (n : ℝ) ^ 2 + K := by nlinarith only [hu1, hK]
  have hΛ0 : 0 ≤ Real.log (n : ℝ) ^ 2 + K := by linarith only [hΛ1]
  rcases Nat.eq_zero_or_pos h with h0 | hpos
  · subst h0
    simp only [Nat.add_zero, Nat.cast_zero, mul_zero, sub_self, abs_zero]
    positivity
  · have hs0 : 0 < s n := by linarith only [hs1]
    have hr := hrec hpos
    have hc3 : cStar * Real.log 3 ≤ 3 := by
      nlinarith only [hc2, hc, log_three_le, Real.log_pos (show (1 : ℝ) < 3 by norm_num)]
    have hc0 : 0 ≤ cStar * Real.log 3 := by
      have := Real.log_pos (show (1 : ℝ) < 3 by norm_num); positivity
    have hδ : |s (n + h) - s n - cStar * Real.log 3 * (s n)⁻¹ * (h : ℝ)| ≤
        Cr * (Real.log (n : ℝ) ^ 2 + K) / s n := by
      rw [← div_eq_mul_inv] at hr ⊢; exact hr
    have := square_increment_alg (s := s n) (h := (h : ℝ)) (c₃ := cStar * Real.log 3)
      (Λ := Real.log (n : ℝ) ^ 2 + K) (R := Cr)
      (δ := s (n + h) - s n - cStar * Real.log 3 * (s n)⁻¹ * (h : ℝ)) hs1 (by positivity) hhs
      hΛ1 hΛs hc0 hc3 hCr hδ
    have e : s n + cStar * Real.log 3 * (s n)⁻¹ * (h : ℝ) +
        (s (n + h) - s n - cStar * Real.log 3 * (s n)⁻¹ * (h : ℝ)) = s (n + h) := by ring
    rwa [e] at this

/-- Steps 2-5: the coarse lower comparison `c₃ n ≤ s_n²`. -/
theorem coarse_lower_of_square_increment (C1 cStar K A : ℝ) (hC1 : 0 ≤ C1) (hc : 0 < cStar)
    (hK : 0 ≤ K) (hA : 0 < A) (N1 : ℕ) (hN1 : 3 ≤ N1) :
    ∃ N4 : ℕ, N1 ≤ N4 ∧ ∀ s : ℕ → ℝ,
      (∀ n : ℕ, N1 ≤ n → 2 ≤ s n ∧ s n ≤ n ∧
        s n ≤ A * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (9 / 2 : ℝ) ∧
        A⁻¹ * (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) ^ (-(9 / 2 : ℝ)) ≤ s n) →
      (∀ n : ℕ, N1 ≤ n → ∀ h : ℕ, (h : ℝ) ≤ s n →
        |s (n + h) ^ 2 - s n ^ 2 - 2 * (cStar * Real.log 3) * (h : ℝ)| ≤
          C1 * (Real.log (n : ℝ) ^ 2 + K)) →
      ∀ n : ℕ, N4 ≤ n → cStar * Real.log 3 * (n : ℝ) ≤ s n ^ 2 := by
  have hl3 := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  have hc3 : 0 < cStar * Real.log 3 := by positivity
  obtain ⟨Nc, -, hNc⟩ := threshold_const_absorbed
    ((A * (N1 : ℝ) ^ (1 / 2 : ℝ) * Real.log (N1 : ℝ) ^ (9 / 2 : ℝ)) ^ 2 +
      2 * (cStar * Real.log 3) * N1) 1 K one_pos hK
  obtain ⟨Ncs, -, hNcs⟩ := threshold_coarse ((6 * A + 1) * C1 + 1) K (cStar * Real.log 3) hc3 hK
  refine ⟨max N1 (max Nc Ncs), le_max_left _ _, fun s hbr hsq n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hnc := hNc n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have hncs := hNcs n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  have hn3 : 3 ≤ n := le_trans hN1 hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hu1 := one_le_log_nat hn3
  set u := Real.log (n : ℝ) with hu
  have hu0 : 0 < u := by linarith only [hu1]
  set p := u ^ (9 / 2 : ℝ) with hp
  have hp1 : 1 ≤ p := Real.one_le_rpow hu1 (by norm_num)
  have hp0 : 0 < p := by linarith only [hp1]
  set w := (n : ℝ) ^ (1 / 2 : ℝ) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
  have hw0 : 0 < w := by linarith only [hw1]
  have hsqrt : Real.sqrt (n : ℝ) = w := by rw [Real.sqrt_eq_rpow, hw]
  have hΛ : 1 ≤ u ^ 2 + K := by nlinarith only [hu1, hK]
  -- the telescoping along `⌊s⌋`
  have hθ : 0 < A⁻¹ * p⁻¹ / 2 := by positivity
  have hfn := telescope_along_steps (fun m => s m ^ 2 - 2 * (cStar * Real.log 3) * (m : ℝ))
    (fun m => ⌊s m⌋₊) N1 n (A⁻¹ * p⁻¹ / 2) (C1 * (u ^ 2 + K)) hθ (by positivity) hn1
    (fun m hm1 _ => Nat.le_floor (by simpa using (le_trans (by norm_num) (hbr m hm1).1)))
    (fun m hm1 _ => by
      have h1 := hbr m hm1
      have : (⌊s m⌋₊ : ℝ) ≤ s m := Nat.floor_le (by linarith only [h1.1])
      exact_mod_cast le_trans this h1.2.1)
    (fun m hm1 hmn => by
      have h1 := hbr m hm1
      have hm3 : 3 ≤ m := le_trans hN1 hm1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hum := one_le_log_nat hm3
      have hlog : Real.log (m : ℝ) ≤ u := Real.log_le_log hm0 (by exact_mod_cast hmn)
      have hpm : Real.log (m : ℝ) ^ (9 / 2 : ℝ) ≤ p :=
        Real.rpow_le_rpow (by linarith only [hum]) hlog (by norm_num)
      have hpm0 : 0 < Real.log (m : ℝ) ^ (9 / 2 : ℝ) := by
        have := Real.one_le_rpow hum (show (0 : ℝ) ≤ 9 / 2 by norm_num); linarith only [this]
      have hlow := h1.2.2.2
      rw [Real.rpow_neg (by linarith only [hum])] at hlow
      have h2 : A⁻¹ * (m : ℝ) ^ (1 / 2 : ℝ) * p⁻¹ ≤ s m := by
        refine le_trans ?_ hlow
        have : p⁻¹ ≤ (Real.log (m : ℝ) ^ (9 / 2 : ℝ))⁻¹ := inv_anti₀ hpm0 hpm
        have : 0 ≤ A⁻¹ * (m : ℝ) ^ (1 / 2 : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left ‹p⁻¹ ≤ _› this
      have h3 := half_le_floor (show 1 ≤ s m by linarith only [h1.1])
      rw [← Real.sqrt_eq_rpow] at h2
      calc A⁻¹ * p⁻¹ / 2 * Real.sqrt (m : ℝ) = (A⁻¹ * Real.sqrt (m : ℝ) * p⁻¹) / 2 := by ring
        _ ≤ s m / 2 := by linarith only [h2]
        _ ≤ _ := h3)
    (fun m hm1 hmn h hh => by
      have h1 := hbr m hm1
      have hm3 : 3 ≤ m := le_trans hN1 hm1
      have hum := one_le_log_nat hm3
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hlog : Real.log (m : ℝ) ≤ u := Real.log_le_log hm0 (by exact_mod_cast hmn)
      have hhs : (h : ℝ) ≤ s m := by
        have : (⌊s m⌋₊ : ℝ) ≤ s m := Nat.floor_le (by linarith only [h1.1])
        exact le_trans (by exact_mod_cast hh) this
      have := hsq m hm1 h hhs
      have hu2 : Real.log (m : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith only [hum]) hlog 2
      have e : s (m + h) ^ 2 - 2 * (cStar * Real.log 3) * ((m + h : ℕ) : ℝ) -
          (s m ^ 2 - 2 * (cStar * Real.log 3) * (m : ℝ)) =
          s (m + h) ^ 2 - s m ^ 2 - 2 * (cStar * Real.log 3) * (h : ℝ) := by push_cast; ring
      rw [e]
      refine le_trans this ?_
      exact mul_le_mul_of_nonneg_left (by linarith only [hu2]) hC1)
  simp only [hsqrt] at hfn
  have hinv : (A⁻¹ * p⁻¹ / 2)⁻¹ = 2 * A * p := by field_simp
  rw [hinv] at hfn
  -- the initial value
  have hB := hbr N1 le_rfl
  have hN10 : (0 : ℝ) ≤ N1 := by positivity
  have hBd : |s N1 ^ 2 - 2 * (cStar * Real.log 3) * (N1 : ℝ)| ≤
      (A * (N1 : ℝ) ^ (1 / 2 : ℝ) * Real.log (N1 : ℝ) ^ (9 / 2 : ℝ)) ^ 2 +
        2 * (cStar * Real.log 3) * N1 := by
    have hs2 : s N1 ^ 2 ≤ (A * (N1 : ℝ) ^ (1 / 2 : ℝ) * Real.log (N1 : ℝ) ^ (9 / 2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hB.1]) hB.2.2.1 2
    have : 0 ≤ 2 * (cStar * Real.log 3) * (N1 : ℝ) := by positivity
    rw [abs_le]; constructor <;> nlinarith only [hs2, this, sq_nonneg (s N1)]
  rw [one_mul] at hnc
  -- assemble
  have hfn' : |s n ^ 2 - 2 * (cStar * Real.log 3) * (n : ℝ)| ≤
      ((6 * A + 1) * C1 + 1) * ((u ^ 2 + K) * w * p) := by
    have h1 : |s n ^ 2 - 2 * (cStar * Real.log 3) * (n : ℝ)| ≤
        |s n ^ 2 - 2 * (cStar * Real.log 3) * (n : ℝ) -
          (s N1 ^ 2 - 2 * (cStar * Real.log 3) * (N1 : ℝ))| +
        |s N1 ^ 2 - 2 * (cStar * Real.log 3) * (N1 : ℝ)| := by
      have := abs_add_le (s n ^ 2 - 2 * (cStar * Real.log 3) * (n : ℝ) -
          (s N1 ^ 2 - 2 * (cStar * Real.log 3) * (N1 : ℝ)))
        (s N1 ^ 2 - 2 * (cStar * Real.log 3) * (N1 : ℝ))
      rwa [sub_add_cancel] at this
    have hnc' : (A * (N1 : ℝ) ^ (1 / 2 : ℝ) * Real.log (N1 : ℝ) ^ (9 / 2 : ℝ)) ^ 2 +
        2 * (cStar * Real.log 3) * N1 ≤ (u ^ 2 + K) * w * p := by
      have : (u ^ 2 + K) * w ≤ (u ^ 2 + K) * w * p := by
        have : 0 ≤ (u ^ 2 + K) * w := by positivity
        nlinarith only [this, hp1]
      linarith only [hnc, this]
    have hmain : (3 * (2 * A * p) * w + 1) * (C1 * (u ^ 2 + K)) ≤
        ((6 * A + 1) * C1) * ((u ^ 2 + K) * w * p) := by
      have h1p : 1 ≤ w * p := by nlinarith only [hw1, hp1]
      have hC : 0 ≤ C1 * (u ^ 2 + K) := by positivity
      have : (3 * (2 * A * p) * w + 1) ≤ (6 * A + 1) * (w * p) := by
        nlinarith only [h1p, hA, mul_pos hw0 hp0]
      calc (3 * (2 * A * p) * w + 1) * (C1 * (u ^ 2 + K))
          ≤ ((6 * A + 1) * (w * p)) * (C1 * (u ^ 2 + K)) :=
            mul_le_mul_of_nonneg_right this hC
        _ = ((6 * A + 1) * C1) * ((u ^ 2 + K) * w * p) := by ring
    have hz : 0 ≤ (u ^ 2 + K) * w * p := by positivity
    linarith only [h1, hfn, hmain, hnc', hz, hBd]
  have hfin : ((6 * A + 1) * C1 + 1) * ((u ^ 2 + K) * w * p) ≤ cStar * Real.log 3 * n := by
    have := hncs
    calc _ = ((6 * A + 1) * C1 + 1) * (u ^ 2 + K) * w * p := by ring
      _ ≤ _ := this
  have := (abs_le.1 (le_trans hfn' hfin)).1
  linarith only [this]

/-- Step 6: telescoping along steps `⌊λ √m⌋`, `λ = ½ (c⋆ log 3)^{1/2}`. -/
theorem second_pass_telescope (C1 cStar K : ℝ) (hC1 : 0 ≤ C1) (hc : 0 < cStar) (hK : 0 ≤ K)
    (s : ℕ → ℝ) (N5 : ℕ) (hN5 : 3 ≤ N5)
    (hcond : ∀ n : ℕ, N5 ≤ n →
      1 ≤ (1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) ∧
      (1 / 2 * (cStar * Real.log 3) ^ (1 / 2 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) ≤ n ∧
      1 ≤ cStar ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ))
    (hcoarse : ∀ n : ℕ, N5 ≤ n → 0 < s n ∧ cStar * Real.log 3 * (n : ℝ) ≤ s n ^ 2)
    (hsq : ∀ n : ℕ, N5 ≤ n → ∀ h : ℕ, (h : ℝ) ≤ s n →
      |s (n + h) ^ 2 - s n ^ 2 - 2 * (cStar * Real.log 3) * (h : ℝ)| ≤
        C1 * (Real.log (n : ℝ) ^ 2 + K)) :
    ∀ N : ℕ, N5 ≤ N →
      |(s N ^ 2 - 2 * (cStar * Real.log 3) * (N : ℝ)) -
          (s N5 ^ 2 - 2 * (cStar * Real.log 3) * (N5 : ℝ))| ≤
        13 * C1 * (cStar ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (1 / 2 : ℝ)) *
          (Real.log (N : ℝ) ^ 2 + K) := by
  intro N hN
  have hl3 := Real.log_pos (show (1 : ℝ) < 3 by norm_num)
  have hc3 : 0 < cStar * Real.log 3 := by positivity
  have hq : (cStar * Real.log 3) ^ (1 / 2 : ℝ) = Real.sqrt (cStar * Real.log 3) :=
    (Real.sqrt_eq_rpow _).symm
  have hq0 : 0 < Real.sqrt (cStar * Real.log 3) := Real.sqrt_pos.2 hc3
  set q := Real.sqrt (cStar * Real.log 3) with hqdef
  have hconv : ∀ m : ℕ, (m : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (m : ℝ) := fun m =>
    (Real.sqrt_eq_rpow _).symm
  have hN3 : 3 ≤ N := le_trans hN5 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hu1 := one_le_log_nat hN3
  set u := Real.log (N : ℝ) with hu
  have hθ : 0 < (1 / 2 * q) / 2 := by positivity
  have hfn := telescope_along_steps (fun m => s m ^ 2 - 2 * (cStar * Real.log 3) * (m : ℝ))
    (fun m => ⌊1 / 2 * q * Real.sqrt (m : ℝ)⌋₊) N5 N ((1 / 2 * q) / 2) (C1 * (u ^ 2 + K)) hθ
    (by positivity) hN
    (fun m hm1 _ => by
      have := (hcond m hm1).1
      rw [hq, hconv] at this
      exact Nat.le_floor (by simpa using this))
    (fun m hm1 _ => by
      have := (hcond m hm1).2.1
      rw [hq, hconv] at this
      have h2 : (⌊1 / 2 * q * Real.sqrt (m : ℝ)⌋₊ : ℝ) ≤ 1 / 2 * q * Real.sqrt (m : ℝ) :=
        Nat.floor_le (by positivity)
      exact_mod_cast le_trans h2 this)
    (fun m hm1 _ => by
      have := (hcond m hm1).1
      rw [hq, hconv] at this
      have h3 := half_le_floor this
      calc (1 / 2 * q) / 2 * Real.sqrt (m : ℝ) = (1 / 2 * q * Real.sqrt (m : ℝ)) / 2 := by ring
        _ ≤ _ := h3)
    (fun m hm1 hmn h hh => by
      have hm3 : 3 ≤ m := le_trans hN5 hm1
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hum := one_le_log_nat hm3
      have hlog : Real.log (m : ℝ) ≤ u := Real.log_le_log hm0 (by exact_mod_cast hmn)
      have hco := hcoarse m hm1
      have hqm : q * Real.sqrt (m : ℝ) ≤ s m := by
        rw [hqdef, ← Real.sqrt_mul hc3.le]
        exact Real.sqrt_le_iff.2 ⟨hco.1.le, hco.2⟩
      have hx : 0 ≤ 1 / 2 * q * Real.sqrt (m : ℝ) := by positivity
      have hhs : (h : ℝ) ≤ s m := by
        have h2 : (⌊1 / 2 * q * Real.sqrt (m : ℝ)⌋₊ : ℝ) ≤ 1 / 2 * q * Real.sqrt (m : ℝ) :=
          Nat.floor_le hx
        have h4 : (h : ℝ) ≤ (⌊1 / 2 * q * Real.sqrt (m : ℝ)⌋₊ : ℝ) := by exact_mod_cast hh
        have h5 : 0 ≤ q * Real.sqrt (m : ℝ) := by positivity
        linarith only [h2, h4, hqm, h5]
      have := hsq m hm1 h hhs
      have hu2 : Real.log (m : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith only [hum]) hlog 2
      have e : s (m + h) ^ 2 - 2 * (cStar * Real.log 3) * ((m + h : ℕ) : ℝ) -
          (s m ^ 2 - 2 * (cStar * Real.log 3) * (m : ℝ)) =
          s (m + h) ^ 2 - s m ^ 2 - 2 * (cStar * Real.log 3) * (h : ℝ) := by push_cast; ring
      rw [e]
      refine le_trans this ?_
      exact mul_le_mul_of_nonneg_left (by linarith only [hu2]) hC1)
  have hr : cStar ^ (-(1 / 2 : ℝ)) = (Real.sqrt cStar)⁻¹ := by
    rw [Real.rpow_neg hc.le, Real.sqrt_eq_rpow]
  have hcq : Real.sqrt cStar ≤ q := by
    apply Real.sqrt_le_sqrt
    nlinarith only [hl3, one_lt_log_three, hc]
  have hsc : 0 < Real.sqrt cStar := Real.sqrt_pos.2 hc
  have hinv : ((1 / 2 * q) / 2)⁻¹ ≤ 4 * cStar ^ (-(1 / 2 : ℝ)) := by
    rw [hr]
    have : ((1 / 2 * q) / 2)⁻¹ = 4 / q := by field_simp; norm_num
    rw [this, div_eq_mul_inv]
    have : q⁻¹ ≤ (Real.sqrt cStar)⁻¹ := inv_anti₀ hsc hcq
    linarith only [this]
  have hN1c := (hcond N hN).2.2
  rw [hconv] at hN1c ⊢
  set r := cStar ^ (-(1 / 2 : ℝ)) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hs0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hE : 0 ≤ C1 * (u ^ 2 + K) := by positivity
  have hbd : 3 * ((1 / 2 * q) / 2)⁻¹ * Real.sqrt (N : ℝ) + 1 ≤ 13 * (r * Real.sqrt (N : ℝ)) := by
    have : 3 * ((1 / 2 * q) / 2)⁻¹ * Real.sqrt (N : ℝ) ≤ 12 * (r * Real.sqrt (N : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hinv hs0
      nlinarith only [this]
    linarith only [this, hN1c]
  calc _ ≤ _ := hfn
    _ ≤ (13 * (r * Real.sqrt (N : ℝ))) * (C1 * (u ^ 2 + K)) :=
        mul_le_mul_of_nonneg_right hbd hE
    _ = _ := by ring

end SuperdiffusionCLT.Section5
