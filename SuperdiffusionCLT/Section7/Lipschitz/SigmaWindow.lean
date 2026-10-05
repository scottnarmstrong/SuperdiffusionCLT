/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The window of `σ̄`

From `|σ̄_m - (2 c⋆ log 3 · m)^{1/2}| ≤ C c⋆⁻¹ (log² m + K)` for `m ≥ M`, the values `σ̄_k`,
`σ̄_m` with `k ≤ m ≤ 2k` and `k` large satisfy `1 ≤ σ̄_k ≤ k`, `σ̄_m ≤ 2 σ̄_k`, `σ̄_k ≤ 2 σ̄_m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

/-- Polylogarithms are negligible against the square root, along `2k`. -/
theorem lip_sigma_window_log {B D δ : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      B * Real.log (2 * (k : ℝ)) ^ 2 + D ≤ δ * Real.sqrt (k : ℝ) := by
  set T : ℝ := 2 * (64 * B + D) / δ + 1 with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ 2 * (64 * B + D) / δ := by positivity
    linarith only [this]
  refine ⟨⌈T ^ 8⌉₊, fun k hk => ?_⟩
  have hk1 : (T ^ 8 : ℝ) ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hT8 : 1 ≤ T ^ 8 := one_le_pow₀ hT1
  have hk0 : (1 : ℝ) ≤ k := hT8.trans hk1
  have hy : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
  set r : ℝ := (2 * (k : ℝ)) ^ ((1 : ℝ) / 8) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hy _
  have hrT : T ≤ r := by
    have h1 : (T ^ 8 : ℝ) ≤ 2 * k := by linarith only [hk1, hk0]
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have h3 : (T ^ 8 : ℝ) ^ ((1 : ℝ) / 8) = T := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith only [hT1])]
      norm_num
    rwa [h3] at h2
  have hlog : Real.log (2 * (k : ℝ)) ≤ 8 * r := by
    have := Real.log_le_rpow_div hy (by norm_num : (0 : ℝ) < 1 / 8)
    have e : (2 * (k : ℝ)) ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * r := by
      rw [← hr]; ring
    linarith only [this, e]
  have hlog0 : 0 ≤ Real.log (2 * (k : ℝ)) :=
    Real.log_nonneg (by linarith only [hk0])
  have hlog2 : Real.log (2 * (k : ℝ)) ^ 2 ≤ 64 * r ^ 2 := by
    have := pow_le_pow_left₀ hlog0 hlog 2
    linarith only [this]
  have hr4 : r ^ 4 = Real.sqrt (2 * (k : ℝ)) := by
    rw [Real.sqrt_eq_rpow, hr, ← Real.rpow_natCast, ← Real.rpow_mul hy]
    norm_num
  have hsq : Real.sqrt (2 * (k : ℝ)) ≤ 2 * Real.sqrt (k : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    linarith only [hk0]
  have hr1 : 1 ≤ r := hT1.trans hrT
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
  have hTr : T ≤ r ^ 2 := by
    have : r ≤ r ^ 2 := by
      calc r = r * 1 := (mul_one r).symm
        _ ≤ r * r := mul_le_mul_of_nonneg_left hr1 hr0
        _ = r ^ 2 := (sq r).symm
    exact hrT.trans this
  have hc : 2 * (64 * B + D) / δ ≤ r ^ 2 := by linarith only [hTr, hT]
  have hc2 : 64 * B + D ≤ δ / 2 * r ^ 2 := by
    rw [div_le_iff₀ hδ] at hc
    linarith only [hc]
  have hfin : 64 * B * r ^ 2 + D ≤ δ / 2 * r ^ 4 := by
    have h1 : (64 * B + D) * r ^ 2 ≤ δ / 2 * r ^ 2 * r ^ 2 :=
      mul_le_mul_of_nonneg_right hc2 (by positivity)
    have h2 : D ≤ D * r ^ 2 := by
      calc D = D * 1 := (mul_one D).symm
        _ ≤ D * r ^ 2 := mul_le_mul_of_nonneg_left hr2 hD
    have e4 : δ / 2 * r ^ 2 * r ^ 2 = δ / 2 * r ^ 4 := by ring
    linarith only [h1, h2, e4]
  have hB2 : B * Real.log (2 * (k : ℝ)) ^ 2 ≤ B * (64 * r ^ 2) :=
    mul_le_mul_of_nonneg_left hlog2 hB
  have hδ4 : δ / 2 * r ^ 4 ≤ δ * Real.sqrt (k : ℝ) := by
    rw [hr4]
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ δ / 2)
    linarith only [this]
  linarith only [hB2, hfin, hδ4]

/-- The deterministic comparison: all four bounds from the two-sided estimates. -/
theorem lip_sigma_window_real {κ e X x sk sm k : ℝ} (hκ : 0 < κ)
    (hxX : X ≤ x) (hx : x ≤ 3 / 2 * X)
    (hek : e ≤ κ / 6 * X) (hk1 : 2 ≤ κ * X) (hk2 : 2 * κ * X ≤ k)
    (hsk : |sk - κ * X| ≤ e) (hsm : |sm - κ * x| ≤ e) :
    1 ≤ sk ∧ sk ≤ k ∧ sm ≤ 2 * sk ∧ sk ≤ 2 * sm := by
  have h1 := abs_le.1 hsk
  have h2 := abs_le.1 hsm
  have hm1 : κ * x ≤ κ * (3 / 2 * X) := mul_le_mul_of_nonneg_left hx hκ.le
  have hm2 : κ * X ≤ κ * x := mul_le_mul_of_nonneg_left hxX hκ.le
  have e1 : κ * (3 / 2 * X) = 3 / 2 * (κ * X) := by ring
  have e2 : κ / 6 * X = (κ * X) / 6 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [h1.1, hek, hk1, e2]
  · linarith only [h1.2, hek, hk2, hk1, e2]
  · linarith only [h1.1, h2.2, hek, hm1, e1, e2]
  · linarith only [h1.2, h2.1, hek, hm2, e2, hk1]

/-- The deterministic core of the window of `σ̄`, for an arbitrary sequence. -/
theorem lip_sigma_window_seq {cStar B K : ℝ} (hc : 0 < cStar) (hB0 : 0 ≤ B) (M : ℕ) :
    ∃ L₀ : ℕ, ∀ s : ℕ → ℝ,
      (∀ m : ℕ, M ≤ m → |s m - (2 * cStar * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2)| ≤
        B * (Real.log (m : ℝ) ^ (2 : ℝ) + K)) →
      ∀ k m : ℕ, L₀ ≤ k → k ≤ m → m ≤ 2 * k →
      1 ≤ s k ∧ s k ≤ (k : ℝ) ∧ s m ≤ 2 * s k ∧ s k ≤ 2 * s m := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set A : ℝ := 2 * cStar * Real.log 3 with hA
  have hA0 : 0 < A := by positivity
  set κ : ℝ := Real.sqrt A with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 hA0
  obtain ⟨N, hN⟩ := lip_sigma_window_log hB0 (by positivity : 0 ≤ B * |K|) (by positivity : 0 < κ / 6)
  refine ⟨max (max M N) (max ⌈4 / κ ^ 2⌉₊ ⌈4 * κ ^ 2⌉₊ + 1), ?_⟩
  intro s hs k m hk hkm hm2
  have hMk : M ≤ k := by omega
  have hNk : N ≤ k := by omega
  have hk4a : ⌈4 / κ ^ 2⌉₊ ≤ k := by omega
  have hk4b : ⌈4 * κ ^ 2⌉₊ ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hkmR : (k : ℝ) ≤ m := by exact_mod_cast hkm
  have hm2R : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm2
  have hmR : (1 : ℝ) ≤ m := hkR.trans hkmR
  have hk4a' : 4 / κ ^ 2 ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk4a)
  have hk4b' : 4 * κ ^ 2 ≤ (k : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk4b)
  set X : ℝ := Real.sqrt (k : ℝ) with hXdef
  set x : ℝ := Real.sqrt (m : ℝ) with hxdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hXsq : X ^ 2 = k := Real.sq_sqrt (by positivity)
  have hxX : X ≤ x := Real.sqrt_le_sqrt hkmR
  have hx : x ≤ 3 / 2 * X := by
    rw [hxdef, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hXsq]
    linarith only [hm2R, hkR]
  have hkap : 2 ≤ κ * X := by
    have h : (2 : ℝ) ^ 2 ≤ (κ * X) ^ 2 := by
      rw [mul_pow, hXsq]
      have : 4 ≤ κ ^ 2 * k := by
        have := (div_le_iff₀ (by positivity : 0 < κ ^ 2)).1 hk4a'
        linarith only [this]
      linarith only [this]
    exact le_of_sq_le_sq (by linarith only [h]) (by positivity)
  have hkap2 : 2 * κ * X ≤ k := by
    have h : (2 * κ * X) ^ 2 ≤ (k : ℝ) ^ 2 := by
      have e : (2 * κ * X) ^ 2 = 4 * κ ^ 2 * k := by rw [mul_pow, mul_pow, hXsq]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hk4b' (by positivity : (0 : ℝ) ≤ k)
      linarith only [this, sq (k : ℝ)]
    exact le_of_sq_le_sq h (by positivity)
  -- the error term
  set e : ℝ := B * (Real.log (2 * (k : ℝ)) ^ 2 + |K|) with he
  have hek : e ≤ κ / 6 * X := by
    have := hN k hNk
    rw [he]
    linarith only [this, mul_add B (Real.log (2 * (k : ℝ)) ^ 2) |K|]
  have hbound : ∀ n : ℕ, M ≤ n → k ≤ n → n ≤ 2 * k →
      |s n - κ * Real.sqrt (n : ℝ)| ≤ e := by
    intro n hMn hkn hn2
    have h := hs n hMn
    have hnR : (1 : ℝ) ≤ n := hkR.trans (by exact_mod_cast hkn)
    have hn2R : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2
    have hsq : (2 * cStar * Real.log 3 * (n : ℝ)) ^ ((1 : ℝ) / 2) = κ * Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_eq_rpow, hκ, hA, Real.sqrt_mul (by positivity)]
    rw [hsq, Real.rpow_two] at h
    refine h.trans ?_
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have hlog : Real.log (n : ℝ) ≤ Real.log (2 * (k : ℝ)) :=
      Real.log_le_log (by linarith only [hnR]) hn2R
    have hlog2 : Real.log (n : ℝ) ^ 2 ≤ Real.log (2 * (k : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    have hKK : K ≤ |K| := le_abs_self K
    have := mul_le_mul_of_nonneg_left (add_le_add hlog2 hKK) hB0
    rw [he]
    linarith only [this]
  have hbk := hbound k hMk le_rfl (by omega)
  have hbm := hbound m (hMk.trans hkm) hkm hm2
  exact lip_sigma_window_real hκ0 hxX hx hek hkap hkap2 hbk hbm


/-- **The window of `σ̄`** (the "deterministic comparison of `σ̄_k` and `σ̄_m`"):
for `k ≤ m ≤ 2k`, `k ≥ L₀`. -/
theorem lip_sigma_window (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hS5 :
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
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ cStar : ℝ, 0 < cStar → ∀ K : ℝ,
      ∃ L₀ : ℕ, ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
        (hJ3 : ShellLawJ3 d P), ShellLawJ1Restriction d P → ShellLawJ4 d P →
        ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
        ∀ k m : ℕ, L₀ ≤ k → k ≤ m → m ≤ 2 * k →
          1 ≤ sigmaBarInfinite nu k P ∧ sigmaBarInfinite nu k P ≤ (k : ℝ) ∧
            sigmaBarInfinite nu m P ≤ 2 * sigmaBarInfinite nu k P ∧
            sigmaBarInfinite nu k P ≤ 2 * sigmaBarInfinite nu m P := by
  obtain ⟨C, hC1, hC⟩ := hS5
  have _hd := hd
  intro nu hnu hnu1 cStar hc K
  obtain ⟨M, hM⟩ := hC nu hnu hnu1 cStar hc K
  obtain ⟨L₀, hL⟩ := lip_sigma_window_seq (cStar := cStar) (B := C * cStar⁻¹) (K := K) hc
    (by positivity) M
  exact ⟨L₀, fun P hPrefix hJ2 hJ3 h1 h4 h5 k m hk hkm hm2 =>
    hL (fun n => sigmaBarInfinite nu n P) (fun n hn => hM P hPrefix hJ2 hJ3 h1 h4 h5 n hn)
      k m hk hkm hm2⟩

/-- Witness: the exact sequence `s_m = (2 c⋆ log 3 · m)^{1/2}` (error constants zero). -/
example : ∃ L₀ : ℕ, ∀ k m : ℕ, L₀ ≤ k → k ≤ m → m ≤ 2 * k →
    1 ≤ (2 * (1 : ℝ) * Real.log 3 * (k : ℝ)) ^ ((1 : ℝ) / 2) ∧
      (2 * (1 : ℝ) * Real.log 3 * (k : ℝ)) ^ ((1 : ℝ) / 2) ≤ (k : ℝ) ∧
      (2 * (1 : ℝ) * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2) ≤
        2 * (2 * (1 : ℝ) * Real.log 3 * (k : ℝ)) ^ ((1 : ℝ) / 2) ∧
      (2 * (1 : ℝ) * Real.log 3 * (k : ℝ)) ^ ((1 : ℝ) / 2) ≤
        2 * (2 * (1 : ℝ) * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨L₀, hL⟩ := lip_sigma_window_seq (cStar := 1) (B := 0) (K := 0) one_pos le_rfl 0
  exact ⟨L₀, hL (fun m => (2 * (1 : ℝ) * Real.log 3 * (m : ℝ)) ^ ((1 : ℝ) / 2))
    (fun m _ => by simp)⟩

end SuperdiffusionCLT.Section7
