/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.SstarLowerB
public import SuperdiffusionCLT.Section4.LNaught.Monotone
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# `e.L.vs.Lnaught.again`

For `m ≥ 2 L₀`, `n = ⌊m - h - 100 log₃(ν⁻¹ m)⌋`, `n ≥ m/2` and `m ≥ ν⁻²`, the infimum over
`r ≥ n` of `shom_{m-h,*}(cu_r)` is at least `m^{3/8} log^{3/2} m`, and so is the
infinite-volume limit.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

/-- Pure arithmetic: `m^{3/4} log³ m ≤ 16 L^{3/4} log³ L` when `m/2 ≤ L ≤ m`, `4 ≤ m`. -/
theorem lAgain_arith {m L : ℝ} (hm : 4 ≤ m) (hL : m / 2 ≤ L) :
    m ^ (3 / 4 : ℝ) * Real.log m ^ (3 : ℕ) ≤
      16 * (L ^ (3 / 4 : ℝ) * Real.log L ^ (3 : ℕ)) := by
  have hm0 : 0 < m := by linarith only [hm]
  have hL0 : 0 < L := by linarith only [hm, hL]
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (3 / 4 : ℝ) := by positivity
  have hpow : m ^ (3 / 4 : ℝ) ≤ 2 * L ^ (3 / 4 : ℝ) := by
    have h1 : (m / 2) ^ (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hL (by norm_num)
    rw [Real.div_rpow hm0.le (by norm_num)] at h1
    have h3 : m ^ (3 / 4 : ℝ) ≤ L ^ (3 / 4 : ℝ) * (2 : ℝ) ^ (3 / 4 : ℝ) := by
      rwa [div_le_iff₀ h2pos] at h1
    have hLp : 0 ≤ L ^ (3 / 4 : ℝ) := by positivity
    nlinarith only [h3, h2, hLp]
  have hlog2 : Real.log m ≤ 2 * Real.log L := by
    have h1 : Real.log (m / 2) ≤ Real.log L := Real.log_le_log (by positivity) hL
    rw [Real.log_div hm0.ne' (by norm_num)] at h1
    have h4 : Real.log 4 ≤ Real.log m := Real.log_le_log (by norm_num) hm
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith only [h1, h4, h42]
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by linarith only [hm])
  have hlogc : Real.log m ^ (3 : ℕ) ≤ 8 * Real.log L ^ (3 : ℕ) := by
    have := pow_le_pow_left₀ hlogm hlog2 3
    calc Real.log m ^ (3 : ℕ) ≤ (2 * Real.log L) ^ (3 : ℕ) := this
      _ = 8 * Real.log L ^ (3 : ℕ) := by ring
  have hLp : 0 ≤ L ^ (3 / 4 : ℝ) := by positivity
  have hlogL : 0 ≤ Real.log L ^ (3 : ℕ) :=
    pow_nonneg (Real.log_nonneg (by linarith only [hm, hL])) 3
  have hmp : 0 ≤ m ^ (3 / 4 : ℝ) := by positivity
  calc m ^ (3 / 4 : ℝ) * Real.log m ^ (3 : ℕ)
      ≤ (2 * L ^ (3 / 4 : ℝ)) * (8 * Real.log L ^ (3 : ℕ)) :=
        mul_le_mul hpow hlogc (by positivity) (by positivity)
    _ = 16 * (L ^ (3 / 4 : ℝ) * Real.log L ^ (3 : ℕ)) := by ring

/-- **`e.L.vs.Lnaught.again`**.  The scale hypotheses `m ≥ ν⁻²` and `m ≤ 2n` are the
two consequences of the enlarged threshold that the paper asserts ("we may further assume"). -/
theorem eLVsLnaughtAgain (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      ∀ cStar : ℝ, ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ K : ℝ,
      ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
        (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
        ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
      ∀ m h n : ℕ, 1 ≤ h → 400 * h ≤ m →
        2 * lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) → nu⁻¹ ^ 2 ≤ (m : ℝ) →
        n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ → m ≤ 2 * n →
        (∀ r : ℕ, n ≤ r →
          (m : ℝ) ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ) ≤
            sigmaBarStarScalar nu (m - h) P (Homogenization.cubeSet (Homogenization.originCube d (r : ℤ)))) ∧
        (m : ℝ) ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ) ≤ sigmaBarInfinite nu (m - h) P := by
  obtain ⟨C0a, hC0a1, c, hc, hMain⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower d hd
  obtain ⟨Cg, hCg1, hGe⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_ge
  set M2 : ℝ := max 1 (16 / c) with hM2
  have hM2one : 1 ≤ M2 := le_max_left _ _
  have hcM2 : 16 ≤ c * M2 := by
    have : 16 / c ≤ M2 := le_max_right _ _
    rwa [div_le_iff₀ hc, mul_comm] at this
  refine ⟨max (max C0a Cg) M2, le_trans hC0a1 (le_trans (le_max_left _ _) (le_max_left _ _)),
    ?_⟩
  intro C hC cStar nu hnu hnu1 K P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 m h n h1 h400 hL0 hnu2 hn hmn
  have hCa : C0a ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC
  have hCg : Cg ≤ C := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC
  have hCM : M2 ≤ C := le_trans (le_max_right _ _) hC
  have hcStar := hJ5.cStar_pos
  have hcStar2 := hJ5.cStar_le_two
  have hK := hJ5.K_pos.le
  have hC1 : 1 ≤ C := le_trans hM2one hCM
  have h8 := hGe C hCg C hC1 (3 / 4) (by norm_num) (by norm_num) cStar hcStar hcStar2 nu hnu hnu1 K hK
  have hm4 : (4 : ℝ) ≤ m := by linarith only [h8, hL0]
  have h400r : 400 * (h : ℝ) ≤ m := by exact_mod_cast h400
  set L : ℕ := m - h with hLdef
  have hhm : h ≤ m := by omega
  have hLr : (L : ℝ) = m - h := by rw [hLdef, Nat.cast_sub hhm]
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hmL : (m : ℝ) / 2 ≤ L := by rw [hLr]; linarith only [h400r, hh1, hm4]
  have hLm : (L : ℝ) ≤ m := by rw [hLr]; linarith only [hh1]
  have hlNmono := SuperdiffusionCLT.Section4.LNaught.lNaught_mono_both (C := C) (C' := C) (M := M2) (M' := C)
    (alpha := 3 / 4) (cStar := cStar) (nu := nu) (K := K) (by linarith only [hC1]) le_rfl
    (by linarith only [hM2one]) hCM hK hcStar hnu (by norm_num)
  have hmpos : (0 : ℝ) < m := by linarith only [hm4]
  have hlNL : lNaught C M2 (3 / 4) cStar nu K ≤ (L : ℝ) := by
    linarith only [hlNmono, hL0, hmL, h8]
  -- n ≤ L
  have hlogp : 0 ≤ Real.log (nu⁻¹ * m) / Real.log 3 := by
    apply div_nonneg
    · apply Real.log_nonneg
      have : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
      nlinarith only [this, hm4]
    · exact (Real.log_pos (by norm_num)).le
  have hnL : n ≤ L := by
    rw [hn]
    apply Nat.floor_le_of_le
    rw [hLr]; linarith only [hlogp]
  have hnLr : (L : ℝ) ≤ 2 * (n : ℝ) := by
    have : (m : ℝ) ≤ 2 * n := by exact_mod_cast hmn
    linarith only [this, hLm]
  have hLow := hMain C hCa M2 hM2one (3 / 4) (by norm_num) (by norm_num) cStar hcStar hcStar2 nu hnu
    hnu1 K hK P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hlNL n hnLr hnL
  have hari := lAgain_arith hm4 hmL
  have hLpos : (0 : ℝ) ≤ (L : ℝ) ^ (3 / 4 : ℝ) * Real.log L ^ (3 : ℕ) := by
    have : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hmL, hm4])
    positivity
  have hLow' : (m : ℝ) ^ (3 / 4 : ℝ) * Real.log m ^ (3 : ℕ) ≤
      sigmaBarStarScalar nu L P (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) ^ 2 := by
    have e1 : Real.log (L : ℝ) ^ (3 : ℝ) = Real.log (L : ℝ) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    calc (m : ℝ) ^ (3 / 4 : ℝ) * Real.log m ^ (3 : ℕ)
        ≤ 16 * ((L : ℝ) ^ (3 / 4 : ℝ) * Real.log L ^ (3 : ℕ)) := hari
      _ ≤ c * M2 * ((L : ℝ) ^ (3 / 4 : ℝ) * Real.log L ^ (3 : ℕ)) :=
          mul_le_mul_of_nonneg_right hcM2 hLpos
      _ = c * M2 * (L : ℝ) ^ (3 / 4 : ℝ) * Real.log (L : ℝ) ^ (3 : ℝ) := by rw [e1]; ring
      _ ≤ _ := hLow
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by linarith only [hm4])
  have hT0 : 0 ≤ (m : ℝ) ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ) := by positivity
  have hT2 : ((m : ℝ) ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ)) ^ 2 =
      (m : ℝ) ^ (3 / 4 : ℝ) * Real.log m ^ (3 : ℕ) := by
    have a1 : ((m : ℝ) ^ (3 / 8 : ℝ)) ^ 2 = (m : ℝ) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]; norm_num
    have a2 : (Real.log m ^ (3 / 2 : ℝ)) ^ 2 = Real.log m ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlogm0, ← Real.rpow_natCast]; norm_num
    rw [mul_pow, a1, a2]
  have hpos : ∀ r : ℕ, 0 < sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (r : ℤ))) := fun r => by
    rw [sigmaBarStarScalar_eq_inv hnu L hJ4 (r : ℤ)
      (sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 r)]
    exact inv_pos.2 (sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 r)
  have hSn : (m : ℝ) ^ (3 / 8 : ℝ) * Real.log m ^ (3 / 2 : ℝ) ≤ sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) := by
    refine (pow_le_pow_iff_left₀ hT0 (hpos n).le two_ne_zero).1 ?_
    rw [hT2]; exact hLow'
  refine ⟨fun r hr => le_trans hSn ?_, le_trans hSn
    (sigmaBarStarScalar_originCube_le_sigmaBarInfinite hnu L hPrefix hJ2 hJ3 hJ4 n)⟩
  have hanti := antitone_sigmaBarStarInvSeq hnu L hPrefix hJ2 hJ3 hJ4 hr
  rw [sigmaBarStarScalar_eq_inv hnu L hJ4 (n : ℤ) (sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n),
    sigmaBarStarScalar_eq_inv hnu L hJ4 (r : ℤ) (sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 r)]
  exact inv_anti₀ (sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 r) hanti

/-- Satisfiability of the scale hypotheses of `eLVsLnaughtAgain`: for any constants (in
particular `c⋆ = 2`, `ν = 1`, `K = 1`) and `h = 1` there is a scale `m` meeting all of them. -/
theorem eLVsLnaughtAgain_scale_witness (C cStar K : ℝ) (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    ∃ m h n : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧
      2 * lNaught C C (3 / 4) cStar nu K ≤ (m : ℝ) ∧ nu⁻¹ ^ 2 ≤ (m : ℝ) ∧
      n = ⌊(m : ℝ) - h - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ ∧ m ≤ 2 * n := by
  obtain ⟨t, ht⟩ := exists_nat_ge (max (max 1000 (2 * lNaught C C (3 / 4) cStar nu K)) (nu⁻¹ ^ 2))
  have ht1 : (1000 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht2 : 2 * lNaught C C (3 / 4) cStar nu K ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht3 : nu⁻¹ ^ 2 ≤ (t : ℝ) := le_trans (le_max_right _ _) ht
  refine ⟨t * t, 1, ⌊(((t * t : ℕ) : ℝ)) - (1 : ℕ) - 100 * (Real.log (nu⁻¹ * ((t * t : ℕ) : ℝ)) /
    Real.log 3)⌋₊, le_rfl, ?_, ?_, ?_, by push_cast; rfl, ?_⟩
  · have : 1000 ≤ t := by exact_mod_cast ht1
    nlinarith only [this]
  · push_cast; nlinarith only [ht1, ht2]
  · push_cast
    have : (1 : ℝ) ≤ (t : ℝ) := by linarith only [ht1]
    nlinarith only [ht3, this, inv_pos.2 hnu]
  · set m : ℝ := ((t * t : ℕ) : ℝ) with hm
    have hmt : m = (t : ℝ) * t := by rw [hm]; push_cast; ring
    have hm0 : 0 < m := by rw [hmt]; nlinarith only [ht1]
    have hnu' : 1 ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
    have hlog3 : 1 < Real.log 3 := by
      have := Real.exp_one_lt_d9
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      linarith only [this]
    have hnuinv : nu⁻¹ ≤ (t : ℝ) := by nlinarith only [ht3, hnu', ht1]
    have hlog : Real.log (nu⁻¹ * m) ≤ 3 * (t : ℝ) := by
      have h1 : Real.log (nu⁻¹ * m) ≤ nu⁻¹ * m - 1 := Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_mul (by positivity) hm0.ne'] at h1 ⊢
      have h2 : Real.log nu⁻¹ ≤ nu⁻¹ := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith only)
      have h3 : Real.log m ≤ 2 * (t : ℝ) := by
        have := Real.log_le_rpow_div hm0.le (show (0 : ℝ) < 1 / 2 by norm_num)
        have hs : m ^ (1 / 2 : ℝ) = (t : ℝ) := by
          rw [hmt, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self (by positivity)]
        rw [hs] at this
        linarith only [this]
      linarith only [h2, h3, hnuinv]
    have hlogpos : 0 ≤ Real.log (nu⁻¹ * m) := Real.log_nonneg (by nlinarith only [hnu', hm0, ht1, hmt])
    have hq : 100 * (Real.log (nu⁻¹ * m) / Real.log 3) ≤ 300 * (t : ℝ) := by
      have : Real.log (nu⁻¹ * m) / Real.log 3 ≤ Real.log (nu⁻¹ * m) :=
        div_le_self hlogpos hlog3.le
      linarith only [this, hlog]
    have hx : m / 2 + 1 ≤ m - 1 - 100 * (Real.log (nu⁻¹ * m) / Real.log 3) := by
      have hk : 300 * (t : ℝ) + 2 ≤ m / 2 := by rw [hmt]; nlinarith only [ht1]
      linarith only [hq, hk]
    have hfl := Nat.lt_floor_add_one (m - 1 - 100 * (Real.log (nu⁻¹ * m) / Real.log 3))
    have : (t * t : ℕ) ≤ 2 * ⌊m - 1 - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ := by
      have : ((t * t : ℕ) : ℝ) ≤ 2 * (⌊m - 1 - 100 * (Real.log (nu⁻¹ * m) / Real.log 3)⌋₊ : ℝ) := by
        rw [← hm]; linarith only [hfl, hx]
      exact_mod_cast this
    rw [Nat.cast_one]; exact this

end SuperdiffusionCLT.Section5
