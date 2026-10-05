/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.RootArithOneScaleD

/-!
# `hOneScale`'s union-bound inequality: substitution lemmas

In the proof of `p.minimal.scales`
(`e.new.mixing.minscale.one.scale`), this file collects identities and size
comparisons that connect the explicit amplitudes `srootMS_A1`, `srootMS_A2`,
`srootMS_Lhat2` to the abstract lemmas of `RootArithOneScaleD.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open SuperdiffusionCLT.Section4.LNaught
open SuperdiffusionCLT.Section4.NewMixing
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

noncomputable section

/-- `(C^{1/2} M^{1/2} s^{-3/2})² = (C M s⁻¹)(s⁻¹)²`. -/
theorem srootD_a_sq {C M s : ℝ} (hC : 0 < C) (hM : 0 < M) (hs : 0 < s) :
    (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) *
        (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) =
      (C * M * s⁻¹) * (s⁻¹) ^ 2 := by
  have hc : C ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) = C := by
    rw [← Real.rpow_add hC]; norm_num
  have hm : M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) = M := by
    rw [← Real.rpow_add hM]; norm_num
  have hss : s ^ (-((3 : ℝ) / 2)) * s ^ (-((3 : ℝ) / 2)) = (s⁻¹) ^ 3 := by
    rw [← Real.rpow_add hs, show -((3 : ℝ) / 2) + -((3 : ℝ) / 2) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hs.le, Real.rpow_natCast, inv_pow]
  calc (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) *
        (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)))
      = (C ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) * (M ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2)) *
          (s ^ (-((3 : ℝ) / 2)) * s ^ (-((3 : ℝ) / 2))) := by ring
    _ = C * M * (s⁻¹) ^ 3 := by rw [hc, hm, hss]
    _ = (C * M * s⁻¹) * (s⁻¹) ^ 2 := by ring

/-- `s^{-4} M² = (s⁻¹)⁴ M²`. -/
theorem srootD_S_eq {s M : ℝ} (hs : 0 < s) :
    s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) = (s⁻¹) ^ 4 * M ^ 2 := by
  rw [Real.rpow_neg hs.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.rpow_two, inv_pow]

/-- `delta^{-2} delta² = 1`. -/
theorem srootD_delta_neg2 {delta : ℝ} (hdel : 0 < delta) :
    delta ^ (-(2 : ℝ)) * delta ^ 2 = 1 := by
  rw [Real.rpow_neg hdel.le, Real.rpow_two]
  exact inv_mul_cancel₀ (by positivity)

/-- The `Γ₂` ratio, in the form used for the squared lower bounds. -/
theorem srootD_T1_eq {sig l r CE p q w D : ℝ} (hrr : r * r = l) (hr0 : 0 < r) (hsig : 0 < sig)
    (hCE : 0 < CE) (hp : 0 < p) (hq : 0 < q) (hw : 0 < w) :
    sig⁻¹ * l * D / (2 * (CE * p * q * w * sig⁻¹ * r)) = r * D / (2 * CE * (p * q * w)) := by
  subst hrr
  field_simp

/-- `K ≤ Q²` once `Q ≥ (C/4) u⁴ M²`, `C ≥ 16`. -/
theorem srootD_K_le {C u M Q : ℝ} (hC : 16 ≤ C) (hu : 1 ≤ u) (hM : 1 ≤ M)
    (hQ : (C / 4) * (u ^ 4 * M ^ 2) ≤ Q) : C * M * u ≤ Q ^ 2 := by
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hu4 : u ≤ u ^ 4 := by nlinarith only [hu, pow_le_pow_right₀ hu (show 1 ≤ 4 by norm_num)]
  have hM2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have h1 : M * u ≤ u ^ 4 * M ^ 2 := by
    have := mul_le_mul hM2 hu4 (by linarith only [hu]) (by positivity)
    linarith only [this]
  have h2 : C * (M * u) ≤ C * (u ^ 4 * M ^ 2) := mul_le_mul_of_nonneg_left h1 hC0
  have h3 : (C / 4) * (u ^ 4 * M ^ 2) ≤ Q := hQ
  have h4 : (0 : ℝ) ≤ (C / 4) * (u ^ 4 * M ^ 2) := by positivity
  have h5 : ((C / 4) * (u ^ 4 * M ^ 2)) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ h4 h3 2
  have h6 : (1 : ℝ) ≤ u ^ 4 * M ^ 2 := by
    have : (1 : ℝ) ≤ u ^ 4 := one_le_pow₀ hu
    have : (1 : ℝ) ≤ M ^ 2 := one_le_pow₀ hM
    nlinarith only [this, ‹(1 : ℝ) ≤ u ^ 4›]
  have hT : (16 : ℝ) ≤ C * (u ^ 4 * M ^ 2) := by nlinarith only [hC, h6]
  have h7 : C * (u ^ 4 * M ^ 2) ≤ ((C / 4) * (u ^ 4 * M ^ 2)) ^ 2 := by
    have : ((C / 4) * (u ^ 4 * M ^ 2)) ^ 2 = (C * (u ^ 4 * M ^ 2)) ^ 2 / 16 := by ring
    rw [this]
    nlinarith only [hT]
  nlinarith only [h2, h5, h7]

/-- `(m^ρ)² ≤ m` for `m ≥ 1`, `ρ ≤ 1/2`. -/
theorem srootD_Q_sq_le {m expon : ℝ} (hm : 1 ≤ m) (hexp1 : expon < 1 / 2) :
    (m ^ expon) ^ 2 ≤ m := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  have h : m ^ (2 * expon) ≤ m ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm (by linarith only [hexp1])
  rw [Real.rpow_one] at h
  have h2 : (m ^ expon) ^ 2 = m ^ (2 * expon) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    norm_num
    ring_nf
  rw [h2]
  exact h

/-- Lower bound for `(L̂₂^ρ)²` times `delta²`. -/
theorem srootD_Lh2_ge {C CE ei z u M delta P : ℝ} (hC : 2 ^ 21 * (CE * CE) ≤ C)
    (hCE : 1 ≤ CE) (hu : 1 ≤ u) (hM : 1 ≤ M) (hei : 2 ≤ ei) (hz : z * delta ^ 2 = 1)
    (hz0 : 0 < z) (hdel : 0 < delta) (hdel1 : delta ≤ 1)
    (hP : (C * (C * ei * z * (u ^ 4 * M ^ 2)) / 8) * (1 / 4096) ≤ P) :
    72 * CE ^ 2 * (C * M * u) * u ^ 2 ≤ (P * P) * delta ^ 2 := by
  have hCE2 : 1 ≤ CE * CE := by nlinarith only [hCE]
  have hC1 : (2 : ℝ) ^ 21 ≤ C := by nlinarith only [hC, hCE2]
  have hC0 : 0 < C := by linarith only [hC1, (by norm_num : (0 : ℝ) < 2 ^ 21)]
  have hu0 : 0 < u := by linarith only [hu]
  have hM0 : 0 < M := by linarith only [hM]
  have hd2 : delta ^ 2 ≤ 1 := by nlinarith only [hdel, hdel1]
  have hz1 : 1 ≤ z := by nlinarith only [hz, hd2, hz0]
  have hS : 1 ≤ u ^ 4 * M ^ 2 := by
    have h1 : (1 : ℝ) ≤ u ^ 4 := one_le_pow₀ hu
    have h2 : (1 : ℝ) ≤ M ^ 2 := one_le_pow₀ hM
    nlinarith only [h1, h2]
  -- lower bound of `P`
  have hB : C * C * z * (u ^ 4 * M ^ 2) / 16384 ≤ P := by
    have h1 : C * C * (2 * z * (u ^ 4 * M ^ 2)) ≤ C * C * (ei * z * (u ^ 4 * M ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 0 ≤ z * (u ^ 4 * M ^ 2) := by positivity
      nlinarith only [hei, this]
    nlinarith only [h1, hP]
  have hPge1 : 1 ≤ P := by
    have h1 : (2 : ℝ) ^ 21 * 2 ^ 21 ≤ C * C := by nlinarith only [hC1]
    have h2 : 1 ≤ z * (u ^ 4 * M ^ 2) := by nlinarith only [hz1, hS]
    have h3 : C * C * 1 ≤ C * C * (z * (u ^ 4 * M ^ 2)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith only [hB, h1, h3]
  have hPP : P ≤ P * P := by nlinarith only [hPge1]
  have hstep : C * C * (u ^ 4 * M ^ 2) / 16384 ≤ P * delta ^ 2 := by
    have h1 : C * C * z * (u ^ 4 * M ^ 2) / 16384 * delta ^ 2 ≤ P * delta ^ 2 :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    have h2 : C * C * z * (u ^ 4 * M ^ 2) / 16384 * delta ^ 2 =
        C * C * (u ^ 4 * M ^ 2) / 16384 * (z * delta ^ 2) := by ring
    rw [h2, hz] at h1
    linarith only [h1]
  have hfin : 72 * CE ^ 2 * (C * M * u) * u ^ 2 ≤ C * C * (u ^ 4 * M ^ 2) / 16384 := by
    have hM2 : M ≤ M ^ 2 := by nlinarith only [hM]
    have h2 : (72 * 16384 : ℝ) * CE ^ 2 ≤ C := by nlinarith only [hC, hCE2]
    have h3 : 72 * CE ^ 2 * (C * M * u) * u ^ 2 = 72 * CE ^ 2 * C * (M * u * u ^ 2) := by ring
    have h4 : C * C * (u ^ 4 * M ^ 2) / 16384 = C * C * (M ^ 2 * u ^ 4) / 16384 := by ring
    have h5 : M * u * u ^ 2 ≤ M ^ 2 * u ^ 4 := by
      have := mul_le_mul hM2 (pow_le_pow_right₀ hu (show 3 ≤ 4 by norm_num)) (by positivity)
        (by positivity)
      linarith only [this]
    have h6 : 72 * CE ^ 2 * C * (M * u * u ^ 2) ≤ 72 * CE ^ 2 * C * (M ^ 2 * u ^ 4) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have h7 : 72 * CE ^ 2 * C * (M ^ 2 * u ^ 4) ≤ C * C * (M ^ 2 * u ^ 4) / 16384 := by
      have h8 : 0 ≤ C * (M ^ 2 * u ^ 4) := by positivity
      nlinarith only [h2, h8]
    rw [h3, h4]
    exact le_trans h6 h7
  calc 72 * CE ^ 2 * (C * M * u) * u ^ 2 ≤ C * C * (u ^ 4 * M ^ 2) / 16384 := hfin
    _ ≤ P * delta ^ 2 := hstep
    _ ≤ (P * P) * delta ^ 2 := mul_le_mul_of_nonneg_right hPP (by positivity)

/-- **The finite union-bound inequality of `hOneScale`**, given the `L₀`-threshold
comparison at `m` and the size thresholds on `C`. -/
theorem srootD_union_core (d : ℕ) {CE Cg C nu cStar nondeg expon delta s M sig : ℝ} {m : ℕ}
    (hCE1 : 1 ≤ CE) (hCg1 : 1 ≤ Cg)
    (h144 : 144 * (CE * CE) ≤ C) (h24 : 24 * Cg * CE ≤ C)
    (hCexp : 4 * Real.exp (288 * (14 * (d : ℝ) + 10) * CE ^ 2) ≤ C)
    (h21 : 2 ^ 21 * (CE * CE) ≤ C) (h16 : 16 ≤ C)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnondeg : 0 < nondeg) (hexp0 : 0 < expon) (hexp1 : expon < 1 / 2)
    (hdel0 : 0 < delta) (hdel1 : delta ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1) (hM : 1 ≤ M)
    (hthr1 : (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) *
        cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) ≤ (m : ℝ) ^ expon)
    (hLh4 : 4 * Real.log 3 ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg)
    (hLh : srootMS_Lhat2 C expon delta s M cStar nu nondeg ≤ (m : ℝ))
    (hsig0 : 0 < sig) (hsigle : sig ≤ Cg * nu⁻¹ * (1 + (m : ℝ))) :
    (((⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ : ℝ) + 1) *
        (2 * (3 : ℝ) ^ (⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ + 3) + 1) ^ d) *
      (Real.exp (-(((srootMS_target delta sig expon m -
            srootMS_det CE s (C * M * s⁻¹) sig m) /
            (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m)) ^ (2 : ℝ))) +
        Real.exp (-(((srootMS_target delta sig expon m -
            srootMS_det CE s (C * M * s⁻¹) sig m) /
            (2 * srootMS_A2 CE m)) ^ ((2 : ℝ) / 3)))) ≤
      (((m : ℝ) ^ 2)⁻¹) *
        Real.exp (-((2 * Real.log 3 * (m : ℝ) /
          srootMS_Lhat2 C expon delta s M cStar nu nondeg) ^ (2 * expon))) := by
  have hCEpos : 0 < CE := lt_of_lt_of_le one_pos hCE1
  have hC1 : (1 : ℝ) ≤ C := by nlinarith only [h144, hCE1]
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC1
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hu1 : (1 : ℝ) ≤ s⁻¹ := (one_le_inv₀ hs0).2 hs1
  have hu0 : (0 : ℝ) < s⁻¹ := inv_pos.2 hs0
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hlogm1 : 1 ≤ Real.log (m : ℝ) := srootA2_logm_ge_one hLh4 hLh
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := le_trans zero_le_one hlogm1
  have hm4 : (4 : ℝ) < (m : ℝ) := srootA2_m_gt_four hLh4 hLh
  have hm1r : (1 : ℝ) ≤ (m : ℝ) := by linarith only [hm4]
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith only [hm4]
  have hLhpos : 0 < srootMS_Lhat2 C expon delta s M cStar nu nondeg := by
    linarith only [hLh4, hlog3]
  -- the `R'` chain
  have hR := srootA2_Rprime_le_delta_mexpon hCpos.le hexp0 hdel0 hs0 hMpos.le hcStar hcStar2 hnu
    hlogm0 hthr1
  have hslackM := srootA2_slack_ge_two hexp0 hexp1 hdel0 hdel1 hnu hnu1 hlogm1
  have hBound1 := srootA2_delta_mexpon_ge_Mslot hCpos.le hs0 hMpos.le hslackM hR
  have hslackNu := srootA2_slack_ge_two_nu hexp0 hexp1 hdel0 hdel1 hs0 hs1 hM hlogm1
  have hBound2 := srootA2_delta_mexpon_ge_nu hCpos.le hnu hslackNu hR
  have hKey2 := srootA2_key_ineq_delta hCE1 h144 hM hs0 hs1
  have hDeltaTwoThirds := srootA2_Delta_ge_two_thirds hs0 hBound1 hKey2
  have hDeltaNu := srootA2_Delta_ge_nu hDeltaTwoThirds hBound2
  -- the `(log m)^12`-strengthened bound
  have hSe := srootD_S_eq (s := s) (M := M) hs0
  have hslack2 := srootD_slack_two hexp0 hexp1 hdel0 hdel1 hnu hnu1
  have hBY := srootD_bound_Y hCpos.le hs0 hMpos.le hlogm0 hslack2 hR
  rw [hSe] at hBY
  have hY1 : (1 : ℝ) ≤ Real.log (m : ℝ) ^ (12 : ℝ) := Real.one_le_rpow hlogm1 (by norm_num)
  have hYl : Real.log (m : ℝ) ≤ Real.log (m : ℝ) ^ (12 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hlogm1 (show (1 : ℝ) ≤ 12 by norm_num)
    rwa [Real.rpow_one] at this
  have hY0 : (0 : ℝ) ≤ Real.log (m : ℝ) ^ (12 : ℝ) := by linarith only [hY1]
  have hS1 : (1 : ℝ) ≤ (s⁻¹) ^ 4 * M ^ 2 := by
    have h1 : (1 : ℝ) ≤ (s⁻¹) ^ 4 := one_le_pow₀ hu1
    have h2 : (1 : ℝ) ≤ M ^ 2 := one_le_pow₀ hM
    nlinarith only [h1, h2]
  have hQ0 : (0 : ℝ) ≤ (m : ℝ) ^ expon := Real.rpow_nonneg hmpos.le _
  have hdQ : (0 : ℝ) ≤ delta * (m : ℝ) ^ expon := by positivity
  have hdQle : delta * (m : ℝ) ^ expon ≤ (m : ℝ) ^ expon := by nlinarith only [hdel1, hQ0]
  have hQle : (m : ℝ) ^ expon ≤ (m : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hm1r (show expon ≤ 1 by linarith only [hexp1])
    rwa [Real.rpow_one] at this
  have hSY : (1 : ℝ) ≤ ((s⁻¹) ^ 4 * M ^ 2) * Real.log (m : ℝ) ^ (12 : ℝ) := by
    nlinarith only [hS1, hY1]
  have hCQ : C / 4 ≤ (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hSY (by positivity : (0 : ℝ) ≤ C / 4)
    linarith only [this, hBY, hdQle, hQle]
  have hexpm : Real.exp (288 * (14 * (d : ℝ) + 10) * CE ^ 2) ≤ (m : ℝ) := by
    linarith only [hCQ, hCexp]
  have hLam : 288 * (14 * (d : ℝ) + 10) * CE ^ 2 ≤ Real.log (m : ℝ) :=
    (Real.le_log_iff_exp_le hmpos).2 hexpm
  have hY2 : 288 * (14 * (d : ℝ) + 10) * CE ^ 2 ≤ (Real.log (m : ℝ) ^ (12 : ℝ)) ^ 2 := by
    nlinarith only [hLam, hYl, hY1]
  have hDY : (C / 6) * ((s⁻¹) ^ 4 * M ^ 2) * Real.log (m : ℝ) ^ (12 : ℝ) ≤
      delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ := by
    linarith only [hBY, hDeltaTwoThirds]
  -- `T₁` in closed form
  have hrr : Real.sqrt (Real.log (m : ℝ)) * Real.sqrt (Real.log (m : ℝ)) = Real.log (m : ℝ) :=
    Real.mul_self_sqrt hlogm0
  have hr0 : 0 < Real.sqrt (Real.log (m : ℝ)) := Real.sqrt_pos.2 (by linarith only [hlogm1])
  have hsq : Real.log (m : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (Real.log (m : ℝ)) :=
    (Real.sqrt_eq_rpow _).symm
  have hT1eq : (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
      (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m) =
      Real.sqrt (Real.log (m : ℝ)) *
        (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) /
        (2 * CE * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)))) := by
    rw [srootA2_target_sub_det_eq (CE := CE) (C := C) (M := M) (s := s) (delta := delta)
      (sig := sig) (expon := expon) m hCpos.le hMpos.le hs0,
      srootA2_A1_eq CE C M s sig m hCpos.le hMpos.le hs0, hsq]
    exact srootD_T1_eq hrr hr0 hsig0 hCEpos (Real.rpow_pos_of_pos hCpos _)
      (Real.rpow_pos_of_pos hMpos _) (Real.rpow_pos_of_pos hs0 _)
  obtain ⟨hA, hB⟩ := srootD_T1sq hr0 hrr hCE1 (srootD_a_sq hCpos hMpos hs0) rfl hC1 hM hu1 hY0
    hdQ hDY hDeltaTwoThirds
  -- the `L̂₂`-tail
  have hLpow := srootD_Lhat2_rpow_ge hCpos.le hexp0 hexp1 hdel0 hs0 hMpos.le hcStar hcStar2 hnu
    hnu1 hnondeg
  have hexpinv : (2 : ℝ) ≤ expon⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hexp0]; linarith only [hexp1]
  have hzpos : (0 : ℝ) < delta ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hdel0 _
  have hP1 : (C * (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * ((s⁻¹) ^ 4 * M ^ 2)) / 8) * (1 / 4096) ≤
      srootMS_Lhat2 C expon delta s M cStar nu nondeg ^ expon := by
    have e1 : C * (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) / 8 =
        C * (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * (s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))) / 8 := by ring
    rw [e1, hSe] at hLpow
    exact le_trans (mul_le_mul_of_nonneg_left srootD_log2_pow_ge (by positivity)) hLpow
  have hL := srootD_Lh2_ge h21 hCE1 hu1 hM hexpinv (srootD_delta_neg2 hdel0) hzpos hdel0 hdel1 hP1
  have hLh2eq : srootMS_Lhat2 C expon delta s M cStar nu nondeg ^ (2 * expon) =
      srootMS_Lhat2 C expon delta s M cStar nu nondeg ^ expon *
        srootMS_Lhat2 C expon delta s M cStar nu nondeg ^ expon := by
    rw [two_mul, Real.rpow_add hLhpos]
  have hWL := srootD_W_mul_le (m := (m : ℝ)) hexp1 hLhpos hmpos
  rw [hLh2eq] at hWL
  have hW0 : 0 ≤ (2 * Real.log 3 * (m : ℝ) / srootMS_Lhat2 C expon delta s M cStar nu nondeg) ^
      (2 * expon) := Real.rpow_nonneg (by positivity) _
  have hK1 : (1 : ℝ) ≤ C * M * s⁻¹ := by
    have h1 : (1 : ℝ) ≤ C * M := by nlinarith only [hC1, hM]
    nlinarith only [h1, hu1]
  have hKpos : (0 : ℝ) < C * M * s⁻¹ := by linarith only [hK1]
  have hX1 := srootD_X1_ge (n := 14 * (d : ℝ) + 10) hCE1 hlogm1 hKpos hW0 hdel0 hu0 hA hB hY2
    hWL hL
  -- `T₂`
  have hT := srootD_T2_ge (m := m) hCE1 hCg1 hnu hnu1 hsig0 hm1r hlogm1 hsigle h24 hDeltaNu
  have hT2eq : (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
      (2 * srootMS_A2 CE m) =
      (sig⁻¹ * Real.log (m : ℝ) *
        (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹)) /
        (2 * (CE * (m : ℝ) ^ (-(1000 : ℝ)))) := by
    rw [srootA2_target_sub_det_eq (CE := CE) (C := C) (M := M) (s := s) (delta := delta)
      (sig := sig) (expon := expon) m hCpos.le hMpos.le hs0]
    rfl
  have hQK : (C / 4) * ((s⁻¹) ^ 4 * M ^ 2) ≤ (m : ℝ) ^ expon := by
    have := mul_le_mul_of_nonneg_left hY1 (by positivity : (0 : ℝ) ≤ (C / 4) * ((s⁻¹) ^ 4 * M ^ 2))
    linarith only [this, hBY, hdQle]
  have hKm : C * M * s⁻¹ ≤ (m : ℝ) :=
    le_trans (srootD_K_le h16 hu1 hM hQK) (srootD_Q_sq_le hm1r hexp1)
  have hlm : Real.log (m : ℝ) ≤ (m : ℝ) := Real.log_le_self hmpos.le
  have hWm := srootD_W_le_m hexp0 hexp1 hLh4 hLh
  have hnm : (14 * (d : ℝ) + 10) + 1 ≤ (m : ℝ) := by
    have h1 := Real.add_one_le_exp (288 * (14 * (d : ℝ) + 10) * CE ^ 2)
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hCE2 : (1 : ℝ) ≤ CE ^ 2 := by nlinarith only [hCE1]
    nlinarith only [h1, hexpm, hd0, hCE2]
  have hn0 : (0 : ℝ) ≤ 14 * (d : ℝ) + 10 := by positivity
  have hX2 := srootD_X2_ge hn0 hlogm1 hKm hlm hWm hnm hT
  have hX1' : (14 * (d : ℝ) + 10) * ((C * M * s⁻¹) * Real.log (m : ℝ)) +
      (2 * Real.log 3 * (m : ℝ) / srootMS_Lhat2 C expon delta s M cStar nu nondeg) ^ (2 * expon) ≤
      ((srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
        (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m)) ^ (2 : ℝ) := by
    rw [hT1eq, Real.rpow_two]
    exact hX1
  have hX2' : (14 * (d : ℝ) + 10) * ((C * M * s⁻¹) * Real.log (m : ℝ)) +
      (2 * Real.log 3 * (m : ℝ) / srootMS_Lhat2 C expon delta s M cStar nu nondeg) ^ (2 * expon) ≤
      ((srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
        (2 * srootMS_A2 CE m)) ^ ((2 : ℝ) / 3) := by
    rw [hT2eq]
    exact hX2
  exact srootD_union_bound d hK1 hlogm1 hmpos rfl hX1' hX2'

/-- **`hOneScale` for `srootMS_minimal_scales_of_inputs`**: the three conjuncts
`4 log 3 ≤ L̂₂`, the two floors `1 ≤ T₁`, `1 ≤ T₂`, and the finite union-bound
inequality. -/
theorem srootD_hOneScale (d : ℕ) :
    ∀ CE Cg : ℝ, 1 ≤ CE → 1 ≤ Cg → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 → 0 < cStar → cStar ≤ 2 → 0 < nondeg →
        ∀ (expon delta s M : ℝ), 0 < expon → expon < 1 / 2 → 0 < delta → delta ≤ 1 →
          0 < s → s ≤ 1 → 1 ≤ M →
            4 * Real.log 3 ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg ∧
            ∀ (sig : ℝ) (m : ℕ), srootMS_Lhat2 C expon delta s M cStar nu nondeg ≤ (m : ℝ) →
              0 < sig → sig ≤ Cg * nu⁻¹ * (1 + (m : ℝ)) →
                1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
                    (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m) ∧
                1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
                    (2 * srootMS_A2 CE m) ∧
                (((⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ : ℝ) + 1) *
                    (2 * (3 : ℝ) ^ (⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ + 3) + 1) ^ d) *
                  (Real.exp (-(((srootMS_target delta sig expon m -
                        srootMS_det CE s (C * M * s⁻¹) sig m) /
                        (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m)) ^ (2 : ℝ))) +
                    Real.exp (-(((srootMS_target delta sig expon m -
                        srootMS_det CE s (C * M * s⁻¹) sig m) /
                        (2 * srootMS_A2 CE m)) ^ ((2 : ℝ) / 3)))) ≤
                  (((m : ℝ) ^ 2)⁻¹) *
                    Real.exp (-((2 * Real.log 3 * (m : ℝ) /
                      srootMS_Lhat2 C expon delta s M cStar nu nondeg) ^ (2 * expon))) := by
  intro CE Cg hCE1 hCg1
  obtain ⟨CLT, hCLT1, hthr⟩ := lNaught_threshold
  obtain ⟨CFL, hCFL1, hFL⟩ := srootA_hOneScale_fourLog3
  obtain ⟨Cf, hCf1, hfl⟩ := srootA2_hOneScale_floors CE Cg hCE1 hCg1
  refine ⟨max Cf (max (144 * (CE * CE)) (max (24 * Cg * CE) (max CLT (max CFL
    (max (4 * Real.exp (288 * (14 * (d : ℝ) + 10) * CE ^ 2))
      (max (2 ^ 21 * (CE * CE)) 16)))))), le_trans hCf1 (le_max_left _ _), ?_⟩
  intro C hC0 nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg expon delta s M hexp0 hexp1
    hdel0 hdel1 hs0 hs1 hM
  simp only [max_le_iff] at hC0
  obtain ⟨hCf, h144, h24, hCLT, hCFL, hCexp, h21, h16⟩ := hC0
  have hLh4 : 4 * Real.log 3 ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg :=
    hFL C hCFL nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg expon delta s M hexp0 hexp1
      hdel0 hdel1 hs0 hs1 hM
  refine ⟨hLh4, ?_⟩
  intro sig m hLh hsig0 hsigle
  obtain ⟨hT1, hT2⟩ := hfl C hCf nu cStar nondeg hnu hnu1 hcStar hcStar2 hnondeg expon delta s M
    hexp0 hexp1 hdel0 hdel1 hs0 hs1 hM sig m hLh hsig0 hsigle
  refine ⟨hT1, hT2, ?_⟩
  have hC1 : (1 : ℝ) ≤ C := by nlinarith only [h144, hCE1]
  have hMprime1 : (1 : ℝ) ≤ C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) :=
    srootA2_Mprime_ge_one hC1 hexp0 (by linarith only [hexp1]) hdel0 hdel1 hs0 hs1 hM
  have hL1m : lNaught C (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
      (1 - expon) cStar nu nondeg ≤ (m : ℝ) := by
    have hle : lNaught C (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
        (1 - expon) cStar nu nondeg ≤ srootMS_Lhat2 C expon delta s M cStar nu nondeg := by
      unfold srootMS_Lhat2; exact le_max_left _ _
    exact le_trans hle hLh
  have hthr' := hthr C hCLT _ hMprime1 (1 - expon) (by linarith only [hexp1])
    (by linarith only [hexp0]) cStar hcStar hcStar2 nu hnu hnu1 nondeg hnondeg.le m hL1m
  have hthr1 := hthr'.1
  rw [show (1 : ℝ) - (1 - expon) = expon by ring] at hthr1
  exact srootD_union_core d hCE1 hCg1 h144 h24 hCexp h21 h16 hnu hnu1 hcStar hcStar2
    hnondeg hexp0 hexp1 hdel0 hdel1 hs0 hs1 hM hthr1 hLh4 hLh hsig0 hsigle

/-- **`p.minimal.scales`** from the
body of `mathcalE_bounds` alone: the threshold comparison and the one-scale union-bound
arithmetic are supplied by `srootA_hThr` and `srootD_hOneScale`. -/
theorem srootMS_minimal_scales_of_hE (d : ℕ) [NeZero d]
    (hE :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 →
            ∀ K : ℝ, C ≤ K →
              ∀ m n : ℕ,
                SuperdiffusionCLT.Frozen.Section4.lNaught C (C * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
                m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n →
                n ≤ m →
                ∀ k : Fin d → ℤ,
                                    (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                        Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                  ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                    Measurable X1 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma 2) X1
                        (C * s⁻¹ * K ^ ((1 : ℝ) / 2) *
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                              P)⁻¹ *
                          Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ∧
                    Measurable X2 ∧
                    Homogenization.IndependentSums.IsBigO P.toMeasure
                        (Homogenization.IndependentSums.gammaSigma (2 / 3)) X2
                        (C * (m : ℝ) ^ (-(1000 : ℝ))) ∧
                      ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d
                          ∂P.toMeasure,
                        ∀ L : ℕ, (m : ℝ) - C * s⁻¹ * ((⌈K * Real.log (m : ℝ)⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) →
                          Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                                    nu omega L
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))).toCoeffField
                                  ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) +
                            Homogenization.HomogenizationErrorOnCube
                              (Homogenization.originCube d (n : ℤ)) s
                              Homogenization.MultiscaleExponent.infinity
                              (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                              (fun x =>
                                nu • (1 : Homogenization.Mat d) +
                                  SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                                    omega
                                    (Homogenization.cubeSet
                                      (Homogenization.originCube d (m : ℤ)))
                                    ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                              (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu
                                  m P •
                                (1 : Homogenization.Mat d)) ≤
                            C * s ^ (-((1 : ℝ) / 2)) * K ^ ((1 : ℝ) / 2) *
                                (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite
                                    nu m P)⁻¹ *
                                Real.log (m : ℝ) +
                              X1 omega + X2 omega)
    :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ (expon delta s M : ℝ),
            0 < expon → expon < 1 / 2 →
            0 < delta → delta ≤ 1 →
            0 < s → s ≤ 1 →
            1 ≤ M →
            ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
              Measurable X ∧
              Homogenization.IndependentSums.IsBigO P.toMeasure
                  (Homogenization.IndependentSums.gammaSigma (2 * expon))
                  (fun omega => Real.log (X omega))
                  (max
                    (SuperdiffusionCLT.Frozen.Section4.lNaught C
                      (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
                      (1 - expon) cStar nu nondeg)
                    (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * s ^ (-(2 : ℝ))) (1 / 2 + expon) cStar nu
                      nondeg)) ∧
              ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                ∀ m n : ℕ,
                  max
                      (SuperdiffusionCLT.Frozen.Section4.lNaught C
                        (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
                        (1 - expon) cStar nu nondeg)
                      (SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M * s ^ (-(2 : ℝ))) (1 / 2 + expon) cStar nu
                        nondeg) ≤
                    (m : ℝ) →
                  X omega ≤ (3 : ℝ) ^ m →
                  m - ⌈C * M * s⁻¹ * Real.log (m : ℝ)⌉₊ ≤ n →
                  n ≤ m →
                  (∀ L : ℕ, m ≤ L →
                    ∀ k : Fin d → ℤ,
                                            (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                            Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                          Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                      Homogenization.HomogenizationErrorOnCube
                          (Homogenization.originCube d (n : ℤ)) s
                          Homogenization.MultiscaleExponent.infinity
                          (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                          (fun x =>
                            (SuperdiffusionCLT.Section2.Cutoff.centeredCoefficientCutoff
                                nu omega L
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (m : ℤ)))).toCoeffField
                              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                            (1 : Homogenization.Mat d)) ≤
                        delta *
                          (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                              P)⁻¹ *
                          (m : ℝ) ^ expon * Real.log (m : ℝ)) ∧
                  (∀ k : Fin d → ℤ,
                                        (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                          Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                        Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
                    Homogenization.HomogenizationErrorOnCube
                        (Homogenization.originCube d (n : ℤ)) s
                        Homogenization.MultiscaleExponent.infinity
                        (Homogenization.MultiscaleExponent.finite (2 : ℝ))
                        (fun x =>
                          nu • (1 : Homogenization.Mat d) +
                            SuperdiffusionCLT.Section2.Carriers.centeredStreamField
                              omega
                              (Homogenization.cubeSet
                                (Homogenization.originCube d (m : ℤ)))
                              ((fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x))
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P •
                          (1 : Homogenization.Mat d)) ≤
                      delta *
                        (SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m
                            P)⁻¹ *
                        (m : ℝ) ^ expon * Real.log (m : ℝ))
    :=
  srootMS_minimal_scales_of_inputs d hE srootA_hThr (srootD_hOneScale d)

end
end SuperdiffusionCLT.Section4.MinimalScales
