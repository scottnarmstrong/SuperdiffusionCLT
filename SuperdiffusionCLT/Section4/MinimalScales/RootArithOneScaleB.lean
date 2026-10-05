/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.RootArithOneScale
public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section4.NewMixing.LogGrowth

/-!
# Arithmetic input `hOneScale` for `srootMS_minimal_scales_of_inputs` — tail floors

In the proof of `p.minimal.scales`
(`e.new.mixing.minscale.one.scale`), this file proves the two
tail-parameter floor conjuncts `1 ≤ T1`, `1 ≤ T2` of `hOneScale`'s body. The remaining
(hardest) conjunct, the big union-bound inequality, is proved in
`RootArithOneScaleD.lean` and `RootArithOneScaleE.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open SuperdiffusionCLT.Section4.LNaught
open SuperdiffusionCLT.Section4.NewMixing
open SuperdiffusionCLT.Frozen.Section4 (lNaught)

noncomputable section

/-! ## Coefficient identities: unfolding `K = C M s⁻¹` inside `det`/`A1` -/

/-- `s⁻¹ = s ^ (-(1:ℝ))` for `s > 0`. -/
theorem srootA2_inv_eq_rpow {s : ℝ} (hs : 0 < s) : s⁻¹ = s ^ (-(1 : ℝ)) := by
  rw [Real.rpow_neg hs.le, Real.rpow_one]

/-- `(C*M*s⁻¹)^(1/2) = C^(1/2) * M^(1/2) * s^(-(1/2))` for `C,M ≥ 0`, `s>0`. -/
theorem srootA2_K_rpow_half {C M s : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hs : 0 < s) :
    (C * M * s⁻¹) ^ ((1 : ℝ) / 2) = C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((1 : ℝ) / 2)) := by
  rw [srootA2_inv_eq_rpow hs, Real.mul_rpow (mul_nonneg hC hM) (Real.rpow_nonneg hs.le _),
    Real.mul_rpow hC hM, ← Real.rpow_mul hs.le]
  norm_num

/-- `srootMS_det CE s (C*M*s⁻¹) sig m = CE * C^(1/2) * M^(1/2) * s⁻¹ * sig⁻¹ * log m`. -/
theorem srootA2_det_eq (CE C M s sig : ℝ) (m : ℕ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hs : 0 < s) :
    srootMS_det CE s (C * M * s⁻¹) sig m =
      CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ * sig⁻¹ * Real.log (m : ℝ) := by
  have hss : s ^ (-((1 : ℝ) / 2)) * s ^ (-((1 : ℝ) / 2)) = s⁻¹ := by
    rw [← Real.rpow_add hs, srootA2_inv_eq_rpow hs]
    norm_num
  unfold srootMS_det
  rw [srootA2_K_rpow_half hC hM hs]
  calc CE * s ^ (-((1 : ℝ) / 2)) *
        (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((1 : ℝ) / 2))) * sig⁻¹ *
        Real.log (m : ℝ)
      = CE * (s ^ (-((1 : ℝ) / 2)) * s ^ (-((1 : ℝ) / 2))) * C ^ ((1 : ℝ) / 2) *
          M ^ ((1 : ℝ) / 2) * sig⁻¹ * Real.log (m : ℝ) := by ring
    _ = CE * s⁻¹ * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * sig⁻¹ * Real.log (m : ℝ) := by
        rw [hss]
    _ = CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ * sig⁻¹ * Real.log (m : ℝ) := by ring

/-- `srootMS_A1 CE s (C*M*s⁻¹) sig m = CE * C^(1/2) * M^(1/2) * s^(-3/2) * sig⁻¹ * (log m)^(1/2)`. -/
theorem srootA2_A1_eq (CE C M s sig : ℝ) (m : ℕ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hs : 0 < s) :
    srootMS_A1 CE s (C * M * s⁻¹) sig m =
      CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) * sig⁻¹ *
        Real.log (m : ℝ) ^ ((1 : ℝ) / 2) := by
  have hss : s⁻¹ * s ^ (-((1 : ℝ) / 2)) = s ^ (-((3 : ℝ) / 2)) := by
    rw [srootA2_inv_eq_rpow hs, ← Real.rpow_add hs]
    norm_num
  unfold srootMS_A1
  rw [srootA2_K_rpow_half hC hM hs]
  calc CE * s⁻¹ * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((1 : ℝ) / 2))) * sig⁻¹ *
        Real.log (m : ℝ) ^ ((1 : ℝ) / 2)
      = CE * (s⁻¹ * s ^ (-((1 : ℝ) / 2))) * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * sig⁻¹ *
          Real.log (m : ℝ) ^ ((1 : ℝ) / 2) := by ring
    _ = CE * s ^ (-((3 : ℝ) / 2)) * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * sig⁻¹ *
          Real.log (m : ℝ) ^ ((1 : ℝ) / 2) := by rw [hss]
    _ = CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) * sig⁻¹ *
          Real.log (m : ℝ) ^ ((1 : ℝ) / 2) := by ring

/-! ## The `R'` bound: `L₀`-threshold, `cStar`-bound and a `delta`-multiply combined -/

/-- `delta * delta^(-2) = delta^(-1)` for `delta > 0`. -/
theorem srootA2_delta_mul_rpow_neg2 {delta : ℝ} (hdel0 : 0 < delta) :
    delta * delta ^ (-(2 : ℝ)) = delta ^ (-(1 : ℝ)) := by
  nth_rewrite 1 [← Real.rpow_one delta]
  rw [← Real.rpow_add hdel0]
  norm_num

/-- **`R'` bounds `delta · m^expon` from below**: from the `L₀`-threshold
comparison `hthr` (the first conjunct of `LNaught.Threshold.lNaught_threshold`,
already evaluated at `alpha := 1 - expon`, `L := m`), using `cStar^(-3) ≥ 1/8`
(from `cStar ≤ 2`) and multiplying by `delta > 0`. -/
theorem srootA2_Rprime_le_delta_mexpon {C expon delta s M cStar nu : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hexp0 : 0 < expon) (hdel0 : 0 < delta) (hs0 : 0 < s) (hM0 : 0 ≤ M)
    (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hlogm0 : 0 ≤ Real.log (m : ℝ))
    (hthr : (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) *
        cStar ^ (-(3 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) ≤ (m : ℝ) ^ expon) :
    (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) * nu ^ (-(4 : ℝ)) *
        Real.log (m : ℝ) ^ (12 : ℝ) ≤ delta * (m : ℝ) ^ expon := by
  have hcpow : (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := newMixParam_cStar_neg3_ge hcStar hcStar2
  have hApos : 0 ≤ C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by positivity
  have hrest_nn : 0 ≤ nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) := by
    have h1 : 0 ≤ nu ^ (-(4 : ℝ)) := Real.rpow_nonneg hnu.le _
    have h2 : 0 ≤ Real.log (m : ℝ) ^ (12 : ℝ) := Real.rpow_nonneg hlogm0 _
    positivity
  have hdd : delta * delta ^ (-(2 : ℝ)) = delta ^ (-(1 : ℝ)) := srootA2_delta_mul_rpow_neg2 hdel0
  have hkey : delta * ((C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * (1 / 8) *
      (nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ))) ≤ delta * (m : ℝ) ^ expon := by
    apply mul_le_mul_of_nonneg_left _ hdel0.le
    calc (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * (1 / 8) *
          (nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ))
        ≤ (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * cStar ^ (-(3 : ℝ)) *
            (nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcpow hApos) hrest_nn
      _ = (C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * cStar ^ (-(3 : ℝ)) *
            nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) := by ring
      _ ≤ (m : ℝ) ^ expon := hthr
  have heq : (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
      nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) =
      delta * ((C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * (1 / 8) *
        (nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ))) := by
    rw [show delta * ((C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * (1 / 8) *
          (nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ))) =
        (delta * delta ^ (-(2 : ℝ))) * (C * expon⁻¹ * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) * (1 / 8) *
          (nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ))) from by ring, hdd]
    ring
  linarith only [hkey, heq.le, heq.ge]

/-! ## The four `≥1`/`≥2` slack factors, combined -/

/-- The product of the four slack factors (`expon⁻¹ > 2`, `delta^{-1} ≥ 1`,
`nu^{-4} ≥ 1`, `(log m)^{12} ≥ 1`) is at least `2`. -/
theorem srootA2_slack_ge_two {expon delta nu : ℝ} {m : ℕ}
    (hexp0 : 0 < expon) (hexp1 : expon < 1 / 2) (hdel0 : 0 < delta) (hdel1 : delta ≤ 1)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hlogm1 : 1 ≤ Real.log (m : ℝ)) :
    (2 : ℝ) ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) := by
  have hexpinv2 : (2 : ℝ) < expon⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hexp0]; linarith only [hexp1]
  have hdelinv1 : (1 : ℝ) ≤ delta ^ (-(1 : ℝ)) := by
    rw [← srootA2_inv_eq_rpow hdel0]
    exact (one_le_inv₀ hdel0).2 hdel1
  have hnu4le1 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hnu4pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hnuinv1 : (1 : ℝ) ≤ nu ^ (-(4 : ℝ)) := by
    rw [Real.rpow_neg hnu.le]
    exact (one_le_inv₀ hnu4pos).2 hnu4le1
  have hlog12ge1 : (1 : ℝ) ≤ Real.log (m : ℝ) ^ (12 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (12 : ℝ) := (Real.one_rpow _).symm
      _ ≤ Real.log (m : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow (by norm_num) hlogm1 (by norm_num)
  have hexpinv_nn : (0 : ℝ) ≤ expon⁻¹ := le_trans (by norm_num) hexpinv2.le
  have hdelinv_nn : (0 : ℝ) ≤ delta ^ (-(1 : ℝ)) := le_trans zero_le_one hdelinv1
  have hnuinv_nn : (0 : ℝ) ≤ nu ^ (-(4 : ℝ)) := le_trans zero_le_one hnuinv1
  calc (2 : ℝ) = 2 * 1 * 1 * 1 := by norm_num
    _ ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) := by
        gcongr

/-- The product of the four slack factors (`expon⁻¹ > 2`, `delta^{-1} ≥ 1`,
`s^{-4} ≥ 1`, `M^2 ≥ 1`, `(log m)^{12} ≥ 1`) with `nu` omitted is at least `2`. -/
theorem srootA2_slack_ge_two_nu {expon delta s M : ℝ} {m : ℕ}
    (hexp0 : 0 < expon) (hexp1 : expon < 1 / 2) (hdel0 : 0 < delta) (hdel1 : delta ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hM1 : 1 ≤ M) (hlogm1 : 1 ≤ Real.log (m : ℝ)) :
    (2 : ℝ) ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
      Real.log (m : ℝ) ^ (12 : ℝ) := by
  have hexpinv2 : (2 : ℝ) < expon⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hexp0]; linarith only [hexp1]
  have hdelinv1 : (1 : ℝ) ≤ delta ^ (-(1 : ℝ)) := by
    rw [← srootA2_inv_eq_rpow hdel0]
    exact (one_le_inv₀ hdel0).2 hdel1
  have hsinv1 : (1 : ℝ) ≤ s ^ (-(4 : ℝ)) := by
    have hs4le1 : s ^ (4 : ℝ) ≤ 1 := by
      calc s ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hs0.le hs1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have hs4pos : (0 : ℝ) < s ^ (4 : ℝ) := Real.rpow_pos_of_pos hs0 _
    rw [Real.rpow_neg hs0.le]
    exact (one_le_inv₀ hs4pos).2 hs4le1
  have hM2ge1 : (1 : ℝ) ≤ M ^ (2 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (2 : ℝ) := (Real.one_rpow _).symm
      _ ≤ M ^ (2 : ℝ) := Real.rpow_le_rpow (by norm_num) hM1 (by norm_num)
  have hlog12ge1 : (1 : ℝ) ≤ Real.log (m : ℝ) ^ (12 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (12 : ℝ) := (Real.one_rpow _).symm
      _ ≤ Real.log (m : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow (by norm_num) hlogm1 (by norm_num)
  have hexpinv_nn : (0 : ℝ) ≤ expon⁻¹ := le_trans (by norm_num) hexpinv2.le
  have hdelinv_nn : (0 : ℝ) ≤ delta ^ (-(1 : ℝ)) := le_trans zero_le_one hdelinv1
  have hsinv_nn : (0 : ℝ) ≤ s ^ (-(4 : ℝ)) := le_trans zero_le_one hsinv1
  have hM2_nn : (0 : ℝ) ≤ M ^ (2 : ℝ) := le_trans zero_le_one hM2ge1
  calc (2 : ℝ) = 2 * 1 * 1 * 1 * 1 := by norm_num
    _ ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
          Real.log (m : ℝ) ^ (12 : ℝ) := by
        gcongr

/-! ## `delta · m^expon` dominates `(C/4)·s^{-4}·M²` and `(C/4)·ν^{-4}` -/

/-- `delta * m^expon ≥ (C/4) * s^{-4} * M^2`, from `R'` and the four-factor
slack (keeping `s^{-4} M^2`). -/
theorem srootA2_delta_mexpon_ge_Mslot {C expon delta s M nu : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hs0 : 0 < s) (hM0 : 0 ≤ M)
    (hslack : (2 : ℝ) ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ)) *
      Real.log (m : ℝ) ^ (12 : ℝ))
    (hR : (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
        nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) ≤ delta * (m : ℝ) ^ expon) :
    (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) ≤ delta * (m : ℝ) ^ expon := by
  have hX_nn : (0 : ℝ) ≤ (C / 8) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by positivity
  have hchain : (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) ≤
      (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) * nu ^ (-(4 : ℝ)) *
        Real.log (m : ℝ) ^ (12 : ℝ) := by
    have heq1 : (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
        nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) =
        ((C / 8) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) *
          (expon⁻¹ * delta ^ (-(1 : ℝ)) * nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ)) := by
      ring
    have heq2 : (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) =
        ((C / 8) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) * 2 := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left hslack hX_nn
  linarith only [hchain, hR]

/-- `delta * m^expon ≥ (C/4) * ν^{-4}`, from `R'` and the four-factor slack
(keeping `ν^{-4}`). -/
theorem srootA2_delta_mexpon_ge_nu {C expon delta s M nu : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hnu : 0 < nu)
    (hslack : (2 : ℝ) ≤ expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
      Real.log (m : ℝ) ^ (12 : ℝ))
    (hR : (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
        nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) ≤ delta * (m : ℝ) ^ expon) :
    (C / 4) * nu ^ (-(4 : ℝ)) ≤ delta * (m : ℝ) ^ expon := by
  have hY_nn : (0 : ℝ) ≤ (C / 8) * nu ^ (-(4 : ℝ)) := by positivity
  have hchain : (C / 4) * nu ^ (-(4 : ℝ)) ≤
      (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) * nu ^ (-(4 : ℝ)) *
        Real.log (m : ℝ) ^ (12 : ℝ) := by
    have heq1 : (C / 8) * expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
        nu ^ (-(4 : ℝ)) * Real.log (m : ℝ) ^ (12 : ℝ) =
        ((C / 8) * nu ^ (-(4 : ℝ))) *
          (expon⁻¹ * delta ^ (-(1 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) *
            Real.log (m : ℝ) ^ (12 : ℝ)) := by
      ring
    have heq2 : (C / 4) * nu ^ (-(4 : ℝ)) = ((C / 8) * nu ^ (-(4 : ℝ))) * 2 := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left hslack hY_nn
  linarith only [hchain, hR]

/-! ## The `C ≥ 144 CE²` threshold gives `C^{1/2} ≥ 12 CE` -/

/-- `C^{1/2} ≥ 12 CE` from `C ≥ 144 CE²` (`CE ≥ 1`, so `12 CE ≥ 0`). -/
theorem srootA2_sqrtC_ge_twelveCE {C CE : ℝ} (hCE1 : 1 ≤ CE) (hC144 : 144 * (CE * CE) ≤ C) :
    12 * CE ≤ C ^ ((1 : ℝ) / 2) := by
  have h1 : (12 * CE) * (12 * CE) ≤ C := by nlinarith only [hC144]
  have h2 : ((12 * CE) * (12 * CE)) ^ ((1 : ℝ) / 2) ≤ C ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h3 : ((12 * CE) * (12 * CE)) ^ ((1 : ℝ) / 2) = 12 * CE := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_mul_self (by nlinarith only [hCE1])
  linarith only [h2, h3.ge, h3.le]

/-- **The key algebra inequality for `T1`'s floor**:
`3 CE C^{1/2} M^{1/2} s^{-3/2} ≤ (C/4) s^{-4} M²`, once `C ≥ 144 CE²`. -/
theorem srootA2_key_ineq_T1 {C M s CE : ℝ}
    (hCE1 : 1 ≤ CE) (hC144 : 144 * (CE * CE) ≤ C) (hM1 : 1 ≤ M) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    3 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) ≤
      (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by
  have hCpos : (0 : ℝ) < C := by nlinarith only [hC144, hCE1]
  have hMpos : (0 : ℝ) < M := by linarith only [hM1]
  have hsqrtC : 12 * CE ≤ C ^ ((1 : ℝ) / 2) := srootA2_sqrtC_ge_twelveCE hCE1 hC144
  have hM32ge1 : (1 : ℝ) ≤ M ^ ((3 : ℝ) / 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 2) := (Real.one_rpow _).symm
      _ ≤ M ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hM1 (by norm_num)
  have hs52ge1 : (1 : ℝ) ≤ s ^ (-((5 : ℝ) / 2)) := by
    have hs52le1 : s ^ ((5 : ℝ) / 2) ≤ 1 := by
      calc s ^ ((5 : ℝ) / 2) ≤ (1 : ℝ) ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow hs0.le hs1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have hs52pos : (0 : ℝ) < s ^ ((5 : ℝ) / 2) := Real.rpow_pos_of_pos hs0 _
    rw [Real.rpow_neg hs0.le]
    exact (one_le_inv₀ hs52pos).2 hs52le1
  have hX_nn : (0 : ℝ) ≤ C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) := by
    positivity
  have hcoef : 3 * CE ≤ C ^ ((1 : ℝ) / 2) / 4 := by linarith only [hsqrtC]
  have hslackprod : (1 : ℝ) ≤ M ^ ((3 : ℝ) / 2) * s ^ (-((5 : ℝ) / 2)) := by
    nlinarith only [hM32ge1, hs52ge1]
  have hRHS_nn : (0 : ℝ) ≤
      (C ^ ((1 : ℝ) / 2) / 4) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) := by
    positivity
  have hstep4 : (C ^ ((1 : ℝ) / 2) / 4) *
      (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) *
      (M ^ ((3 : ℝ) / 2) * s ^ (-((5 : ℝ) / 2))) = (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by
    have e1 : C ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) = C := by
      rw [← Real.rpow_add hCpos]; norm_num
    have e2 : M ^ ((1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2) = M ^ (2 : ℝ) := by
      rw [← Real.rpow_add hMpos]; norm_num
    have e3 : s ^ (-((3 : ℝ) / 2)) * s ^ (-((5 : ℝ) / 2)) = s ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_add hs0]; norm_num
    calc (C ^ ((1 : ℝ) / 2) / 4) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) *
          (M ^ ((3 : ℝ) / 2) * s ^ (-((5 : ℝ) / 2)))
        = (C ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) / 4 * (M ^ ((1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2)) *
            (s ^ (-((3 : ℝ) / 2)) * s ^ (-((5 : ℝ) / 2))) := by ring
      _ = C / 4 * M ^ (2 : ℝ) * s ^ (-(4 : ℝ)) := by rw [e1, e2, e3]
      _ = (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by ring
  calc 3 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))
      = (3 * CE) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) := by ring
    _ ≤ (C ^ ((1 : ℝ) / 2) / 4) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_right hcoef hX_nn
    _ ≤ (C ^ ((1 : ℝ) / 2) / 4) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2))) *
          (M ^ ((3 : ℝ) / 2) * s ^ (-((5 : ℝ) / 2))) :=
        le_mul_of_one_le_right hRHS_nn hslackprod
    _ = (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := hstep4

/-- **The key algebra inequality for `Δ(m)`'s floor**:
`CE C^{1/2} M^{1/2} s^{-1} ≤ (C/12) s^{-4} M²`, once `C ≥ 144 CE²`. -/
theorem srootA2_key_ineq_delta {C M s CE : ℝ}
    (hCE1 : 1 ≤ CE) (hC144 : 144 * (CE * CE) ≤ C) (hM1 : 1 ≤ M) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ)) ≤
      (C / 12) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by
  have hCpos : (0 : ℝ) < C := by nlinarith only [hC144, hCE1]
  have hMpos : (0 : ℝ) < M := by linarith only [hM1]
  have hsqrtC : 12 * CE ≤ C ^ ((1 : ℝ) / 2) := srootA2_sqrtC_ge_twelveCE hCE1 hC144
  have hM32ge1 : (1 : ℝ) ≤ M ^ ((3 : ℝ) / 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((3 : ℝ) / 2) := (Real.one_rpow _).symm
      _ ≤ M ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hM1 (by norm_num)
  have hs3ge1 : (1 : ℝ) ≤ s ^ (-(3 : ℝ)) := by
    have hs3le1 : s ^ (3 : ℝ) ≤ 1 := by
      calc s ^ (3 : ℝ) ≤ (1 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow hs0.le hs1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have hs3pos : (0 : ℝ) < s ^ (3 : ℝ) := Real.rpow_pos_of_pos hs0 _
    rw [Real.rpow_neg hs0.le]
    exact (one_le_inv₀ hs3pos).2 hs3le1
  have hX_nn : (0 : ℝ) ≤ C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ)) := by positivity
  have hcoef : CE ≤ C ^ ((1 : ℝ) / 2) / 12 := by linarith only [hsqrtC]
  have hslackprod : (1 : ℝ) ≤ M ^ ((3 : ℝ) / 2) * s ^ (-(3 : ℝ)) := by
    nlinarith only [hM32ge1, hs3ge1]
  have hRHS_nn : (0 : ℝ) ≤
      (C ^ ((1 : ℝ) / 2) / 12) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ))) := by
    positivity
  have hstep4 : (C ^ ((1 : ℝ) / 2) / 12) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ))) *
      (M ^ ((3 : ℝ) / 2) * s ^ (-(3 : ℝ))) = (C / 12) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by
    have e1 : C ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) = C := by
      rw [← Real.rpow_add hCpos]; norm_num
    have e2 : M ^ ((1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2) = M ^ (2 : ℝ) := by
      rw [← Real.rpow_add hMpos]; norm_num
    have e3 : s ^ (-(1 : ℝ)) * s ^ (-(3 : ℝ)) = s ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_add hs0]; norm_num
    calc (C ^ ((1 : ℝ) / 2) / 12) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ))) *
          (M ^ ((3 : ℝ) / 2) * s ^ (-(3 : ℝ)))
        = (C ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) / 12 * (M ^ ((1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2)) *
            (s ^ (-(1 : ℝ)) * s ^ (-(3 : ℝ))) := by ring
      _ = C / 12 * M ^ (2 : ℝ) * s ^ (-(4 : ℝ)) := by rw [e1, e2, e3]
      _ = (C / 12) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by ring
  calc CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ))
      = CE * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ))) := by ring
    _ ≤ (C ^ ((1 : ℝ) / 2) / 12) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcoef hX_nn
    _ ≤ (C ^ ((1 : ℝ) / 2) / 12) * (C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ))) *
          (M ^ ((3 : ℝ) / 2) * s ^ (-(3 : ℝ))) :=
        le_mul_of_one_le_right hRHS_nn hslackprod
    _ = (C / 12) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := hstep4

/-! ## Assembling `Δ(m) ≥ (2/3) δ m^ρ`, `Δ(m) ≥ 2 CE C^{1/2} M^{1/2} s^{-3/2}`, and `T1 ≥ 1` -/

/-- `Δ(m) := delta·m^expon − CE·C^{1/2}·M^{1/2}·s⁻¹ ≥ (2/3)·delta·m^expon`, from
`Bound1` (`delta·m^expon ≥ (C/4)s^{-4}M²`) and `srootA2_key_ineq_delta`. -/
theorem srootA2_Delta_ge_two_thirds {C expon delta s M CE : ℝ} {m : ℕ}
    (hs0 : 0 < s)
    (hBound1 : (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) ≤ delta * (m : ℝ) ^ expon)
    (hKey2 : CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-(1 : ℝ)) ≤
        (C / 12) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) :
    (2 / 3) * (delta * (m : ℝ) ^ expon) ≤
      delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ := by
  rw [← srootA2_inv_eq_rpow hs0] at hKey2
  have heq : (C / 12) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) =
      (1 / 3) * ((C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ)) := by ring
  linarith only [hBound1, hKey2, heq.le, heq.ge]

/-- `Δ(m) ≥ 2 CE C^{1/2} M^{1/2} s^{-3/2}`, from `Bound1`, `srootA2_key_ineq_T1`
and `srootA2_Delta_ge_two_thirds`. -/
theorem srootA2_Delta_ge_T1bound {C expon delta s M CE : ℝ} {m : ℕ}
    (hBound1 : (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) ≤ delta * (m : ℝ) ^ expon)
    (hKeyT1 : 3 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) ≤
        (C / 4) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ))
    (hDeltaBound : (2 / 3) * (delta * (m : ℝ) ^ expon) ≤
        delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :
    2 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) ≤
      delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ := by
  linarith only [hBound1, hKeyT1, hDeltaBound]

/-- `target − det = sig⁻¹ · log m · (delta·m^expon − CE·C^{1/2}·M^{1/2}·s⁻¹)`. -/
theorem srootA2_target_sub_det_eq {CE C M s delta sig expon : ℝ} (m : ℕ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hs : 0 < s) :
    srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m =
      sig⁻¹ * Real.log (m : ℝ) *
        (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) := by
  unfold srootMS_target
  rw [srootA2_det_eq CE C M s sig m hC hM hs]
  ring

/-- `x^{1/2} ≤ x` for `x ≥ 1`. -/
theorem srootA2_sqrt_le_self {x : ℝ} (hx1 : 1 ≤ x) : x ^ ((1 : ℝ) / 2) ≤ x := by
  have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ) / 2 ≤ 1 by norm_num)
  rwa [Real.rpow_one] at h

/-- **The first floor of `hOneScale`**: `1 ≤ T1`. -/
theorem srootA2_T1_ge_one {CE C M s delta sig expon : ℝ} {m : ℕ}
    (hCpos : 0 < C) (hMpos : 0 < M) (hs0 : 0 < s) (hsig0 : 0 < sig) (hCE1 : 1 ≤ CE)
    (hlogm1 : 1 ≤ Real.log (m : ℝ))
    (hDeltaT1 : 2 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) ≤
        delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :
    1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
        (2 * srootMS_A1 CE s (C * M * s⁻¹) sig m) := by
  have hCEpos : 0 < CE := lt_of_lt_of_le one_pos hCE1
  have hlogmpos : 0 < Real.log (m : ℝ) := lt_of_lt_of_le one_pos hlogm1
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := hlogmpos.le
  have hsub_eq := srootA2_target_sub_det_eq (CE := CE) (C := C) (M := M) (s := s) (delta := delta)
    (sig := sig) (expon := expon) m hCpos.le hMpos.le hs0
  have hA1_eq := srootA2_A1_eq CE C M s sig m hCpos.le hMpos.le hs0
  have hA1pos : 0 < srootMS_A1 CE s (C * M * s⁻¹) sig m := by rw [hA1_eq]; positivity
  have hDpos : 0 < 2 * srootMS_A1 CE s (C * M * s⁻¹) sig m := by linarith only [hA1pos]
  have hsiginv_nn : 0 ≤ sig⁻¹ := (inv_pos.2 hsig0).le
  have hX_nn : 0 ≤ CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) := by
    positivity
  have hDelta_nn : 0 ≤ delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ := by
    linarith only [hDeltaT1, hX_nn]
  have hsqrtle : Real.log (m : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.log (m : ℝ) :=
    srootA2_sqrt_le_self hlogm1
  have hsqrt_nn : 0 ≤ Real.log (m : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hlogm0 _
  have hstepA : 2 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) *
      Real.log (m : ℝ) ^ ((1 : ℝ) / 2) ≤
      (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) *
        Real.log (m : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hDeltaT1 hsqrt_nn
  have hstepB : (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) *
      Real.log (m : ℝ) ^ ((1 : ℝ) / 2) ≤
      (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) *
        Real.log (m : ℝ) :=
    mul_le_mul_of_nonneg_left hsqrtle hDelta_nn
  have hstepAB : 2 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) *
      Real.log (m : ℝ) ^ ((1 : ℝ) / 2) ≤
      (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) *
        Real.log (m : ℝ) :=
    le_trans hstepA hstepB
  have hstepC : sig⁻¹ * (2 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) *
      Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) ≤
      sig⁻¹ * ((delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) *
        Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hstepAB hsiginv_nn
  have hLHSeq : 2 * srootMS_A1 CE s (C * M * s⁻¹) sig m =
      sig⁻¹ * (2 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) *
        Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) := by rw [hA1_eq]; ring
  have hRHSeq : sig⁻¹ * ((delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) *
      s⁻¹) * Real.log (m : ℝ)) =
      srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m := by
    rw [hsub_eq]; ring
  rw [le_div_iff₀ hDpos, one_mul]
  calc 2 * srootMS_A1 CE s (C * M * s⁻¹) sig m
      = sig⁻¹ * (2 * CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s ^ (-((3 : ℝ) / 2)) *
          Real.log (m : ℝ) ^ ((1 : ℝ) / 2)) := hLHSeq
    _ ≤ sig⁻¹ * ((delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) *
          Real.log (m : ℝ)) := hstepC
    _ = srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m := hRHSeq

/-! ## `T2 ≥ 1` -/

/-- `sig⁻¹ ≥ ν/(2 Cg m)`, from `sig ≤ Cg ν⁻¹ (1+m)` and `m ≥ 1`. -/
theorem srootA2_siginv_ge {Cg nu sig : ℝ} {m : ℕ}
    (hCg1 : 1 ≤ Cg) (hnu : 0 < nu) (hsig0 : 0 < sig) (hm1 : 1 ≤ (m : ℝ))
    (hsigle : sig ≤ Cg * nu⁻¹ * (1 + (m : ℝ))) :
    nu / (2 * Cg * (m : ℝ)) ≤ sig⁻¹ := by
  have hCgpos : 0 < Cg := lt_of_lt_of_le one_pos hCg1
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le one_pos hm1
  have h1m2m : 1 + (m : ℝ) ≤ 2 * (m : ℝ) := by linarith only [hm1]
  have hstep : Cg * nu⁻¹ * (1 + (m : ℝ)) ≤ Cg * nu⁻¹ * (2 * (m : ℝ)) :=
    mul_le_mul_of_nonneg_left h1m2m (by positivity)
  have hsigle2 : sig ≤ 2 * Cg * nu⁻¹ * (m : ℝ) := by nlinarith only [hsigle, hstep]
  have hnusig : nu * sig ≤ 2 * Cg * (m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsigle2 hnu.le
    have heq : nu * (2 * Cg * nu⁻¹ * (m : ℝ)) = 2 * Cg * (m : ℝ) := by field_simp
    linarith only [h, heq.le, heq.ge]
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hsig0]
  linarith only [hnusig]

/-- **The second floor of `hOneScale`**: `1 ≤ T2`. -/
theorem srootA2_T2_ge_one {CE C M s delta sig expon Cg nu : ℝ} {m : ℕ}
    (hCpos : 0 < C) (hMpos : 0 < M) (hs0 : 0 < s) (hsig0 : 0 < sig) (hCE1 : 1 ≤ CE)
    (hCg1 : 1 ≤ Cg) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hm1 : 1 ≤ (m : ℝ))
    (hlogm1 : 1 ≤ Real.log (m : ℝ)) (hsigle : sig ≤ Cg * nu⁻¹ * (1 + (m : ℝ)))
    (hC24CgCE : 24 * Cg * CE ≤ C)
    (hDeltaNu : (C / 6) * nu ^ (-(4 : ℝ)) ≤
        delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :
    1 ≤ (srootMS_target delta sig expon m - srootMS_det CE s (C * M * s⁻¹) sig m) /
        (2 * srootMS_A2 CE m) := by
  have hCEpos : 0 < CE := lt_of_lt_of_le one_pos hCE1
  have hCgpos : 0 < Cg := lt_of_lt_of_le one_pos hCg1
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le one_pos hm1
  have hlogmpos : 0 < Real.log (m : ℝ) := lt_of_lt_of_le one_pos hlogm1
  have hsub_eq := srootA2_target_sub_det_eq (CE := CE) (C := C) (M := M) (s := s) (delta := delta)
    (sig := sig) (expon := expon) m hCpos.le hMpos.le hs0
  have hA2pos : 0 < srootMS_A2 CE m := by
    unfold srootMS_A2
    have : 0 < (m : ℝ) ^ (-(1000 : ℝ)) := Real.rpow_pos_of_pos hmpos _
    positivity
  have hDpos : 0 < 2 * srootMS_A2 CE m := by linarith only [hA2pos]
  have hsiginv_ge : nu / (2 * Cg * (m : ℝ)) ≤ sig⁻¹ :=
    srootA2_siginv_ge hCg1 hnu hsig0 hm1 hsigle
  have hDelta_nn : 0 ≤ delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ := by
    have hnu4_nn : 0 ≤ (C / 6) * nu ^ (-(4 : ℝ)) := by positivity
    linarith only [hDeltaNu, hnu4_nn]
  have hnusiginv_nn : 0 ≤ nu / (2 * Cg * (m : ℝ)) := by positivity
  have hstepA : nu / (2 * Cg * (m : ℝ)) * ((C / 6) * nu ^ (-(4 : ℝ))) ≤
      sig⁻¹ * (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) := by
    have h1 : nu / (2 * Cg * (m : ℝ)) * ((C / 6) * nu ^ (-(4 : ℝ))) ≤
        nu / (2 * Cg * (m : ℝ)) *
          (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :=
      mul_le_mul_of_nonneg_left hDeltaNu hnusiginv_nn
    have h2 : nu / (2 * Cg * (m : ℝ)) *
        (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) ≤
        sig⁻¹ * (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :=
      mul_le_mul_of_nonneg_right hsiginv_ge hDelta_nn
    exact le_trans h1 h2
  have hnup : nu * nu ^ (-(4 : ℝ)) = nu ^ (-(3 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one nu]
    rw [← Real.rpow_add hnu]; norm_num
  have hmm : (m : ℝ) ^ (-(1000 : ℝ)) * (m : ℝ) ^ (1 : ℝ) = (m : ℝ) ^ (-(999 : ℝ)) := by
    rw [← Real.rpow_add hmpos]; norm_num
  have hm1eq : (m : ℝ) ^ (1 : ℝ) = (m : ℝ) := Real.rpow_one _
  have hm999le1 : (m : ℝ) ^ (-(999 : ℝ)) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ (m : ℝ) ^ (999 : ℝ) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (999 : ℝ) := (Real.one_rpow _).symm
        _ ≤ (m : ℝ) ^ (999 : ℝ) := Real.rpow_le_rpow (by norm_num) hm1 (by norm_num)
    have h2 : (0 : ℝ) < (m : ℝ) ^ (999 : ℝ) := lt_of_lt_of_le one_pos h1
    rw [Real.rpow_neg hmpos.le]
    exact (inv_le_one₀ h2).2 h1
  have hnu3ge1 : (1 : ℝ) ≤ nu ^ (-(3 : ℝ)) := by
    have h1 : nu ^ (3 : ℝ) ≤ 1 := by
      calc nu ^ (3 : ℝ) ≤ (1 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
        _ = 1 := Real.one_rpow _
    have h2 : (0 : ℝ) < nu ^ (3 : ℝ) := Real.rpow_pos_of_pos hnu _
    rw [Real.rpow_neg hnu.le]
    exact (one_le_inv₀ h2).2 h1
  have hbase : 2 * CE * (m : ℝ) ^ (-(1000 : ℝ)) ≤
      nu / (2 * Cg * (m : ℝ)) * ((C / 6) * nu ^ (-(4 : ℝ))) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Cg * (m : ℝ))]
    calc 2 * CE * (m : ℝ) ^ (-(1000 : ℝ)) * (2 * Cg * (m : ℝ))
        = 4 * CE * Cg * ((m : ℝ) ^ (-(1000 : ℝ)) * (m : ℝ) ^ (1 : ℝ)) := by rw [hm1eq]; ring
      _ = 4 * CE * Cg * (m : ℝ) ^ (-(999 : ℝ)) := by rw [hmm]
      _ ≤ 4 * CE * Cg * 1 := by
          have hnn : (0 : ℝ) ≤ 4 * CE * Cg := by positivity
          nlinarith only [hm999le1, hnn]
      _ = 4 * CE * Cg := by ring
      _ ≤ C / 6 := by linarith only [hC24CgCE]
      _ ≤ (C / 6) * nu ^ (-(3 : ℝ)) := by
          have hC6nn : (0 : ℝ) ≤ C / 6 := by positivity
          nlinarith only [hnu3ge1, hC6nn]
      _ = nu * ((C / 6) * nu ^ (-(4 : ℝ))) := by rw [← hnup]; ring
  have hnumeric : 2 * CE * (m : ℝ) ^ (-(1000 : ℝ)) ≤
      sig⁻¹ * (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :=
    le_trans hbase hstepA
  have hA2eq : 2 * srootMS_A2 CE m = 2 * CE * (m : ℝ) ^ (-(1000 : ℝ)) := by
    unfold srootMS_A2; ring
  rw [le_div_iff₀ hDpos, one_mul, hA2eq, hsub_eq]
  have heqfinal : sig⁻¹ * Real.log (m : ℝ) *
      (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) =
      Real.log (m : ℝ) *
        (sig⁻¹ * (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹)) := by
    ring
  rw [heqfinal]
  have hsiginvDelta_nn : 0 ≤
      sig⁻¹ * (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :=
    le_trans (by positivity : (0:ℝ) ≤ 2 * CE * (m : ℝ) ^ (-(1000 : ℝ))) hnumeric
  calc 2 * CE * (m : ℝ) ^ (-(1000 : ℝ))
      ≤ sig⁻¹ * (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹) :=
        hnumeric
    _ ≤ Real.log (m : ℝ) *
          (sig⁻¹ * (delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹)) :=
        le_mul_of_one_le_left hsiginvDelta_nn hlogm1

/-! ## Wiring facts: `Δ(m) ≥ (C/6) ν^{-4}` and `1 ≤ log m` -/

/-- `Δ(m) ≥ (C/6) ν^{-4}`, from `Δ(m) ≥ (2/3) δ m^ρ` and `Bound2`
(`δ m^ρ ≥ (C/4) ν^{-4}`). -/
theorem srootA2_Delta_ge_nu {C expon delta s M CE nu : ℝ} {m : ℕ}
    (hDeltaTwoThirds : (2 / 3) * (delta * (m : ℝ) ^ expon) ≤
        delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹)
    (hBound2 : (C / 4) * nu ^ (-(4 : ℝ)) ≤ delta * (m : ℝ) ^ expon) :
    (C / 6) * nu ^ (-(4 : ℝ)) ≤
      delta * (m : ℝ) ^ expon - CE * C ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 2) * s⁻¹ := by
  have heq : (C / 6) * nu ^ (-(4 : ℝ)) = (2 / 3) * ((C / 4) * nu ^ (-(4 : ℝ))) := by ring
  linarith only [hDeltaTwoThirds, hBound2, heq.le, heq.ge]

/-- `1 ≤ log m`, from `4 log 3 ≤ Lhat2 ≤ m` (`Lhat2`'s leading conjunct,
`srootA_hOneScale_fourLog3`, and the hypothesis `Lhat2 ≤ m`). -/
theorem srootA2_logm_ge_one {Lh : ℝ} {m : ℕ} (hLh4log3 : 4 * Real.log 3 ≤ Lh)
    (hLhm : Lh ≤ (m : ℝ)) : 1 ≤ Real.log (m : ℝ) := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hm3 : (3 : ℝ) < (m : ℝ) := by linarith only [hLh4log3, hLhm, hlog3]
  have hlogm : Real.log 3 < Real.log (m : ℝ) := Real.log_lt_log (by norm_num) hm3
  linarith only [hlog3, hlogm]

/-- `4 < m`, from `4 log 3 ≤ Lhat2 ≤ m`. -/
theorem srootA2_m_gt_four {Lh : ℝ} {m : ℕ} (hLh4log3 : 4 * Real.log 3 ≤ Lh)
    (hLhm : Lh ≤ (m : ℝ)) : (4 : ℝ) < (m : ℝ) := by
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  linarith only [hLh4log3, hLhm, hlog3]

/-- `1 ≤ C expon⁻¹ delta^{-2} s^{-4} M²` (the `M`-slot of `Lhat2`'s first
`L₀` term is always `≥ 1`), for `C ≥ 1`, `0 < expon`, `0 < delta ≤ 1`,
`0 < s ≤ 1`, `1 ≤ M`. -/
theorem srootA2_Mprime_ge_one {C expon delta s M : ℝ}
    (hC1 : 1 ≤ C) (hexp0 : 0 < expon) (hexp1 : expon < 1) (hdel0 : 0 < delta) (hdel1 : delta ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hM : 1 ≤ M) :
    (1 : ℝ) ≤ C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by
  have hexpinv1 : (1 : ℝ) ≤ expon⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hexp0]; nlinarith only [hexp1]
  have hdelta2 : (1 : ℝ) ≤ delta ^ (-(2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hdel0 hdel1
      (show (-(2 : ℝ)) ≤ (0 : ℝ) by norm_num)
    rwa [Real.rpow_zero] at h
  have hs4 : (1 : ℝ) ≤ s ^ (-(4 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hs0 hs1
      (show (-(4 : ℝ)) ≤ (0 : ℝ) by norm_num)
    rwa [Real.rpow_zero] at h
  have hM2 : (1 : ℝ) ≤ M ^ (2 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (2 : ℝ) := (Real.one_rpow _).symm
      _ ≤ M ^ (2 : ℝ) := Real.rpow_le_rpow (by norm_num) hM (by norm_num)
  calc (1 : ℝ) = 1 * 1 * 1 * 1 * 1 := by norm_num
    _ ≤ C * expon⁻¹ * delta ^ (-(2 : ℝ)) * s ^ (-(4 : ℝ)) * M ^ (2 : ℝ) := by
        gcongr

end
end SuperdiffusionCLT.Section4.MinimalScales
