/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.LargeGapWideNumeric

/-!
# The `ν^{-4}L^2` numeric tail, one constant uniform in `ν, L, m`

The wide numeric tail (`LargeGapWideNumeric.lean`)
produces its `∃ C` witness via a case split on `L ≤ x` vs `L > x`
(`x := m - L`), returning a *different* closed-form `C(d,K)` in each branch.
Fixing the gap threshold to the canonical value `K₀(d) := 6100/(d log 3)`
(the minimal value this route needs) and taking the `max` of the two
branch constants gives a single `C(d)` valid on both branches, hence uniform
in every `ν, L, m` satisfying the (now `K₀`-fixed) gap hypothesis. This is
the only place in the `n > L` route where the
`n ≤ L` and `L < n` assemblies' witnesses come from a case split, so it is
proved once here, generic in the scale parameter `L` (used at `L := L` for
the `n ≤ L` branch and at `L := nn` for the `L < n` branch). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

noncomputable section

/-- **The `ν^{-4}L^2` numeric tail, one `d`-only constant, `K` fixed at the
canonical threshold `6100/(d log 3)`.** -/
theorem mixGapAbove_numericTail_uniform {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {nu : ℝ} {L m : ℕ}, 0 < nu → nu ≤ 1 → 1 ≤ L → 1 ≤ m →
        (6100 / ((d : ℝ) * Real.log 3)) * Real.log (nu⁻¹ * (L : ℝ)) ≤ (m : ℝ) - (L : ℝ) →
        nu ^ (-(4 : ℝ)) * (L : ℝ) ^ (2 : ℝ) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * ((m : ℝ) - (L : ℝ))) ≤
          C * (m : ℝ) ^ (-(3000 : ℝ)) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hd
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set K : ℝ := 6100 / ((d : ℝ) * Real.log 3) with hKdef
  have hK_pos : 0 < K := div_pos (by norm_num) (mul_pos hd_pos hlog3_pos)
  set γ : ℝ := (d : ℝ) / 2 * Real.log 3 with hγ_def
  have hγ_pos : 0 < γ := by rw [hγ_def]; positivity
  set c : ℝ := γ - 4 / K with hc_def
  have hKγ : K * γ = 3050 := by
    rw [hKdef, hγ_def]
    field_simp
    ring
  have heq_Kc : K * c = K * γ - 4 := by rw [hc_def]; field_simp
  have hKc : (3000 : ℝ) ≤ K * c := by rw [heq_Kc, hKγ]; norm_num
  have hc_pos : 0 < c := by
    have h4K : 4 / K < γ := by
      rw [div_lt_iff₀ hK_pos]
      nlinarith only [hKγ]
    rw [hc_def]; linarith only [h4K]
  set C1A : ℝ := 2 ^ (3000 : ℕ) * ((3000 : ℝ) / c) ^ (3000 : ℕ) with hC1Adef
  set C1B : ℝ := (2 : ℝ) ^ (c * K) with hC1Bdef
  have hC1A_nn : 0 ≤ C1A := by rw [hC1Adef]; positivity
  have hC1B_nn : 0 ≤ C1B := by rw [hC1Bdef]; positivity
  set Cmax : ℝ := max C1A C1B with hCmaxdef
  have hCmax_nn : 0 ≤ Cmax := le_trans hC1A_nn (le_max_left _ _)
  refine ⟨Cmax, hCmax_nn, ?_⟩
  intro nu L m hnu hnu1 hL hm1 hgap
  have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have harg1 : (1 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul hnuinv1 hLcast (by norm_num) (by linarith only [hnuinv1])
  have hlogarg_nonneg : (0 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := Real.log_nonneg harg1
  set x : ℝ := (m : ℝ) - (L : ℝ) with hx_def
  have hx_nonneg : (0 : ℝ) ≤ x := le_trans (mul_nonneg hK_pos.le hlogarg_nonneg) hgap
  -- Step 1: `ν^{-4} L^2 3^{-γx} ≤ exp(-cx)`.
  have hstepA : nu⁻¹ * (L : ℝ) ≤ Real.exp (x / K) := by
    have h1 : Real.log (nu⁻¹ * (L : ℝ)) ≤ x / K := by
      rw [le_div_iff₀ hK_pos]
      nlinarith only [hgap]
    calc nu⁻¹ * (L : ℝ) = Real.exp (Real.log (nu⁻¹ * (L : ℝ))) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (x / K) := Real.exp_le_exp.mpr h1
  have hnuinv_nonneg : (0 : ℝ) ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
  have hnuinv_le : nu⁻¹ ≤ Real.exp (x / K) / (L : ℝ) := by
    rw [le_div_iff₀ hL_pos]
    exact hstepA
  have hnu4L2 : nu⁻¹ ^ (4 : ℕ) * (L : ℝ) ^ (2 : ℕ) ≤ Real.exp (4 * (x / K)) := by
    have hb1 : nu⁻¹ ^ (4 : ℕ) ≤ (Real.exp (x / K) / (L : ℝ)) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hnuinv_nonneg hnuinv_le 4
    have hb2 : (Real.exp (x / K) / (L : ℝ)) ^ (4 : ℕ) =
        Real.exp (x / K) ^ (4 : ℕ) / (L : ℝ) ^ (4 : ℕ) := div_pow _ _ _
    rw [hb2] at hb1
    have hb3 : nu⁻¹ ^ (4 : ℕ) * (L : ℝ) ^ (2 : ℕ) ≤
        (Real.exp (x / K) ^ (4 : ℕ) / (L : ℝ) ^ (4 : ℕ)) * (L : ℝ) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hb1 (by positivity)
    have heq2 : (Real.exp (x / K) ^ (4 : ℕ) / (L : ℝ) ^ (4 : ℕ)) * (L : ℝ) ^ (2 : ℕ) =
        Real.exp (x / K) ^ (4 : ℕ) / (L : ℝ) ^ (2 : ℕ) := by
      rw [eq_div_iff (by positivity : ((L:ℝ)^(2:ℕ)) ≠ 0)]
      field_simp
    rw [heq2] at hb3
    have hLsq_ge1 : (1 : ℝ) ≤ (L : ℝ) ^ (2 : ℕ) := one_le_pow₀ hLcast
    have hexppow_nonneg : (0:ℝ) ≤ Real.exp (x/K) ^ (4:ℕ) := by positivity
    have hdiv_le : Real.exp (x / K) ^ (4 : ℕ) / (L : ℝ) ^ (2 : ℕ) ≤ Real.exp (x / K) ^ (4 : ℕ) :=
      div_le_self hexppow_nonneg hLsq_ge1
    refine hb3.trans (hdiv_le.trans (le_of_eq ?_))
    rw [← Real.exp_nat_mul]
    norm_num
  have hstep1 : nu ^ (-(4 : ℝ)) * (L : ℝ) ^ (2 : ℝ) *
      (3 : ℝ) ^ (-((d : ℝ) / 2) * x) ≤ Real.exp (-(c * x)) := by
    have hnupow : nu ^ (-(4:ℝ)) = nu⁻¹ ^ (4:ℕ) := by
      rw [show (-(4:ℝ)) = -((4:ℕ):ℝ) by norm_num, Real.rpow_neg hnu.le, Real.rpow_natCast,
        ← inv_pow]
    have hLpow : (L : ℝ) ^ (2 : ℝ) = (L : ℝ) ^ (2 : ℕ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have h3pow : (3 : ℝ) ^ (-((d : ℝ) / 2) * x) = Real.exp (-γ * x) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), hγ_def]
      ring_nf
    rw [hnupow, hLpow, h3pow]
    have hmulstep : nu⁻¹ ^ (4 : ℕ) * (L : ℝ) ^ (2 : ℕ) * Real.exp (-γ * x) ≤
        Real.exp (4 * (x / K)) * Real.exp (-γ * x) :=
      mul_le_mul_of_nonneg_right hnu4L2 (by positivity)
    refine hmulstep.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    rw [hc_def]
    field_simp
    ring
  -- Step 2: `m^{3000} ≤ Cmax * exp(cx)`, by a case split on `L ≤ x` vs `L > x`.
  have hstep2 : (m : ℝ) ^ (3000 : ℕ) ≤ Cmax * Real.exp (c * x) := by
    rcases le_or_gt (L : ℝ) x with hcase | hcase
    · -- `m = L + x ≤ 2x`.
      have hm2x : (m : ℝ) ≤ 2 * x := by
        have hmx : (m:ℝ) = (L:ℝ) + x := by rw [hx_def]; ring
        linarith only [hmx, hcase]
      have hmpow : (m : ℝ) ^ (3000 : ℕ) ≤ (2 * x) ^ (3000 : ℕ) :=
        pow_le_pow_left₀ hm_pos.le hm2x 3000
      have hxpow : x ^ (3000 : ℕ) * Real.exp (-(c * x)) ≤ ((3000 : ℝ) / c) ^ (3000 : ℕ) :=
        mixGap_pow_mul_exp_neg_le 3000 hc_pos hx_nonneg
      have hmul2x : (2 * x) ^ (3000 : ℕ) = 2 ^ (3000 : ℕ) * x ^ (3000 : ℕ) := mul_pow 2 x 3000
      rw [hmul2x] at hmpow
      have hexp_pos : (0:ℝ) < Real.exp (c * x) := Real.exp_pos _
      have hxb : x ^ (3000 : ℕ) ≤ ((3000 : ℝ) / c) ^ (3000 : ℕ) * Real.exp (c * x) := by
        have hstep0 := mul_le_mul_of_nonneg_right hxpow hexp_pos.le
        have heq1 : x ^ (3000:ℕ) * Real.exp (-(c*x)) * Real.exp (c*x) = x ^ (3000:ℕ) := by
          rw [mul_assoc, ← Real.exp_add]
          simp
        rwa [heq1] at hstep0
      have hfin : (2:ℝ) ^ (3000:ℕ) * x ^ (3000:ℕ) ≤ C1A * Real.exp (c*x) := by
        rw [hC1Adef, mul_assoc]
        exact mul_le_mul_of_nonneg_left hxb (by positivity)
      have hCle : C1A * Real.exp (c*x) ≤ Cmax * Real.exp (c*x) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hexp_pos.le
      exact hmpow.trans (hfin.trans hCle)
    · -- `L > x`, so `m/2 < L`.
      have hLgtm2 : (m : ℝ) / 2 < (L : ℝ) := by
        have hmx : (m:ℝ) = (L:ℝ) + x := by rw [hx_def]; ring
        linarith only [hmx, hcase]
      have hlogL_le : Real.log (L : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by
        apply Real.log_le_log hL_pos
        calc (L:ℝ) = 1 * (L:ℝ) := by ring
          _ ≤ nu⁻¹ * (L:ℝ) := mul_le_mul_of_nonneg_right hnuinv1 hL_pos.le
      have hx_ge : K * Real.log (L : ℝ) ≤ x := by
        have hmul := mul_le_mul_of_nonneg_left hlogL_le hK_pos.le
        linarith only [hmul, hgap]
      have hlog_m2_lt : Real.log ((m:ℝ)/2) < Real.log (L:ℝ) :=
        Real.log_lt_log (by positivity) hLgtm2
      have hx_gt : K * Real.log ((m:ℝ)/2) < x := by
        have hmul := mul_lt_mul_of_pos_left hlog_m2_lt hK_pos
        linarith only [hmul, hx_ge]
      have heq_logm2 : Real.log ((m:ℝ)/2) = Real.log (m:ℝ) - Real.log 2 := by
        rw [Real.log_div hm_pos.ne' (by norm_num)]
      rw [heq_logm2] at hx_gt
      have hcx_gt : c * K * (Real.log (m:ℝ) - Real.log 2) ≤ c * x := by
        have hmul := mul_le_mul_of_nonneg_left hx_gt.le hc_pos.le
        nlinarith only [hmul]
      have hm_cK : (m:ℝ) ^ (c*K) = Real.exp (c*K*Real.log (m:ℝ)) := by
        rw [Real.rpow_def_of_pos hm_pos]; ring_nf
      have h2_cK : (2:ℝ) ^ (c*K) = Real.exp (c*K*Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; ring_nf
      have h2cK_pos : (0:ℝ) < (2:ℝ) ^ (c*K) := Real.rpow_pos_of_pos (by norm_num) _
      have hexp_ge : (m:ℝ) ^ (c*K) ≤ (2:ℝ) ^ (c*K) * Real.exp (c * x) := by
        rw [hm_cK, h2_cK, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith only [hcx_gt]
      have hKc' : (3000:ℝ) ≤ c * K := by nlinarith only [hKc]
      have hm_ge1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hm_mono : (m:ℝ) ^ (3000:ℝ) ≤ (m:ℝ) ^ (c*K) :=
        Real.rpow_le_rpow_of_exponent_le hm_ge1 hKc'
      have hm3000_eq : (m:ℝ) ^ (3000:ℕ) = (m:ℝ) ^ (3000:ℝ) := by
        rw [show (3000:ℝ) = ((3000:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      have hexp_pos : (0:ℝ) < Real.exp (c * x) := Real.exp_pos _
      have hCle : (2:ℝ) ^ (c*K) * Real.exp (c*x) ≤ Cmax * Real.exp (c*x) :=
        mul_le_mul_of_nonneg_right (hC1Bdef ▸ le_max_right C1A C1B) hexp_pos.le
      rw [hm3000_eq]
      exact hm_mono.trans (hexp_ge.trans hCle)
  have hm3000_pos : (0:ℝ) < (m:ℝ) ^ (3000:ℕ) := by positivity
  have hm3000eq2 : (m:ℝ) ^ (-(3000:ℝ)) = ((m:ℝ) ^ (3000:ℕ))⁻¹ := by
    rw [Real.rpow_neg hm_pos.le, show (3000:ℝ) = ((3000:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hexp_pos : (0:ℝ) < Real.exp (c*x) := Real.exp_pos _
  have hstepD : (Real.exp (c*x))⁻¹ ≤ Cmax / (m:ℝ) ^ (3000:ℕ) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hexp_pos hm3000_pos]
    linarith only [hstep2]
  calc nu ^ (-(4:ℝ)) * (L:ℝ) ^ (2:ℝ) * (3:ℝ) ^ (-((d:ℝ)/2) * x)
      ≤ Real.exp (-(c*x)) := hstep1
    _ = (Real.exp (c*x))⁻¹ := by rw [← Real.exp_neg]
    _ ≤ Cmax / (m:ℝ) ^ (3000:ℕ) := hstepD
    _ = Cmax * (m:ℝ) ^ (-(3000:ℝ)) := by rw [hm3000eq2, div_eq_mul_inv]

end

end SuperdiffusionCLT.Section4.Mixing
