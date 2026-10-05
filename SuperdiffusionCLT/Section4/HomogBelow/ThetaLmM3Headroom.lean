/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmAssemblyThresholds
public import SuperdiffusionCLT.Section4.HomogBelow.ThetaLmLNaughtGeLinear

/-!
**The `m₃`-side headroom fact** `2·M·L^α·log³L ≤ L − m₃`, matching the paper's "with
`M` replaced by `2M`" move in the proof of `p.homog.below`, via
an `M`-inflation step at inflation ratio `3` (rather than `2`): the extra unit of slack
(`c·M_thr ≥ 3M` instead of `≥ 2M`) is exactly what is needed to absorb the
`< 1` rounding loss of choosing `m₃` as the smallest natural clearing
`ThetaLmP3Prime.lean`'s own threshold `L − c·M_thr·L^α·log³L ≤ m₃` (a
`Nat.ceil`), once `L ≥ 3` (forced here via `ThetaLmLNaughtGeLinear.lean`'s
`homogBelow_lNaught_ge_linear`, giving `log L ≥ 1` hence `M·L^α·log³L ≥ 1`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory

private theorem homogBelow_inflate3_identity {c : ℝ} (hc : 0 < c) :
    min (1 : ℝ) (c / 3) * max (1 : ℝ) (3 / c) = 1 := by
  rcases le_or_gt c 3 with hle | hlt
  · have hmin : min (1 : ℝ) (c / 3) = c / 3 := min_eq_right (by linarith only [hle])
    have hmax : max (1 : ℝ) (3 / c) = 3 / c := by
      apply max_eq_right
      rw [le_div_iff₀ hc]
      linarith only [hle]
    rw [hmin, hmax]
    field_simp
  · have hmin : min (1 : ℝ) (c / 3) = 1 := by
      apply min_eq_left
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      linarith only [hlt]
    have hmax : max (1 : ℝ) (3 / c) = 1 := by
      apply max_eq_left
      rw [div_le_one₀ hc]
      linarith only [hlt]
    rw [hmin, hmax]; norm_num

private theorem homogBelow_c_mul_max3_ge3 {c : ℝ} (hc : 0 < c) :
    (3 : ℝ) ≤ c * max (1 : ℝ) (3 / c) := by
  rcases le_or_gt c 3 with hle | hlt
  · have hmax : max (1 : ℝ) (3 / c) = 3 / c := by
      apply max_eq_right
      rw [le_div_iff₀ hc]
      linarith only [hle]
    rw [hmax]
    have heq : c * (3 / c) = 3 := by field_simp
    linarith only [heq]
  · have hmax : max (1 : ℝ) (3 / c) = 1 := by
      apply max_eq_left
      rw [div_le_one₀ hc]
      linarith only [hlt]
    rw [hmax]
    linarith only [hlt]

/-- The `M`-inflation lemma at ratio `3` (at `3` instead of
`2`, and exposing the extra fact `3 ≤ c * max 1 (3/c)` a caller needs for the extra unit of
headroom). -/
theorem homogBelow_inflateM3
    {C M c alpha cStar nu K : ℝ} (hC0 : 0 ≤ C) (hM1 : 1 ≤ M) (hc : 0 < c)
    (halpha1 : alpha < 1) (hcStar : 0 < cStar) (hnu : 0 < nu) (hK : 0 ≤ K)
    {L : ℕ}
    (hL : SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ)) :
    1 ≤ M * max (1 : ℝ) (3 / c) ∧
    C * min (1 : ℝ) (c / 3) ≤ C ∧
    (3 : ℝ) ≤ c * max (1 : ℝ) (3 / c) ∧
    SuperdiffusionCLT.Frozen.Section4.lNaught (C * min (1 : ℝ) (c / 3))
        ((C * min (1 : ℝ) (c / 3)) * (M * max (1 : ℝ) (3 / c))) alpha cStar nu K ≤ (L : ℝ) := by
  have hmaxge1 : (1 : ℝ) ≤ max (1 : ℝ) (3 / c) := le_max_left _ _
  have hminle1 : min (1 : ℝ) (c / 3) ≤ 1 := min_le_left _ _
  have hminpos : (0 : ℝ) < min (1 : ℝ) (c / 3) := lt_min (by norm_num) (by linarith only [hc])
  refine ⟨?_, ?_, homogBelow_c_mul_max3_ge3 hc, ?_⟩
  · calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ M * max (1 : ℝ) (3 / c) := mul_le_mul hM1 hmaxge1 (by norm_num) (by linarith only [hM1])
  · calc C * min (1 : ℝ) (c / 3) ≤ C * 1 := mul_le_mul_of_nonneg_left hminle1 hC0
      _ = C := mul_one C
  · have hCthr0 : (0 : ℝ) ≤ C * min (1 : ℝ) (c / 3) := mul_nonneg hC0 hminpos.le
    have hCthrleC : C * min (1 : ℝ) (c / 3) ≤ C := by
      calc C * min (1 : ℝ) (c / 3) ≤ C * 1 := mul_le_mul_of_nonneg_left hminle1 hC0
        _ = C := mul_one C
    have hid : (C * min (1 : ℝ) (c / 3)) * (M * max (1 : ℝ) (3 / c)) = C * M := by
      have hidentity := homogBelow_inflate3_identity hc
      calc (C * min (1 : ℝ) (c / 3)) * (M * max (1 : ℝ) (3 / c))
          = (C * M) * (min (1 : ℝ) (c / 3) * max (1 : ℝ) (3 / c)) := by ring
        _ = (C * M) * 1 := by rw [hidentity]
        _ = C * M := mul_one _
    rw [hid]
    have hCM0 : (0 : ℝ) ≤ C * M := mul_nonneg hC0 (by linarith only [hM1])
    exact SuperdiffusionCLT.Section4.LNaught.lNaught_mono_const
      hCthr0 hCthrleC hCM0 hK hcStar hnu halpha1 |>.trans hL

/-- **The `m₃`-side headroom, and the four threshold facts of [AK, Theorem 6.1] it needs to
be applied at once**: given `d, Cmix`, produces a threshold `C1` (and a
fixed `c > 0`, `lNaught_sstar_lower`'s own witness) such that for every
outer `C ≥ C1` and every valid `(M, alpha, cStar, nu, K, L)` with
`L ≥ lNaught C (C*M) alpha cStar nu K`, there is a natural `m₃` for which
`ThetaLmP3Prime.lean`'s four threshold facts hold at `(c, M·max 1 (3/c))`,
`hm3ge` holds for this `m₃`, and `2·M·L^α·log³L ≤ L − m₃`. -/
theorem homogBelow_m3_headroom
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (Cmix : ℝ) (hCmix1 : 1 ≤ Cmix) :
    ∃ (C1 c : ℝ), 1 ≤ C1 ∧ 0 < c ∧ ∀ C : ℝ, C1 ≤ C →
      ∀ M alpha cStar nu K : ℝ, 1 ≤ M → 0 ≤ alpha → alpha < 1 →
        0 < cStar → cStar ≤ 2 → 0 < nu → nu ≤ 1 → 0 ≤ K →
      ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
        (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
        (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
        (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
        SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
      ∀ L : ℕ,
        SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤ (L : ℝ) →
        ∃ m3 : ℕ,
          (c * (M * max 1 (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
            (L : ℝ) / 2) ∧
          (∀ h : ℕ, (L : ℝ) ≤ 2 * (h : ℝ) → h ≤ L →
            c * (Cmix * (M * max 1 (3 / c))) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
              SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) ^ (2 : ℝ)) ∧
          (∀ n : ℕ,
            (L : ℝ) - c * (M * max 1 (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
              (n : ℝ) →
            Cmix * Real.log (nu⁻¹ * (L : ℝ)) ≤ (n : ℝ)) ∧
          (∀ n : ℕ,
            (L : ℝ) - c * (M * max 1 (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
              (n : ℝ) →
            Real.log (nu⁻¹ * (L : ℝ)) ≤ 2 * Real.log (nu⁻¹ * (n : ℝ))) ∧
          ((L : ℝ) - c * (M * max 1 (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
            (m3 : ℝ)) ∧
          (2 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) - (m3 : ℝ)) ∧
          (L / 2 ≤ m3) := by
  obtain ⟨c, C₀, hcpos, hC01, _hC0_Cmix, _hC0_c, hThreshBody⟩ :=
    homogBelow_thresholdHyps d hd Cmix hCmix1
  obtain ⟨Clin, _hClin1, hlin⟩ := homogBelow_lNaught_ge_linear
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2pow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  have hmnpos : (0 : ℝ) < min (1 : ℝ) (c / 3) := lt_min (by norm_num) (by linarith only [hcpos])
  refine ⟨max 1 (max (C₀ / min (1 : ℝ) (c / 3)) (max Clin (12 / (Real.log 2) ^ (12 : ℝ)))),
    c, le_max_left _ _, hcpos, ?_⟩
  intro C hC M alpha cStar nu K hM1 halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK
    P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hL
  have hC1' : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) hC
  have hCrest := le_trans (le_max_right (1 : ℝ) _) hC
  have hC0mn : C₀ / min (1 : ℝ) (c / 3) ≤ C := le_trans (le_max_left _ _) hCrest
  have hCClin : Clin ≤ C := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCrest
  have hC12 : 12 / (Real.log 2) ^ (12 : ℝ) ≤ C :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCrest
  have hC0nonneg : (0 : ℝ) ≤ C := le_trans zero_le_one hC1'
  -- Step (i): the inflation, at ratio 3.
  obtain ⟨hMthr1, _hCthrleC, hcMthrge3, hLthr⟩ := homogBelow_inflateM3
    (C := C) (M := M) (c := c) (alpha := alpha) (cStar := cStar) (nu := nu) (K := K)
    hC0nonneg hM1 hcpos halpha1 hcStar hnu hK hL
  -- Step (ii): C₀ ≤ Cthr.
  have hC0leCthr : C₀ ≤ C * min (1 : ℝ) (c / 3) := by
    have hstep : C₀ / min (1 : ℝ) (c / 3) * min (1 : ℝ) (c / 3) ≤ C * min (1 : ℝ) (c / 3) :=
      mul_le_mul_of_nonneg_right hC0mn hmnpos.le
    rwa [div_mul_cancel₀ C₀ hmnpos.ne'] at hstep
  -- Step (iii): the four threshold facts, at (c, Mthr).
  obtain ⟨hFact1, hFact2, hFact3, hFact4⟩ :=
    hThreshBody (C * min (1 : ℝ) (c / 3)) hC0leCthr (M * max (1 : ℝ) (3 / c)) alpha cStar nu K
      hMthr1 halpha0 halpha1 hcStar hcStar2 hnu hnu1 hK P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L hLthr
  -- Step (iv): L ≥ 3.
  have hCMge1 : (1 : ℝ) ≤ C * M := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ C * M := mul_le_mul hC1' hM1 (by norm_num) (by linarith only [hC1'])
  have hLge := hlin C hCClin (C * M) hCMge1 alpha halpha0 halpha1 cStar hcStar hcStar2
    nu hnu hnu1 K hK
  have hLgeReal : (Real.log 2) ^ (12 : ℝ) / 4 * C ≤ (L : ℝ) := le_trans hLge hL
  have hL3R : (3 : ℝ) ≤ (L : ℝ) := by
    have hstep : (12 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) * C := by
      rw [div_le_iff₀ hlog2pow_pos] at hC12
      nlinarith only [hC12]
    have hstep2 : (3 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) / 4 * C := by
      have heq : (Real.log 2) ^ (12 : ℝ) / 4 * C = (Real.log 2) ^ (12 : ℝ) * C / 4 := by ring
      rw [heq, le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      linarith only [hstep]
    linarith only [hstep2, hLgeReal]
  -- Step (v): log L ≥ 1, hence M·L^α·log³L ≥ 1.
  have hlogL_gt1 : (1 : ℝ) < Real.log (L : ℝ) := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hlt : Real.exp 1 < (L : ℝ) := lt_of_lt_of_le he3 hL3R
    have hh := Real.log_lt_log (Real.exp_pos 1) hlt
    rwa [Real.log_exp] at hh
  have hlogL1 : (1 : ℝ) ≤ Real.log (L : ℝ) := hlogL_gt1.le
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by linarith only [hL3R]
  have hLalpha_ge1 : (1 : ℝ) ≤ (L : ℝ) ^ alpha := Real.one_le_rpow hL1R halpha0
  have hlogcube_ge1 : (1 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (3 : ℝ) := (Real.one_rpow 3).symm
      _ ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow (by norm_num) hlogL1 (by norm_num)
  have hMLalpha_ge1 : (1 : ℝ) ≤ M * (L : ℝ) ^ alpha := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ M * (L : ℝ) ^ alpha := mul_le_mul hM1 hLalpha_ge1 zero_le_one (by linarith only [hM1])
  have hMLalphaLogCube_ge1 : (1 : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) :=
        mul_le_mul hMLalpha_ge1 hlogcube_ge1 zero_le_one (by linarith only [hMLalpha_ge1])
  -- Step (vi): m3 as the ceiling of the absorbed threshold at (c, Mthr).
  set m3 : ℕ :=
      ⌈(L : ℝ) - c * (M * max (1 : ℝ) (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)⌉₊
      with hm3def
  have hm3ge : (L : ℝ) - c * (M * max (1 : ℝ) (3 / c)) * (L : ℝ) ^ alpha *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤ (m3 : ℝ) := Nat.le_ceil _
  have hargnonneg : (0 : ℝ) ≤
      (L : ℝ) - c * (M * max (1 : ℝ) (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    linarith only [hFact1]
  have hm3lt : (m3 : ℝ) <
      ((L : ℝ) - c * (M * max (1 : ℝ) (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ))
        + 1 :=
    Nat.ceil_lt_add_one hargnonneg
  -- Step (vii): c·Mthr ≥ 3M.
  have hMnonneg : (0 : ℝ) ≤ M := by linarith only [hM1]
  have hcMthr_ge3M : 3 * M ≤ c * (M * max (1 : ℝ) (3 / c)) := by
    have h := mul_le_mul_of_nonneg_left hcMthrge3 hMnonneg
    calc 3 * M = M * 3 := by ring
      _ ≤ M * (c * max (1 : ℝ) (3 / c)) := h
      _ = c * (M * max (1 : ℝ) (3 / c)) := by ring
  have hLalphaLogCube_nonneg : (0 : ℝ) ≤ (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h1 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (by positivity) alpha
    have h2 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := by linarith only [hlogcube_ge1]
    exact mul_nonneg h1 h2
  have hcMthr_ge3M' : 3 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
      c * (M * max (1 : ℝ) (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hcMthr_ge3M hLalphaLogCube_nonneg
    calc 3 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) =
        (3 * M) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
      _ ≤ (c * (M * max (1 : ℝ) (3 / c))) * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := h
      _ = c * (M * max (1 : ℝ) (3 / c)) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by ring
  -- Step (viii): assemble the headroom.
  have hheadroom : 2 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) - (m3 : ℝ) := by
    have h1 : (m3 : ℝ) <
        (L : ℝ) - 3 * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) + 1 := by
      linarith only [hm3lt, hcMthr_ge3M']
    nlinarith only [h1, hMLalphaLogCube_ge1]
  -- The extra `L/2 ≤ m3` fact (it settles the `m2` bound):
  -- `hFact1`'s absorption bound and `hm3ge`'s lower bound on `m3` combine
  -- directly, with no dependence on an older (`M`, not `M_thr`)
  -- version of this fact.
  have hL2m3 : L / 2 ≤ m3 := by
    have hR : (L : ℝ) / 2 ≤ (m3 : ℝ) := by linarith only [hFact1, hm3ge]
    have hcast : ((L / 2 : ℕ) : ℝ) ≤ (L : ℝ) / 2 := Nat.cast_div_le
    exact_mod_cast le_trans hcast hR
  exact ⟨m3, hFact1, hFact2, hFact3, hFact4, hm3ge, hheadroom, hL2m3⟩

end SuperdiffusionCLT.Section4.HomogBelow
