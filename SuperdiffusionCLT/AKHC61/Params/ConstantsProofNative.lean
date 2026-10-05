/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.OneStepClosed

/-!
# Proof-native parameters of AK.HC Theorem 6.1, version 2 (package F1)

Proof of `t.weaker.P3` of [AK], Steps 1-2.

This file supersedes the Step 1 parameter choices of `Params/Constants.lean` where Step 2
(`Step2/OneStepB.lean`, `Step2/OneStepClosed.lean`) shows them to be unusable, and keeps
the rest (`akhcRhoPrime`, `akhcRho`, `akhcEta`).

* **Exponents.** `s′ := (1+ρ)/4`, `η := min{d+1, p_Ψ}`; `akhcStep2_ranges` proves every range
  package C6 (`akhcPrime_step2_thetaBound`) asks of `(s′, ρ, η)`.
* **`δ`.** `akhcStep2_delta := min{δ₀(d, K_w), 1/6400}` with `K_w := K(d,s′,ρ)(c_V+5)`,
  `c_V := 1 + 51d²(2d+4d²)` (node 30's closeness term, `Step2/LaunchB.lean`, divided by `δσ²`).
* **`L`.** The printed `L(σ,δ)` (`e.L.def.prime`) is replaced by `akhcStep2_Lreq … K`, the least
  natural number beyond the three decay thresholds node 40 actually needs when package C6 is
  applied at lag `ell := L` (the window fix, see `Step2/ElaborateLag.lean`), at top scale `K`:
  the window `2L₁ log(L₂K) + 4 ≤ L`, `3^{-(1-2s′)L} ≤ δσ²` (tightened node 26 for `hT1small`,
  which also gives `hT2small`), and the `(P2′)` part of `hMsmall`. Unlike the printed `L`, it
  carries no `1/(δσ²)` prefactor.
* **`m₀`.** `akhcStep2_m0Req` is a predicate on `m₀` itself (no `Nat.find`), with the corrected
  horizon `N′` (`akhcLaunchNprimeNat`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.ParamsProofNative

open SuperdiffusionCLT.AKHC61.Params

noncomputable section

/-! ## Exponents -/

/-- `s′ := (1+ρ)/4`, `ρ = (1+ρ′)/2` (`akhcRho`). -/
def akhcStep2_sPrime (d : ℕ) (gamma pPsi pPsiS : ℝ) : ℝ := (1 + akhcRho d gamma pPsi pPsiS) / 4

theorem akhcStep2_rhoPrime_lt_one {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ} (hgamma1 : gamma < 1)
    (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS) : akhcRhoPrime d gamma pPsi pPsiS < 1 := by
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [this]
  have hmin : (d : ℝ) < min ((d : ℝ) + 1) pPsi := lt_min (by linarith only) hpPsi
  have h1 : (d : ℝ) / min ((d : ℝ) + 1) pPsi < 1 := (div_lt_one (hd0.trans hmin)).2 hmin
  have hmin3 : (2 : ℝ) < min (3 : ℝ) pPsiS := lt_min (by norm_num) hpPsiS
  have h2 : 2 / min (3 : ℝ) pPsiS < 1 := (div_lt_one (by linarith only [hmin3])).2 hmin3
  exact max_lt hgamma1 (max_lt h1 h2)

theorem akhcStep2_gamma_le_rhoPrime (d : ℕ) (gamma pPsi pPsiS : ℝ) :
    gamma ≤ akhcRhoPrime d gamma pPsi pPsiS := le_max_left _ _

theorem akhcStep2_dEta_le_rhoPrime (d : ℕ) (gamma pPsi pPsiS : ℝ) :
    (d : ℝ) / akhcEta d pPsi ≤ akhcRhoPrime d gamma pPsi pPsiS :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- **Every range C6 asks of `(s′, ρ, η)`** (`akhcPrime_step2_thetaBound`'s `hlo hhi hgap
hgammarho heta2 hetaPsi hc`), for `s′ := (1+ρ)/4`, `η := min{d+1,p_Ψ}`. -/
theorem akhcStep2_ranges {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ} (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma < 1) (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS) :
    1 / 4 ≤ akhcStep2_sPrime d gamma pPsi pPsiS ∧ akhcStep2_sPrime d gamma pPsi pPsiS < 1 / 2 ∧
      akhcRho d gamma pPsi pPsiS / 2 < akhcStep2_sPrime d gamma pPsi pPsiS ∧
      gamma ≤ akhcRho d gamma pPsi pPsiS ∧ 2 < akhcEta d pPsi ∧ akhcEta d pPsi ≤ pPsi ∧
      0 < 2 * akhcRho d gamma pPsi pPsiS - 2 * (d : ℝ) / akhcEta d pPsi := by
  have hr1 := akhcStep2_rhoPrime_lt_one hd hgamma1 hpPsi hpPsiS
  have hgr := akhcStep2_gamma_le_rhoPrime d gamma pPsi pPsiS
  have hde := akhcStep2_dEta_le_rhoPrime d gamma pPsi pPsiS
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hrho : akhcRho d gamma pPsi pPsiS = (1 + akhcRhoPrime d gamma pPsi pPsiS) / 2 := rfl
  have hs : akhcStep2_sPrime d gamma pPsi pPsiS = (1 + akhcRho d gamma pPsi pPsiS) / 4 := rfl
  have heta : akhcEta d pPsi = min ((d : ℝ) + 1) pPsi := rfl
  have hdiv : 2 * (d : ℝ) / akhcEta d pPsi = 2 * ((d : ℝ) / akhcEta d pPsi) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, min_le_right _ _, ?_⟩
  · rw [hs, hrho]; linarith only [hgamma0, hgr]
  · rw [hs, hrho]; linarith only [hr1]
  · rw [hs, hrho]; linarith only [hr1]
  · rw [hrho]; linarith only [hgr, hr1]
  · rw [heta]; exact lt_min (by linarith only [hd2]) (by linarith only [hd2, hpPsi])
  · rw [hdiv, hrho]; linarith only [hde, hr1]

/-! ## `c_V`, `K_w`, `δ` -/

/-- `c_V := 1 + 51d²(2d+4d²)`: node 30's closeness term `51d²(2dδ₁+(2dδ₁)²) ≤ 51d²(2d+4d²)δ₁`
(for `δ₁ ≤ 1`), plus one unit for the `(P3′)` term. -/
def akhcStep2_cV (d : ℕ) : ℝ := 1 + 51 * (d : ℝ) ^ 2 * (2 * d + 4 * (d : ℝ) ^ 2)

theorem akhcStep2_cV_nonneg (d : ℕ) : 0 ≤ akhcStep2_cV d := by unfold akhcStep2_cV; positivity

/-- `K_w := K(d,s′,ρ)(c_V+5)` (C6's weak-norm constant). -/
def akhcStep2_Kw (d : ℕ) (gamma pPsi pPsiS : ℝ) : ℝ :=
  SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_Kst d (akhcStep2_sPrime d gamma pPsi pPsiS)
      (akhcRho d gamma pPsi pPsiS) * (akhcStep2_cV d + 5)

/-- `δ := min{δ₀(d,K_w), 1/6400}`. -/
def akhcStep2_delta (d : ℕ) [NeZero d] (gamma pPsi pPsiS : ℝ) : ℝ :=
  min (SuperdiffusionCLT.AKHC61.Step2.akhcOneDelta0 d (akhcStep2_Kw d gamma pPsi pPsiS))
    (6400 : ℝ)⁻¹

theorem akhcStep2_delta_le_delta0 (d : ℕ) [NeZero d] (gamma pPsi pPsiS : ℝ) :
    akhcStep2_delta d gamma pPsi pPsiS ≤
      SuperdiffusionCLT.AKHC61.Step2.akhcOneDelta0 d (akhcStep2_Kw d gamma pPsi pPsiS) :=
  min_le_left _ _

theorem akhcStep2_delta_le (d : ℕ) [NeZero d] (gamma pPsi pPsiS : ℝ) :
    akhcStep2_delta d gamma pPsi pPsiS ≤ (6400 : ℝ)⁻¹ := min_le_right _ _

theorem akhcStep2_delta_pos (d : ℕ) [NeZero d] (gamma pPsi pPsiS : ℝ) :
    0 < akhcStep2_delta d gamma pPsi pPsiS := by
  have hKst : 0 ≤ SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_Kst d
      (akhcStep2_sPrime d gamma pPsi pPsiS) (akhcRho d gamma pPsi pPsiS) := by
    unfold SuperdiffusionCLT.AKHC61.WeakNorms.akhcPrime_Kst
      SuperdiffusionCLT.AKHC61.WeakNorms.akhcWeakC2_maximizerConst
    positivity
  have hKw : 0 ≤ akhcStep2_Kw d gamma pPsi pPsiS :=
    mul_nonneg hKst (by linarith only [akhcStep2_cV_nonneg d])
  have hC := SuperdiffusionCLT.AKHC61.Step2.akhcOne_JBconst_ge_four d
  have hB : 0 < 1 + Real.sqrt (akhcStep2_Kw d gamma pPsi pPsiS) + akhcStep2_Kw d gamma pPsi pPsiS := by
    have := Real.sqrt_nonneg (akhcStep2_Kw d gamma pPsi pPsiS)
    linarith only [this, hKw]
  have h0 : 0 < SuperdiffusionCLT.AKHC61.Step2.akhcOneDelta0 d
      (akhcStep2_Kw d gamma pPsi pPsiS) := by
    unfold SuperdiffusionCLT.AKHC61.Step2.akhcOneDelta0
    have : 0 < 16 * SuperdiffusionCLT.AKHC61.Step2.akhcJB_const d *
        (1 + Real.sqrt (akhcStep2_Kw d gamma pPsi pPsiS) + akhcStep2_Kw d gamma pPsi pPsiS) :=
      mul_pos (by linarith only [hC]) hB
    positivity
  exact lt_min h0 (by norm_num)

/-! ## The needed `L` (tightened node 26) -/

/-- The three real thresholds `L` must exceed at top scale `K` (with `Y := δσ²`):
the window `2L₁ log(L₂K) + 4`, the `hT1small` threshold `log(1/Y)/((1-2s′) log 3)`, and the
`(P2′)`-tail threshold `log(6K_{Ψ_S}^{36}(HK^D)²/((min{3,p_{Ψ_S}}-2)Y))/((ρ-γ) log 3)`. -/
def akhcStep2_Lthreshold (d : ℕ) (gamma pPsi pPsiS L1 L2 H D KPsiS Y : ℝ) (K : ℕ) : ℝ :=
  max (max (2 * (L1 * Real.log (L2 * (K : ℝ))) + 4)
      (Real.log (1 / Y) / ((1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * Real.log 3)))
    (Real.log (6 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ) / ((min 3 pPsiS - 2) * Y)) /
      ((akhcRho d gamma pPsi pPsiS - gamma) * Real.log 3))

/-- `L_req(K) := ⌈threshold⌉ + 1`. -/
def akhcStep2_Lreq (d : ℕ) (gamma pPsi pPsiS L1 L2 H D KPsiS Y : ℝ) (K : ℕ) : ℕ :=
  ⌈akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K⌉₊ + 1

theorem akhcStep2_Lthreshold_le_Lreq (d : ℕ) (gamma pPsi pPsiS L1 L2 H D KPsiS Y : ℝ) (K : ℕ) :
    akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K ≤
      (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K : ℝ) := by
  unfold akhcStep2_Lreq
  push_cast
  have := Nat.le_ceil (akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K)
  linarith only [this]

/-- A threshold of the form `log(1/ε)/(c log 3) ≤ L` gives `3^{-cL} ≤ ε`. -/
theorem akhcStep2_rpow_le_of_div_le {c eps L : ℝ} (hc : 0 < c) (heps : 0 < eps)
    (hL : Real.log (1 / eps) / (c * Real.log 3) ≤ L) : (3 : ℝ) ^ (-(c * L)) ≤ eps := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < c * Real.log 3 := mul_pos hc hlog3
  have h1 : Real.log (1 / eps) ≤ L * (c * Real.log 3) := (div_le_iff₀ hden).1 hL
  exact SuperdiffusionCLT.AKHC61.Step2.akhcOneC_rpow_neg_le_of_log_le hc heps
    (by linarith only [h1])

section Lemmas

variable {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ} (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
  (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS)
  {L1 L2 H D KPsiS Y : ℝ} {K L : ℕ}

include hd hgamma0 hgamma1 hpPsi hpPsiS

/-- **Tightened node 26, `hT1small` part.** -/
theorem akhcStep2_T1_of_Lreq (hY : 0 < Y)
    (hL : akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K ≤ L) :
    (3 : ℝ) ^ (-((1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * (L : ℝ))) ≤ Y := by
  obtain ⟨-, hhi, -⟩ := akhcStep2_ranges hd hgamma0 hgamma1 hpPsi hpPsiS
  have hc : 0 < 1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS := by linarith only [hhi]
  have hLR : (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have hth := akhcStep2_Lthreshold_le_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K
  have hmax : Real.log (1 / Y) / ((1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * Real.log 3) ≤
      akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K :=
    (le_max_right _ _).trans (le_max_left _ _)
  exact akhcStep2_rpow_le_of_div_le hc hY (hmax.trans (hth.trans hLR))

/-- **Tightened node 26, `hT2small` part.** -/
theorem akhcStep2_T2_of_Lreq (hY : 0 < Y)
    (hL : akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K ≤ L) :
    (3 : ℝ) ^ (-(L : ℝ)) ≤ Y := by
  have h1 := akhcStep2_T1_of_Lreq hd hgamma0 hgamma1 hpPsi hpPsiS hY hL
  obtain ⟨hlo, -, -⟩ := akhcStep2_ranges hd hgamma0 hgamma1 hpPsi hpPsiS
  have hc1 : 1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS ≤ 1 := by linarith only [hlo]
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hmono : (3 : ℝ) ^ (-(L : ℝ)) ≤
      (3 : ℝ) ^ (-((1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * (L : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith only [hc1, hL0]
  exact hmono.trans h1

omit hd hgamma0 hgamma1 hpPsi hpPsiS in
/-- **Tightened node 26, window part.** -/
theorem akhcStep2_window_of_Lreq
    (hL : akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K ≤ L) :
    2 * (L1 * Real.log (L2 * (K : ℝ))) + 4 ≤ (L : ℝ) := by
  have hLR : (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have hth := akhcStep2_Lthreshold_le_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K
  have hmax : 2 * (L1 * Real.log (L2 * (K : ℝ))) + 4 ≤
      akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K :=
    (le_max_left _ _).trans (le_max_left _ _)
  linarith only [hmax, hth, hLR]

/-- **Tightened node 26, `(P2′)` part of `hMsmall`**:
`3K_{Ψ_S}^{36}(HK^D)²·3^{-(ρ-γ)L}/(min{3,p_{Ψ_S}}-2) ≤ Y/2`. -/
theorem akhcStep2_Mtail_of_Lreq (hY : 0 < Y) (hH : 1 ≤ H) (hKPsiS : 1 ≤ KPsiS)
    (hL : akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K ≤ L) :
    3 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ) *
        (3 : ℝ) ^ (-((akhcRho d gamma pPsi pPsiS - gamma) * (L : ℝ))) / (min 3 pPsiS - 2) ≤
      Y / 2 := by
  obtain ⟨-, -, -, hgr, -⟩ := akhcStep2_ranges hd hgamma0 hgamma1 hpPsi hpPsiS
  have hr1 := akhcStep2_rhoPrime_lt_one hd hgamma1 hpPsi hpPsiS
  have hgr' := akhcStep2_gamma_le_rhoPrime d gamma pPsi pPsiS
  have hrho : akhcRho d gamma pPsi pPsiS = (1 + akhcRhoPrime d gamma pPsi pPsiS) / 2 := rfl
  have hc : 0 < akhcRho d gamma pPsi pPsiS - gamma := by rw [hrho]; linarith only [hr1, hgr']
  have hmin : 0 < min (3 : ℝ) pPsiS - 2 := by
    have : (2 : ℝ) < min (3 : ℝ) pPsiS := lt_min (by norm_num) hpPsiS
    linarith only [this]
  have hK36 : (0 : ℝ) < KPsiS ^ 36 := by positivity
  have hHK : 0 ≤ (H * (K : ℝ) ^ D) ^ (2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (by linarith only [hH]) (Real.rpow_nonneg (Nat.cast_nonneg K) D)) _
  have hpow : 0 < (3 : ℝ) ^ (-((akhcRho d gamma pPsi pPsiS - gamma) * (L : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rcases hHK.lt_or_eq with hHKpos | hHKzero
  · set A : ℝ := 6 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ) with hAdef
    have hA : 0 < A := by rw [hAdef]; positivity
    have heps : 0 < (min 3 pPsiS - 2) * Y / A := by positivity
    have hLR : (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hL
    have hth := akhcStep2_Lthreshold_le_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K
    have hmax : Real.log (A / ((min 3 pPsiS - 2) * Y)) /
        ((akhcRho d gamma pPsi pPsiS - gamma) * Real.log 3) ≤
        akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K := le_max_right _ _
    have hinv : 1 / ((min 3 pPsiS - 2) * Y / A) = A / ((min 3 pPsiS - 2) * Y) := by
      rw [one_div, inv_div]
    have hthr : Real.log (1 / ((min 3 pPsiS - 2) * Y / A)) /
        ((akhcRho d gamma pPsi pPsiS - gamma) * Real.log 3) ≤ (L : ℝ) := by
      rw [hinv]; exact hmax.trans (hth.trans hLR)
    have hdecay := akhcStep2_rpow_le_of_div_le (L := (L : ℝ)) hc heps hthr
    have hstep : A * (3 : ℝ) ^ (-((akhcRho d gamma pPsi pPsiS - gamma) * (L : ℝ))) ≤
        (min 3 pPsiS - 2) * Y := by
      have := mul_le_mul_of_nonneg_left hdecay hA.le
      rwa [mul_div_cancel₀ _ hA.ne'] at this
    rw [div_le_iff₀ hmin]
    have hAeq : 3 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ) *
        (3 : ℝ) ^ (-((akhcRho d gamma pPsi pPsiS - gamma) * (L : ℝ))) =
        A * (3 : ℝ) ^ (-((akhcRho d gamma pPsi pPsiS - gamma) * (L : ℝ))) / 2 := by
      rw [hAdef]; ring
    rw [hAeq]
    have hY2 : Y / 2 * (min 3 pPsiS - 2) = (min 3 pPsiS - 2) * Y / 2 := by ring
    rw [hY2]
    linarith only [hstep]
  · rw [← hHKzero]
    have hz : 3 * KPsiS ^ 36 * (0 : ℝ) *
        (3 : ℝ) ^ (-((akhcRho d gamma pPsi pPsiS - gamma) * (L : ℝ))) / (min 3 pPsiS - 2) = 0 := by
      ring
    rw [hz]
    linarith only [hY]

end Lemmas

/-! ## The port's `Υ₁` and the `m₀` requirement -/

/-- **The port's `Υ₁`**: `ω_m²·Υ₁ ≤ δσ²` is exactly the `(P3′)`-smallness Step 2 needs, for node 30
(`akhcLaunch_variance_HC_prime` at `p_Ψ := η`, with `(1+δ₁)² ≤ 4`) and for the `(P3′)` part of
`hMsmall` (package C3). Compare the V3 anchor's `C K_Ψ^{4d²}/(min{d+1,p_Ψ}-d)`: the growth
condition at `η ∈ (d, d+1]` costs `K_Ψ^{3⌈η⌉²} = K_Ψ^{3(d+1)²}`. -/
def akhcStep2_Upsilon1 (d : ℕ) (gamma pPsi pPsiS KPsi : ℝ) : ℝ :=
  16 * (3 + 6 * (d : ℝ)) * (d : ℝ) ^ 2 *
      ((akhcEta d pPsi / (akhcEta d pPsi - 2)) * KPsi ^ (3 * ⌈akhcEta d pPsi⌉₊ ^ 2)) +
    2 * ((akhcEta d pPsi / (akhcEta d pPsi - 2)) * KPsi ^ (3 * ⌈akhcEta d pPsi⌉₊ ^ 2) *
      KPsi ^ (2 * (3 * (⌈akhcEta d pPsi⌉₊ : ℝ) ^ 2) / akhcEta d pPsi) *
      (1 - (3 : ℝ) ^ (-(2 * akhcRho d gamma pPsi pPsiS -
        2 * (d : ℝ) / akhcEta d pPsi)))⁻¹)

/-- **The Step 2 requirement on `m₀`** (corrected horizon `N′`, `L := L_req(m+3m₀)`,
`Y := δσ²`): `⌈log(3Θ₀)⌉·N′(L) ≤ m₀` and `2L < (1-β)m₀`. A predicate on `m₀` itself. -/
def akhcStep2_m0Req (d : ℕ) [NeZero d] (gamma pPsi pPsiS L1 L2 H D KPsiS beta sigma Theta0 : ℝ)
    (m m0 : ℕ) : Prop :=
  ⌈Real.log (3 * Theta0)⌉₊ *
      SuperdiffusionCLT.AKHC61.Step2.akhcLaunchNprimeNat
        (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS
          (akhcStep2_delta d gamma pPsi pPsiS * sigma ^ 2) (m + 3 * m0))
        (akhcStep2_delta d gamma pPsi pPsiS) sigma ≤ m0 ∧
    2 * (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS
          (akhcStep2_delta d gamma pPsi pPsiS * sigma ^ 2) (m + 3 * m0) : ℝ) <
      (1 - beta) * (m0 : ℝ)

end

end SuperdiffusionCLT.AKHC61.ParamsProofNative
