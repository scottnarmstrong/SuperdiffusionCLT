/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Params.ConstantsProofNative

/-!
# Growth of the cutoff requirement in `akhcStep2_m0Req`

`akhcStep2_m0Req` (`Params/ConstantsProofNative.lean`) is the Step 2 requirement on the launch delay `m₀`
that `akhcStep2_step_two` (`Step2/StepTwo.lean`) and hence `akhcF1_core` (`Core.lean`) carry as a
hypothesis. Its defining display is self-referential: it bounds the cutoff
`L := akhcStep2_Lreq … (m + 3*m₀)` (whose top scale is `m + 3*m₀`, so it grows with `m₀` itself)
against `m₀`. This file supplies the estimate that makes such a requirement satisfiable for all
large `m₀`: `L` grows only like `log(m₀)`, since `akhcStep2_Lthreshold`'s three terms are each an
affine function of `log K` at fixed parameters, while the two requirements in `akhcStep2_m0Req` ask
for a multiple of `L` to be at most linear terms in `m₀`.

## Main results

* `akhcStep2Sat_Lthreshold_le`: `akhcStep2_Lthreshold` is bounded by an affine function of `log K`
  with `K`-independent coefficients.
* `akhcStep2Sat_Lreq_le`: `akhcStep2_Lreq` inherits the same affine bound, up to an additive `2`.
* `akhcStep2Sat_rhogamma_pos`, `akhcStep2Sat_c3_pos`, `akhcStep2Sat_bracket0_nonneg`,
  `akhcStep2Sat_Ccoef_nonneg`: nonnegativity of the coefficients of that affine bound.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.ParamsProofNative

open SuperdiffusionCLT.AKHC61.Params

noncomputable section

/-! ## Pure real-arithmetic domination (A4's `log x ≤ 2√x` pattern, copied from
`Params/Constants.lean` since the originals are `private`, then generalized to a
`∀ n ≥ threshold` statement instead of a single `Nat.find`-style witness). -/

/-! ## An upper bound for `akhcStep2_Lthreshold`, affine in `log K` -/

/-- `c₃ := 1/((ρ-γ)·log 3)`: the reciprocal rate of the `(P2′)`-tail threshold term. -/
def akhcStep2Sat_c3 (d : ℕ) (gamma pPsi pPsiS : ℝ) : ℝ :=
  1 / ((akhcRho d gamma pPsi pPsiS - gamma) * Real.log 3)

/-- The `K`-independent part of `akhcStep2_Lthreshold`'s third term, before dividing by
`(ρ-γ)·log 3`. -/
def akhcStep2Sat_bracket0 (KPsiS H pPsiS Y : ℝ) : ℝ :=
  Real.log 6 + 36 * Real.log KPsiS + 2 * Real.log H - Real.log (min 3 pPsiS - 2) - Real.log Y

/-- The `K`-independent part of `akhcStep2_Lthreshold`'s second term (node 26's `hT1small`
threshold). -/
def akhcStep2Sat_T1val (d : ℕ) (gamma pPsi pPsiS Y : ℝ) : ℝ :=
  Real.log (1 / Y) / ((1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * Real.log 3)

/-- The constant term of the affine-in-`log K` bound on `akhcStep2_Lthreshold`. -/
def akhcStep2Sat_Cconst (d : ℕ) (gamma pPsi pPsiS L1 L2 H KPsiS Y : ℝ) : ℝ :=
  (2 * L1 * Real.log L2 + 4) + akhcStep2Sat_T1val d gamma pPsi pPsiS Y +
    akhcStep2Sat_c3 d gamma pPsi pPsiS * akhcStep2Sat_bracket0 KPsiS H pPsiS Y

/-- The `log K` coefficient of the affine bound on `akhcStep2_Lthreshold`. -/
def akhcStep2Sat_Ccoef (d : ℕ) (gamma pPsi pPsiS L1 D : ℝ) : ℝ :=
  2 * L1 + 2 * D * akhcStep2Sat_c3 d gamma pPsi pPsiS

section LthresholdBound

variable {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ} (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
  (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS)
  {L1 L2 H D KPsiS Y : ℝ} (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hKPsiS : 1 ≤ KPsiS) (hYpos : 0 < Y) (hYlt1 : Y < 1)

include hd hgamma0 hgamma1 hpPsi hpPsiS hL1 hL2 hH hD hKPsiS hYpos hYlt1

/-- **`akhcStep2_Lthreshold` is bounded by an affine function of `log K`**, for `K ≥ 1`, with
`K`-independent coefficients `akhcStep2Sat_Cconst`, `akhcStep2Sat_Ccoef`. -/
theorem akhcStep2Sat_Lthreshold_le {K : ℕ} (hK1 : 1 ≤ K) :
    akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K ≤
      akhcStep2Sat_Cconst d gamma pPsi pPsiS L1 L2 H KPsiS Y +
        akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D * Real.log (K : ℝ) := by
  have hL1pos : 0 < L1 := by linarith only [hL1]
  have hL2pos : 0 < L2 := by linarith only [hL2]
  have hHpos : 0 < H := by linarith only [hH]
  have hKPsiSpos : 0 < KPsiS := by linarith only [hKPsiS]
  have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hKRpos : 0 < (K : ℝ) := by linarith only [hK1R]
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hminlt : (2 : ℝ) < min (3 : ℝ) pPsiS := lt_min (by norm_num) hpPsiS
  have hminpos : 0 < min (3 : ℝ) pPsiS - 2 := by linarith only [hminlt]
  have hminle1 : min (3 : ℝ) pPsiS - 2 ≤ 1 := by
    have := min_le_left (3 : ℝ) pPsiS; linarith only [this]
  have hr1 := akhcStep2_rhoPrime_lt_one hd hgamma1 hpPsi hpPsiS
  have hgr' := akhcStep2_gamma_le_rhoPrime d gamma pPsi pPsiS
  have hrhodef : akhcRho d gamma pPsi pPsiS = (1 + akhcRhoPrime d gamma pPsi pPsiS) / 2 := rfl
  have hrhogamma : 0 < akhcRho d gamma pPsi pPsiS - gamma := by
    rw [hrhodef]; linarith only [hr1, hgr']
  have hc3pos : 0 < akhcStep2Sat_c3 d gamma pPsi pPsiS :=
    div_pos one_pos (mul_pos hrhogamma hlog3pos)
  obtain ⟨-, hhi, -⟩ := akhcStep2_ranges hd hgamma0 hgamma1 hpPsi hpPsiS
  have hsdenpos : 0 < (1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * Real.log 3 :=
    mul_pos (by linarith only [hhi]) hlog3pos
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK1R
  have hL1logL2 : 0 ≤ 2 * L1 * Real.log L2 := by
    have hlogL2nn := Real.log_nonneg hL2
    have h2 : (0 : ℝ) ≤ 2 * L1 := by linarith only [hL1]
    exact mul_nonneg h2 hlogL2nn
  have hL1logK : 0 ≤ 2 * L1 * Real.log (K : ℝ) := by
    have h1 : (0 : ℝ) ≤ 2 * L1 := by linarith only [hL1]
    exact mul_nonneg h1 hlogK
  have hinvY : (1 : ℝ) ≤ 1 / Y := by
    rw [le_div_iff₀ hYpos]; linarith only [hYlt1]
  have hT1nonneg : 0 ≤ akhcStep2Sat_T1val d gamma pPsi pPsiS Y := by
    unfold akhcStep2Sat_T1val
    exact div_nonneg (Real.log_nonneg hinvY) hsdenpos.le
  have hb1 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  have hb2 : 0 ≤ 36 * Real.log KPsiS := by
    have := Real.log_nonneg hKPsiS; linarith only [this]
  have hb3 : 0 ≤ 2 * Real.log H := by
    have := Real.log_nonneg hH; linarith only [this]
  have hb4 : Real.log (min (3 : ℝ) pPsiS - 2) ≤ 0 := Real.log_nonpos hminpos.le hminle1
  have hb5 : Real.log Y ≤ 0 := Real.log_nonpos hYpos.le hYlt1.le
  have hbracket0nonneg : 0 ≤ akhcStep2Sat_bracket0 KPsiS H pPsiS Y := by
    unfold akhcStep2Sat_bracket0; linarith only [hb1, hb2, hb3, hb4, hb5]
  have hc3bracket0 : 0 ≤ akhcStep2Sat_c3 d gamma pPsi pPsiS * akhcStep2Sat_bracket0 KPsiS H pPsiS Y :=
    mul_nonneg hc3pos.le hbracket0nonneg
  have hDc3logK : 0 ≤ 2 * D * akhcStep2Sat_c3 d gamma pPsi pPsiS * Real.log (K : ℝ) := by
    have h1 : (0 : ℝ) ≤ 2 * D := by linarith only [hD]
    have h2 : 0 ≤ 2 * D * akhcStep2Sat_c3 d gamma pPsi pPsiS := mul_nonneg h1 hc3pos.le
    exact mul_nonneg h2 hlogK
  have hCcoefeq : akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D * Real.log (K : ℝ) =
      2 * L1 * Real.log (K : ℝ) + 2 * D * akhcStep2Sat_c3 d gamma pPsi pPsiS * Real.log (K : ℝ) := by
    unfold akhcStep2Sat_Ccoef; ring
  -- Term 1 (window)
  have hlogL2K : Real.log (L2 * (K : ℝ)) = Real.log L2 + Real.log (K : ℝ) :=
    Real.log_mul hL2pos.ne' hKRpos.ne'
  have hTerm1eq : 2 * (L1 * Real.log (L2 * (K : ℝ))) + 4 =
      2 * L1 * Real.log L2 + 4 + 2 * L1 * Real.log (K : ℝ) := by
    rw [hlogL2K]; ring
  have hTerm1 : 2 * (L1 * Real.log (L2 * (K : ℝ))) + 4 ≤
      akhcStep2Sat_Cconst d gamma pPsi pPsiS L1 L2 H KPsiS Y +
        akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D * Real.log (K : ℝ) := by
    rw [hTerm1eq, hCcoefeq]
    unfold akhcStep2Sat_Cconst
    linarith only [hT1nonneg, hc3bracket0, hDc3logK]
  -- Term 2 (T1small threshold)
  have hTerm2 : Real.log (1 / Y) / ((1 - 2 * akhcStep2_sPrime d gamma pPsi pPsiS) * Real.log 3) ≤
      akhcStep2Sat_Cconst d gamma pPsi pPsiS L1 L2 H KPsiS Y +
        akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D * Real.log (K : ℝ) := by
    rw [hCcoefeq]
    unfold akhcStep2Sat_Cconst akhcStep2Sat_T1val
    linarith only [hL1logL2, hc3bracket0, hDc3logK, hL1logK]
  -- Term 3 (the (P2') tail)
  have hKDpos : 0 < (K : ℝ) ^ D := Real.rpow_pos_of_pos hKRpos D
  have hlogHK : Real.log (H * (K : ℝ) ^ D) = Real.log H + D * Real.log (K : ℝ) := by
    rw [Real.log_mul hHpos.ne' hKDpos.ne', Real.log_rpow hKRpos]
  have hHKpos : 0 < H * (K : ℝ) ^ D := mul_pos hHpos hKDpos
  have hlogHKsq : Real.log ((H * (K : ℝ) ^ D) ^ (2 : ℝ)) = 2 * Real.log (H * (K : ℝ) ^ D) :=
    Real.log_rpow hHKpos 2
  have hHKsqpos : 0 < (H * (K : ℝ) ^ D) ^ (2 : ℝ) := Real.rpow_pos_of_pos hHKpos 2
  have hKPsiS36pos : 0 < KPsiS ^ 36 := pow_pos hKPsiSpos 36
  have hlognum : Real.log (6 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ)) =
      Real.log 6 + 36 * Real.log KPsiS + 2 * Real.log H + 2 * D * Real.log (K : ℝ) := by
    rw [Real.log_mul (by positivity) hHKsqpos.ne', Real.log_mul (by norm_num) hKPsiS36pos.ne',
      Real.log_pow, hlogHKsq, hlogHK]
    push_cast
    ring
  have hdenpos : 0 < (min (3 : ℝ) pPsiS - 2) * Y := mul_pos hminpos hYpos
  have hlogden : Real.log ((min (3 : ℝ) pPsiS - 2) * Y) =
      Real.log (min (3 : ℝ) pPsiS - 2) + Real.log Y :=
    Real.log_mul hminpos.ne' hYpos.ne'
  have hnumpos : 0 < 6 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ) :=
    mul_pos (by positivity) hHKsqpos
  have hTerm3eq :
      Real.log (6 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ) / ((min (3 : ℝ) pPsiS - 2) * Y)) /
          ((akhcRho d gamma pPsi pPsiS - gamma) * Real.log 3) =
        akhcStep2Sat_c3 d gamma pPsi pPsiS *
          (akhcStep2Sat_bracket0 KPsiS H pPsiS Y + 2 * D * Real.log (K : ℝ)) := by
    rw [Real.log_div hnumpos.ne' hdenpos.ne', hlognum, hlogden]
    unfold akhcStep2Sat_c3 akhcStep2Sat_bracket0
    ring
  have hTerm3 :
      Real.log (6 * KPsiS ^ 36 * (H * (K : ℝ) ^ D) ^ (2 : ℝ) / ((min (3 : ℝ) pPsiS - 2) * Y)) /
          ((akhcRho d gamma pPsi pPsiS - gamma) * Real.log 3) ≤
        akhcStep2Sat_Cconst d gamma pPsi pPsiS L1 L2 H KPsiS Y +
          akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D * Real.log (K : ℝ) := by
    rw [hTerm3eq, hCcoefeq]
    have hexpand : akhcStep2Sat_c3 d gamma pPsi pPsiS *
        (akhcStep2Sat_bracket0 KPsiS H pPsiS Y + 2 * D * Real.log (K : ℝ)) =
        akhcStep2Sat_c3 d gamma pPsi pPsiS * akhcStep2Sat_bracket0 KPsiS H pPsiS Y +
          2 * D * akhcStep2Sat_c3 d gamma pPsi pPsiS * Real.log (K : ℝ) := by ring
    rw [hexpand]
    unfold akhcStep2Sat_Cconst
    linarith only [hT1nonneg, hL1logL2, hL1logK]
  unfold akhcStep2_Lthreshold
  exact max_le (max_le hTerm1 hTerm2) hTerm3

/-- **`akhcStep2_Lreq` (the ceiling `+1` of the threshold) inherits the same affine bound**, up to
an additive `2` from the two roundings. -/
theorem akhcStep2Sat_Lreq_le {K : ℕ} (hK1 : 1 ≤ K) :
    (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K : ℝ) ≤
      akhcStep2Sat_Cconst d gamma pPsi pPsiS L1 L2 H KPsiS Y + 2 +
        akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D * Real.log (K : ℝ) := by
  have hthr := akhcStep2Sat_Lthreshold_le hd hgamma0 hgamma1 hpPsi hpPsiS hL1 hL2 hH hD hKPsiS
    hYpos hYlt1 hK1
  have hK1R : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hlogL2Knn : 0 ≤ Real.log (L2 * (K : ℝ)) := by
    have hL2K1 : (1 : ℝ) ≤ L2 * (K : ℝ) := by nlinarith only [hL2, hK1R]
    exact Real.log_nonneg hL2K1
  have hterm1nn : 0 ≤ 2 * (L1 * Real.log (L2 * (K : ℝ))) + 4 := by
    have : 0 ≤ L1 * Real.log (L2 * (K : ℝ)) := mul_nonneg (by linarith only [hL1]) hlogL2Knn
    linarith only [this]
  have hstep : 2 * (L1 * Real.log (L2 * (K : ℝ))) + 4 ≤
      akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K := by
    unfold akhcStep2_Lthreshold
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hLthrnn : 0 ≤ akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K := by
    linarith only [hterm1nn, hstep]
  have hceil : (⌈akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K⌉₊ : ℝ) <
      akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K + 1 :=
    Nat.ceil_lt_add_one hLthrnn
  have hLreqcast : (akhcStep2_Lreq d gamma pPsi pPsiS L1 L2 H D KPsiS Y K : ℝ) =
      (⌈akhcStep2_Lthreshold d gamma pPsi pPsiS L1 L2 H D KPsiS Y K⌉₊ : ℝ) + 1 := by
    unfold akhcStep2_Lreq; push_cast; ring
  linarith only [hceil, hthr, hLreqcast]

end LthresholdBound

/-! ## Nonnegativity of `akhcStep2Sat_Cconst`, `akhcStep2Sat_Ccoef` (standalone, minimal hypotheses,
needed to compare the affine bound with the linear terms in `m₀`). -/

theorem akhcStep2Sat_rhogamma_pos {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ} (hgamma1 : gamma < 1)
    (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS) :
    0 < akhcRho d gamma pPsi pPsiS - gamma := by
  have hr1 := akhcStep2_rhoPrime_lt_one hd hgamma1 hpPsi hpPsiS
  have hgr' := akhcStep2_gamma_le_rhoPrime d gamma pPsi pPsiS
  have hrhodef : akhcRho d gamma pPsi pPsiS = (1 + akhcRhoPrime d gamma pPsi pPsiS) / 2 := rfl
  rw [hrhodef]; linarith only [hr1, hgr']

theorem akhcStep2Sat_c3_pos {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ} (hgamma1 : gamma < 1)
    (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS) :
    0 < akhcStep2Sat_c3 d gamma pPsi pPsiS := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold akhcStep2Sat_c3
  exact div_pos one_pos (mul_pos (akhcStep2Sat_rhogamma_pos hd hgamma1 hpPsi hpPsiS) hlog3pos)

theorem akhcStep2Sat_bracket0_nonneg {KPsiS H pPsiS Y : ℝ} (hKPsiS : 1 ≤ KPsiS) (hH : 1 ≤ H)
    (hpPsiS : 2 < pPsiS) (hYpos : 0 < Y) (hYlt1 : Y < 1) :
    0 ≤ akhcStep2Sat_bracket0 KPsiS H pPsiS Y := by
  have hminlt : (2 : ℝ) < min (3 : ℝ) pPsiS := lt_min (by norm_num) hpPsiS
  have hminpos : 0 < min (3 : ℝ) pPsiS - 2 := by linarith only [hminlt]
  have hminle1 : min (3 : ℝ) pPsiS - 2 ≤ 1 := by
    have := min_le_left (3 : ℝ) pPsiS; linarith only [this]
  have hb1 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  have hb2 : 0 ≤ 36 * Real.log KPsiS := by have := Real.log_nonneg hKPsiS; linarith only [this]
  have hb3 : 0 ≤ 2 * Real.log H := by have := Real.log_nonneg hH; linarith only [this]
  have hb4 : Real.log (min (3 : ℝ) pPsiS - 2) ≤ 0 := Real.log_nonpos hminpos.le hminle1
  have hb5 : Real.log Y ≤ 0 := Real.log_nonpos hYpos.le hYlt1.le
  unfold akhcStep2Sat_bracket0
  linarith only [hb1, hb2, hb3, hb4, hb5]

theorem akhcStep2Sat_Ccoef_nonneg {d : ℕ} (hd : 2 ≤ d) {gamma pPsi pPsiS : ℝ} (hgamma1 : gamma < 1)
    (hpPsi : (d : ℝ) < pPsi) (hpPsiS : 2 < pPsiS) {L1 D : ℝ} (hL1 : 1 ≤ L1) (hD : 0 ≤ D) :
    0 ≤ akhcStep2Sat_Ccoef d gamma pPsi pPsiS L1 D := by
  have h1 : (0 : ℝ) ≤ 2 * L1 := by linarith only [hL1]
  have h2 : (0 : ℝ) ≤ 2 * D * akhcStep2Sat_c3 d gamma pPsi pPsiS := by
    have h3 : (0 : ℝ) ≤ 2 * D := by linarith only [hD]
    exact mul_nonneg h3 (akhcStep2Sat_c3_pos hd hgamma1 hpPsi hpPsiS).le
  unfold akhcStep2Sat_Ccoef
  linarith only [h1, h2]

/-! ## Main result: `akhcStep2_m0Req` is satisfiable, monotonically from an explicit threshold -/

end

end SuperdiffusionCLT.AKHC61.ParamsProofNative
