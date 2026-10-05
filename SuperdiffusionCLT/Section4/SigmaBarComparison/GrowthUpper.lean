/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.Growth
public import Mathlib.Analysis.Complex.Exponential

/-!
# The upper half of `e.sL.growth` (`l.shomm.vs.shomell#growth-construction` /
`#growth-telescoping`)

The printed proof fixes `A ≥ C_{e.sL.vs.sell}`, sets `L_* := L_0(2C_{e.sL.vs.sell}A,
0,cstar,nu)`, chooses a threshold `L_{**}` past which the step size
`⌈A log³ t⌉` is at most `t/2`, then recursively builds a *decreasing* sequence
`R_J = L, R_{J-1}, …, R_0 < L_{**}` by repeated subtraction, and sums the
per-step estimate (`e.sL.vs.sell` at `alpha = 0`) via a comparison with the
integral `∫ t^{-1/2} log^{9/2} t \, dt`.

This file reorganizes the same argument as a single **strong induction on
`L`**, replacing the explicit sequence/telescoping-sum-vs-integral comparison
by a purely algebraic one: since
`(L - L₋) * L^{-1/2} ≤ 2 (√L - √L₋)` (elementary, from `L - L₋ = (√L-√L₋)(√L+√L₋)`
and `√L₋ ≤ √L`), each one-step estimate is bounded by `2 C (√L - √L₋) log^{9/2}L`
(using `log R_{j+1} ≤ log L` to replace every step's own log power by the
top-level `log L`, valid since the sequence is increasing), and these
telescope via the elementary identity `(√L-√L₋)+(√L₋-√L_*) = √L-√L_*` instead
of `intervalIntegral`. No measure-theoretic integral is used anywhere in this
file.

The threshold `L_{**}` (`Lstop` below) is produced from the explicit,
self-contained bound `log t ≤ 6 t^{1/6}` (from `add_one_le_exp`), rather than
from an abstract "eventually" argument or from `Section4/LNaught/
Threshold.lean` (not owned by this task, and — per the now-resolved Gap 2 —
no longer needed for that reason, but a self-contained bound is simpler here
regardless).
-/

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

/-! ## Elementary real-analysis lemmas (no probability content) -/

/-- `log t ≤ 6 t^{1/6}` for `t ≥ 1`, from `add_one_le_exp` applied at
`(log t)/6` and `Real.rpow_def_of_pos`. -/
private theorem sbGrowUp_log_le_rpow_sixth {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ 6 * t ^ ((1 : ℝ) / 6) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hexp : Real.log t * (1 / 6) + 1 ≤ Real.exp (Real.log t * (1 / 6)) :=
    Real.add_one_le_exp (Real.log t * (1 / 6))
  have heq : t ^ ((1 : ℝ) / 6) = Real.exp (Real.log t * (1 / 6)) :=
    Real.rpow_def_of_pos htpos _
  rw [← heq] at hexp
  linarith only [hexp]

/-- `(log t)^3 ≤ 216 t^{1/2}` for `t ≥ 1` (`Real.rpow` throughout). -/
private theorem sbGrowUp_log_cubed_le {t : ℝ} (ht : 1 ≤ t) :
    Real.log t ^ (3 : ℝ) ≤ 216 * t ^ ((1 : ℝ) / 2) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hlog_nonneg : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hbound := sbGrowUp_log_le_rpow_sixth ht
  have hrpow_nonneg : (0 : ℝ) ≤ t ^ ((1 : ℝ) / 6) := Real.rpow_nonneg htpos.le _
  have hstep : Real.log t ^ (3 : ℝ) ≤ (6 * t ^ ((1 : ℝ) / 6)) ^ (3 : ℝ) :=
    Real.rpow_le_rpow hlog_nonneg hbound (by norm_num)
  have heq : (6 * t ^ ((1 : ℝ) / 6)) ^ (3 : ℝ) = 216 * t ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hrpow_nonneg]
    have h6cubed : (6 : ℝ) ^ (3 : ℝ) = 216 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h6cubed]
    congr 1
    rw [← Real.rpow_mul htpos.le]
    norm_num
  rw [heq] at hstep
  exact hstep

/-- The defining property of the threshold `L_{**}`: for `C ≥ 1` and
`t ≥ (434 C)²`, the step size `C (log t)^3` is at most `t/2`, and its
`Nat.ceil` is too. -/
private theorem sbGrowUp_ceil_step_le_half {C t : ℝ} (hC : 1 ≤ C)
    (ht : (434 * C) ^ 2 ≤ t) :
    (Nat.ceil (C * Real.log t ^ (3 : ℝ)) : ℝ) ≤ t / 2 := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have h1le : (1 : ℝ) ≤ (434 * C) ^ 2 := by nlinarith only [hC]
  have ht1 : (1 : ℝ) ≤ t := le_trans h1le ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hcube := sbGrowUp_log_cubed_le ht1
  have hcoeff : (0 : ℝ) ≤ C * Real.log t ^ (3 : ℝ) := by
    apply mul_nonneg hCpos.le
    have hlog_nonneg : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht1
    exact Real.rpow_nonneg hlog_nonneg _
  have hceil_lt : (Nat.ceil (C * Real.log t ^ (3 : ℝ)) : ℝ) <
      C * Real.log t ^ (3 : ℝ) + 1 := Nat.ceil_lt_add_one hcoeff
  have hCcube : C * Real.log t ^ (3 : ℝ) ≤ 216 * C * t ^ ((1 : ℝ) / 2) := by
    have h := mul_le_mul_of_nonneg_left hcube hCpos.le
    calc C * Real.log t ^ (3 : ℝ) ≤ C * (216 * t ^ ((1 : ℝ) / 2)) := h
      _ = 216 * C * t ^ ((1 : ℝ) / 2) := by ring
  have hrpow_ge1 : (1 : ℝ) ≤ t ^ ((1 : ℝ) / 2) := by
    have h1 : (1 : ℝ) ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by norm_num) ht1 (by norm_num)
    simpa using h1
  have hone_le : (1 : ℝ) ≤ C * t ^ ((1 : ℝ) / 2) := by nlinarith only [hC, hrpow_ge1]
  have hkey : 216 * C * t ^ ((1 : ℝ) / 2) + 1 ≤ 217 * C * t ^ ((1 : ℝ) / 2) := by
    nlinarith only [hone_le]
  have hrpow_sq : t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) = t := by
    rw [← Real.rpow_add htpos]
    norm_num
  have hrpow_nonneg : (0 : ℝ) ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_nonneg htpos.le _
  have hfinal : 217 * C * t ^ ((1 : ℝ) / 2) ≤ t / 2 := by
    have hstep : (434 * C) * t ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
      have h434 : 434 * C ≤ t ^ ((1 : ℝ) / 2) := by
        have hsqrt_mono : ((434 * C) ^ 2 : ℝ) ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) ht (by norm_num)
        have heq2 : ((434 * C : ℝ) ^ 2) ^ ((1 : ℝ) / 2) = 434 * C := by
          rw [show ((434 * C : ℝ) ^ 2) = (434 * C) ^ (2 : ℝ) by
              rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
            ← Real.rpow_mul (by positivity)]
          norm_num
        rwa [heq2] at hsqrt_mono
      exact mul_le_mul_of_nonneg_right h434 hrpow_nonneg
    rw [hrpow_sq] at hstep
    linarith only [hstep]
  linarith only [hceil_lt, hCcube, hkey, hfinal]

/-- `log t ≥ 3` once `t ≥ exp 3`. -/
private theorem sbGrowUp_log_ge_three {t : ℝ} (ht : Real.exp 3 ≤ t) :
    (3 : ℝ) ≤ Real.log t := by
  have h := Real.log_le_log (Real.exp_pos 3) ht
  rwa [Real.log_exp] at h

/-- The purely algebraic one-step comparison: `(b-a)/√b ≤ 2(√b-√a)` for
`0 ≤ a`, `0 < b` (no relation between `a` and `b` is needed: this is
equivalent to `(√b-√a)² ≥ 0`). -/
private theorem sbGrowUp_diff_div_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hbpos : 0 < b) :
    (b - a) / Real.sqrt b ≤ 2 * (Real.sqrt b - Real.sqrt a) := by
  have hsb_pos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbpos
  rw [div_le_iff₀ hsb_pos]
  have hsqa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsqb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hbpos.le
  nlinarith only [sq_nonneg (Real.sqrt b - Real.sqrt a), hsqa, hsqb]

/-- `b^{-1/2} = (√b)⁻¹` for `b > 0`. -/
private theorem sbGrowUp_rpow_neg_half_eq {b : ℝ} (hb : 0 < b) :
    b ^ (-(1 : ℝ) / 2) = (Real.sqrt b)⁻¹ := by
  rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hb.le]

/-! ## The generic telescoping step (no probability content)

This replaces the paper's explicit sequence `R_j` and the
telescoping-sum-vs-integral comparison by a single strong induction, using
only the elementary identity `(√L-√L₋) + (√L₋-√L_*) = √L-√L_*` in place of
`intervalIntegral.integral_add_adjacent_intervals`. -/

/-- Strong-induction telescoping: given a one-step estimate `hStep` (valid for
every `L ≥ Lstop`, producing a smaller witness `Lminus < L` with
`Lstar ≤ Lminus` and a `√`-difference bound) and a uniform bound `Ccrude` on
`S` below `Lstop`, `S` is bounded by `Ccrude` plus the telescoped `√`-sum from
`Lstar` to `L`, for every `L ≥ Lstop`. -/
private theorem sbGrowUp_telescope {S : ℕ → ℝ} {Ccrude C2 Lstar : ℝ}
    (hC2 : 0 ≤ C2) {Lstop : ℕ}
    (hCrudeStop : ∀ r : ℕ, r < Lstop → S r ≤ Ccrude)
    (hStep : ∀ L : ℕ, Lstop ≤ L →
        ∃ Lminus : ℕ, Lminus < L ∧ Lstar ≤ (Lminus : ℝ) ∧
          S L - S Lminus ≤ C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) *
            (Real.sqrt (L : ℝ) - Real.sqrt (Lminus : ℝ))) :
    ∀ L : ℕ, Lstop ≤ L →
      S L ≤ Ccrude + C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) *
        (Real.sqrt (L : ℝ) - Real.sqrt Lstar) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro hL
    obtain ⟨Lminus, hLminus_lt, hLminus_ge, hstep⟩ := hStep L hL
    have hLpos : (0 : ℕ) < L := lt_of_le_of_lt (Nat.zero_le Lminus) hLminus_lt
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLpos
    have hlogL0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
    have hlogL_nonneg : (0 : ℝ) ≤ Real.log (L : ℝ) ^ ((9 : ℝ) / 2) :=
      Real.rpow_nonneg hlogL0 _
    have hsqrt_ge : Real.sqrt Lstar ≤ Real.sqrt (Lminus : ℝ) :=
      Real.sqrt_le_sqrt hLminus_ge
    have hlogMinus0 : (0 : ℝ) ≤ Real.log (Lminus : ℝ) := by
      rcases Nat.eq_zero_or_pos Lminus with hz | hpos
      · rw [hz, Nat.cast_zero, Real.log_zero]
      · exact Real.log_nonneg (by exact_mod_cast hpos)
    have hlog_mono : Real.log (Lminus : ℝ) ≤ Real.log (L : ℝ) := by
      rcases Nat.eq_zero_or_pos Lminus with hz | hpos
      · rw [hz, Nat.cast_zero, Real.log_zero]; exact hlogL0
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hLminus_lt.le)
    have hlogpow_mono : Real.log (Lminus : ℝ) ^ ((9 : ℝ) / 2) ≤
        Real.log (L : ℝ) ^ ((9 : ℝ) / 2) :=
      Real.rpow_le_rpow hlogMinus0 hlog_mono (by norm_num)
    by_cases hcase : Lstop ≤ Lminus
    · have hIH := ih Lminus hLminus_lt hcase
      have hsqrtdiff_nonneg : (0 : ℝ) ≤ Real.sqrt (Lminus : ℝ) - Real.sqrt Lstar := by
        linarith only [hsqrt_ge]
      have hIH_upgraded : S Lminus ≤ Ccrude + C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) *
          (Real.sqrt (Lminus : ℝ) - Real.sqrt Lstar) := by
        have hmono :
            C2 * Real.log (Lminus : ℝ) ^ ((9 : ℝ) / 2) *
                (Real.sqrt (Lminus : ℝ) - Real.sqrt Lstar) ≤
              C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) *
                (Real.sqrt (Lminus : ℝ) - Real.sqrt Lstar) := by
          apply mul_le_mul_of_nonneg_right _ hsqrtdiff_nonneg
          exact mul_le_mul_of_nonneg_left hlogpow_mono hC2
        linarith only [hIH, hmono]
      have hexpand :
          C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) * (Real.sqrt (Lminus : ℝ) - Real.sqrt Lstar) +
              C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) *
                (Real.sqrt (L : ℝ) - Real.sqrt (Lminus : ℝ)) =
            C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) * (Real.sqrt (L : ℝ) - Real.sqrt Lstar) := by
        ring
      linarith only [hstep, hIH_upgraded, hexpand]
    · push Not at hcase
      have hcrude := hCrudeStop Lminus hcase
      have hsqrtdiff_le : Real.sqrt (L : ℝ) - Real.sqrt (Lminus : ℝ) ≤
          Real.sqrt (L : ℝ) - Real.sqrt Lstar := by linarith only [hsqrt_ge]
      have hmono2 :
          C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) * (Real.sqrt (L : ℝ) - Real.sqrt (Lminus : ℝ)) ≤
            C2 * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) * (Real.sqrt (L : ℝ) - Real.sqrt Lstar) :=
        mul_le_mul_of_nonneg_left hsqrtdiff_le (mul_nonneg hC2 hlogL_nonneg)
      linarith only [hstep, hcrude, hmono2]

/-! ## Assembly: the upper half of `e.sL.growth` -/

/-- **The upper half of `e.sL.growth`** from `e.sL.vs.sell` (`hSell`, the exact
first conjunct of `sigmaBar_cutoff_comparison`, copied verbatim)
and `hd`. Uses `sbAsm_growth_lower` and `sbAsm_crude_growth_bound`
(`Growth.lean`) for the two other printed ingredients
(`p.sstar.lower.bound`/`e.Enaught.vs.A.and.Ahom`). -/
theorem sbAsm_growth_upper (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hSell : ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              |(sigmaBarInfinite nu ell P)⁻¹ * sigmaBarInfinite nu L P - 1| ≤
                C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                  Real.log (L : ℝ) ^ (3 : ℝ) ∧
              C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu L P) ^ (-(2 : ℝ)) *
                  Real.log (L : ℝ) ^ (3 : ℝ) ≤ (1 : ℝ) / 2) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ cStar : ℝ, 0 < cStar →
          ∀ K : ℝ,
            ∃ Lg : ℕ,
              ∀ (P : ProbabilityMeasure (ShellSeq d))
                (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
                ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
                  ∀ L : ℕ, Lg ≤ L →
                    sigmaBarInfinite nu L P ≤
                      C * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ ((1 : ℝ) / 2) *
                        Real.log (L : ℝ) ^ ((9 : ℝ) / 2) := by
  obtain ⟨C_sell, hCsell1, hSellBody⟩ := hSell
  obtain ⟨Cgrow, hCgrow1, hGrowLower⟩ := sbAsm_growth_lower d hd
  obtain ⟨Ccrude, hCcrude1, hCrude⟩ := sbAsm_crude_growth_bound d
  have hCgrowPos : (0 : ℝ) < Cgrow := lt_of_lt_of_le one_pos hCgrow1
  have hCsellPos : (0 : ℝ) < C_sell := lt_of_lt_of_le one_pos hCsell1
  refine ⟨8 * C_sell * Cgrow + 1, by nlinarith only [hCsellPos, hCgrowPos], ?_⟩
  intro nu hnu hnu1 cStar hcStar K
  obtain ⟨Lg', hGrowLowerL⟩ := hGrowLower nu hnu hnu1 cStar hcStar K
  set Lstar : ℝ :=
    SuperdiffusionCLT.Frozen.Section4.lNaught C_sell (C_sell * (2 * C_sell)) 0 cStar nu K
    with hLstardef
  set Lstop : ℕ :=
    max (Nat.ceil ((434 * C_sell) ^ 2)) (max (Nat.ceil (2 * Lstar)) Lg') with hLstopdef
  have hLstopR1 : ((434 * C_sell) ^ 2 : ℝ) ≤ (Lstop : ℝ) := by
    have h1 : Nat.ceil (((434 * C_sell) ^ 2 : ℝ)) ≤ Lstop := le_trans (le_max_left _ _) le_rfl
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hLstopR2 : 2 * Lstar ≤ (Lstop : ℝ) := by
    have h1 : Nat.ceil ((2 * Lstar : ℝ)) ≤ Lstop :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) le_rfl)
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
  have hLstopLg' : Lg' ≤ Lstop := le_trans (le_max_right _ _) (le_max_right _ _)
  have hexp3 : Real.exp 3 ≤ (Lstop : ℝ) := by
    have h1 : (434 : ℝ) ^ 2 ≤ (434 * C_sell) ^ 2 := by nlinarith only [hCsell1]
    have h2 : Real.exp 3 ≤ (434 : ℝ) ^ 2 := by
      have he1 := Real.exp_one_lt_d9
      have hepos := Real.exp_pos 1
      have hsq : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
        nlinarith only [he1, hepos]
      have hsqpos : (0:ℝ) < Real.exp 1 * Real.exp 1 := mul_pos hepos hepos
      have hcube : Real.exp 1 * Real.exp 1 * Real.exp 1 <
          2.7182818286 * 2.7182818286 * 2.7182818286 := by
        nlinarith only [hsq, he1, hepos, hsqpos]
      have hexp3eq : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3:ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
      rw [hexp3eq]
      nlinarith only [hcube]
    linarith only [h1, h2, hLstopR1]
  -- A further threshold `LgAbsorb` past which the crude-bound residual
  -- `Ccrude'` is absorbed into the leading `cStar^{-3/2} ν^{-2} L^{1/2} log^{9/2}L`
  -- term (using `log L ≥ 3` for `L ≥ Lstop`).
  have hK0pos : (0 : ℝ) < cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) :=
    mul_pos (Real.rpow_pos_of_pos hcStar _) (Real.rpow_pos_of_pos hnu _)
  set LgAbsorb : ℕ :=
    Nat.ceil (((Ccrude * nu⁻¹ * (1 + (Lstop : ℝ))) /
        ((3 : ℝ) ^ ((9 : ℝ) / 2) * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))) ^ 2)
    with hLgAbsorbdef
  set Lg : ℕ := max Lstop LgAbsorb with hLgdef
  have hLstopLeLg : Lstop ≤ Lg := le_max_left _ _
  have hLgAbsorbLeLg : LgAbsorb ≤ Lg := le_max_right _ _
  refine ⟨Lg, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5
  set S : ℕ → ℝ := fun r => sigmaBarInfinite nu r P with hSdef
  have hCrudeStop : ∀ r : ℕ, r < Lstop → S r ≤ Ccrude * nu⁻¹ * (1 + (Lstop : ℝ)) := by
    intro r hr
    have h1 := hCrude nu hnu hnu1 P hPrefix hJ2 hJ3 hJ4 r
    have h2 : (1 + (r : ℝ)) ≤ 1 + (Lstop : ℝ) := by
      have : (r : ℝ) ≤ (Lstop : ℝ) := by exact_mod_cast hr.le
      linarith only [this]
    have hnuinv : (0:ℝ) ≤ nu⁻¹ := (inv_pos.mpr hnu).le
    have h3 : Ccrude * nu⁻¹ * (1 + (r:ℝ)) ≤ Ccrude * nu⁻¹ * (1 + (Lstop:ℝ)) := by
      apply mul_le_mul_of_nonneg_left h2
      exact mul_nonneg (le_trans zero_le_one hCcrude1) hnuinv
    exact le_trans h1 h3
  have hcStarnn : (0:ℝ) ≤ cStar ^ (-((3:ℝ)/2)) := (Real.rpow_pos_of_pos hcStar _).le
  have hnunn : (0:ℝ) ≤ nu ^ (-(2:ℝ)) := (Real.rpow_pos_of_pos hnu _).le
  have hC2nn : (0:ℝ) ≤ 8 * C_sell * Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) := by
    have : (0:ℝ) ≤ 8 * C_sell * Cgrow := by positivity
    exact mul_nonneg (mul_nonneg this hcStarnn) hnunn
  have hStep : ∀ L : ℕ, Lstop ≤ L →
      ∃ Lminus : ℕ, Lminus < L ∧ Lstar ≤ (Lminus : ℝ) ∧
        S L - S Lminus ≤
          8 * C_sell * Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
            Real.log (L : ℝ) ^ ((9 : ℝ) / 2) *
            (Real.sqrt (L : ℝ) - Real.sqrt (Lminus : ℝ)) := by
    intro L hL
    have hLR : (Lstop : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hthr434 : ((434 * C_sell) ^ 2 : ℝ) ≤ (L : ℝ) := le_trans hLstopR1 hLR
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
      have h1 : (1:ℝ) ≤ ((434 * C_sell) ^ 2 : ℝ) := by nlinarith only [hCsell1]
      linarith only [h1, hthr434]
    have hLexp3 : Real.exp 3 ≤ (L : ℝ) := le_trans hexp3 hLR
    have hlogL3 : (3 : ℝ) ≤ Real.log (L : ℝ) := sbGrowUp_log_ge_three hLexp3
    set step : ℕ := Nat.ceil (C_sell * Real.log (L : ℝ) ^ (3 : ℝ)) with hstepdef
    have hstepR_le : (step : ℝ) ≤ (L : ℝ) / 2 :=
      sbGrowUp_ceil_step_le_half hCsell1 hthr434
    have hstepR_ge : C_sell * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (step : ℝ) := Nat.le_ceil _
    have hcube_ge27 : (27 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := by
      have h1 : (3 : ℝ) ^ (3 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hlogL3 (by norm_num)
      have h2 : (3 : ℝ) ^ (3 : ℝ) = 27 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      linarith only [h1, h2]
    have hcube_pos : (0 : ℝ) < C_sell * Real.log (L : ℝ) ^ (3 : ℝ) := by nlinarith only [hCsellPos, hcube_ge27]
    have hstepR_pos : (0 : ℝ) < (step : ℝ) := lt_of_lt_of_le hcube_pos hstepR_ge
    have hstep_pos : 0 < step := by exact_mod_cast hstepR_pos
    have hstep_le_L : step ≤ L := by
      have : (step : ℝ) ≤ (L : ℝ) := le_trans hstepR_le (by linarith only [hL1])
      exact_mod_cast this
    set Lminus : ℕ := L - step with hLminusdef
    have hLminusR : (Lminus : ℝ) = (L : ℝ) - (step : ℝ) := by
      rw [hLminusdef]; exact Nat.cast_sub hstep_le_L
    have hLminus_lt : Lminus < L := by
      have := hstep_pos
      omega
    have hLminus_ge_half : (L:ℝ) / 2 ≤ (Lminus:ℝ) := by
      rw [hLminusR]; linarith only [hstepR_le]
    have hLminus_ge : Lstar ≤ (Lminus : ℝ) := by
      have h1 : Lstar ≤ (Lstop : ℝ) / 2 := by linarith only [hLstopR2]
      have h2 : (Lstop:ℝ) / 2 ≤ (L:ℝ)/2 := by linarith only [hLR]
      linarith only [h1, h2, hLminus_ge_half]
    have hceil_lt_add1 : (step : ℝ) < C_sell * Real.log (L : ℝ) ^ (3 : ℝ) + 1 :=
      Nat.ceil_lt_add_one hcube_pos.le
    have hcube_ge1 : (1 : ℝ) ≤ C_sell * Real.log (L : ℝ) ^ (3 : ℝ) := by
      nlinarith only [hCsell1, hcube_ge27]
    have hthresh2 : (L : ℝ) - (2 * C_sell) * (L : ℝ) ^ (0 : ℝ) *
        Real.log (L : ℝ) ^ (3 : ℝ) ≤ (Lminus : ℝ) := by
      rw [Real.rpow_zero, mul_one]
      rw [hLminusR]
      linarith only [hceil_lt_add1, hcube_ge1]
    have hCsell2 : (1 : ℝ) ≤ 2 * C_sell := by linarith only [hCsell1]
    have hSLpos : (0 : ℝ) < S L := sigmaBarInfinite_pos hnu L hPrefix hJ2 hJ3 hJ4
    have hSLminuspos : (0 : ℝ) < S Lminus := sigmaBarInfinite_pos hnu Lminus hPrefix hJ2 hJ3 hJ4
    obtain ⟨hmainIneq, hmain18⟩ :=
      hSellBody nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5
        0 (2 * C_sell) (le_refl 0) (by norm_num) hCsell2 L Lminus hLminus_lt.le hLminus_ge
        hthresh2
    -- Simplify the printed RHS: `L^0 = 1`.
    rw [Real.rpow_zero, mul_one] at hmainIneq hmain18
    have hab := abs_le.mp hmainIneq
    have hge_half : (1 : ℝ) / 2 ≤ (S Lminus)⁻¹ * S L := by linarith only [hab.1, hmain18]
    have hSLminus_le : S Lminus ≤ 2 * S L := by
      have h1 := mul_le_mul_of_nonneg_left hge_half hSLminuspos.le
      rw [← mul_assoc, mul_inv_cancel₀ hSLminuspos.ne', one_mul] at h1
      linarith only [h1]
    have heq1 : S Lminus * ((S Lminus)⁻¹ * S L - 1) = S L - S Lminus := by
      rw [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ hSLminuspos.ne', one_mul]
    have h2 := mul_le_mul_of_nonneg_left hab.2 hSLminuspos.le
    rw [heq1] at h2
    -- `h2 : S L - S Lminus ≤ S Lminus * (2 C_sell² (S L)^{-2} log³L)`
    have hRHSnn : (0 : ℝ) ≤
        C_sell * (2 * C_sell) * (S L) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have h1 : (0:ℝ) ≤ (S L) ^ (-(2:ℝ)) := (Real.rpow_pos_of_pos hSLpos _).le
      have h2 : (0:ℝ) ≤ Real.log (L:ℝ) ^ (3:ℝ) := by
        have : (0:ℝ) ≤ Real.log (L:ℝ) := by linarith only [hlogL3]
        exact Real.rpow_nonneg this _
      have h3 : (0:ℝ) ≤ C_sell * (2 * C_sell) := by nlinarith only [hCsellPos]
      exact mul_nonneg (mul_nonneg h3 h1) h2
    have hstep1 : S L - S Lminus ≤
        (C_sell * (2 * C_sell) * (S L) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ)) *
          S Lminus := by
      have heq2 : S Lminus * (C_sell * (2 * C_sell) * (S L) ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ (3 : ℝ)) =
          (C_sell * (2 * C_sell) * (S L) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ)) *
            S Lminus := by ring
      rwa [heq2] at h2
    have hstep2 : S L - S Lminus ≤
        C_sell * (2 * C_sell) * (S L) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) * (2 * S L) := by
      have hmul := mul_le_mul_of_nonneg_left hSLminus_le hRHSnn
      linarith only [hstep1, hmul]
    -- Fold the `(S L)^{-2} * (2 S L) = 2 (S L)^{-1}` power identity.
    have hpow_id : (S L) ^ (-(2 : ℝ)) * (2 * S L) = 2 * (S L) ^ (-(1 : ℝ)) := by
      have h1 : (S L) ^ (-(2 : ℝ)) * S L = (S L) ^ (-(1 : ℝ)) := by
        have hh := (Real.rpow_add hSLpos (-(2 : ℝ)) (1 : ℝ)).symm
        rw [Real.rpow_one] at hh
        have hexp : -(2 : ℝ) + 1 = -(1 : ℝ) := by norm_num
        rw [hexp] at hh
        exact hh
      calc (S L) ^ (-(2 : ℝ)) * (2 * S L) = 2 * ((S L) ^ (-(2 : ℝ)) * S L) := by ring
        _ = 2 * (S L) ^ (-(1 : ℝ)) := by rw [h1]
    have hstep3 : S L - S Lminus ≤
        C_sell * (2 * C_sell) * (2 * (S L) ^ (-(1 : ℝ))) * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have heq3 : C_sell * (2 * C_sell) * (S L) ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ (3 : ℝ) *
          (2 * S L) =
          C_sell * (2 * C_sell) * ((S L) ^ (-(2 : ℝ)) * (2 * S L)) * Real.log (L : ℝ) ^ (3 : ℝ) := by
        ring
      rw [heq3, hpow_id] at hstep2
      exact hstep2
    -- Absorb `log³L` via `log³L ≤ (L - Lminus)/C_sell`.
    have hLdiff_eq : (L : ℝ) - (Lminus : ℝ) = (step : ℝ) := by linarith only [hLminusR]
    have hlogcube_le : Real.log (L : ℝ) ^ (3 : ℝ) ≤ ((L : ℝ) - (Lminus : ℝ)) / C_sell := by
      rw [hLdiff_eq, le_div_iff₀ hCsellPos]
      linarith only [hstepR_ge]
    have hSLinv_nonneg : (0:ℝ) ≤ (S L) ^ (-(1:ℝ)) := (Real.rpow_pos_of_pos hSLpos _).le
    have hcoeffnn2 : (0:ℝ) ≤ C_sell * (2 * C_sell) * (2 * (S L) ^ (-(1:ℝ))) := by
      have h3 : (0:ℝ) ≤ C_sell * (2 * C_sell) := by nlinarith only [hCsellPos]
      positivity
    have hstep4 : S L - S Lminus ≤
        C_sell * (2 * C_sell) * (2 * (S L) ^ (-(1 : ℝ))) * (((L:ℝ) - (Lminus:ℝ)) / C_sell) := by
      have hmul2 := mul_le_mul_of_nonneg_left hlogcube_le hcoeffnn2
      linarith only [hstep3, hmul2]
    have hstep5 : S L - S Lminus ≤
        4 * C_sell * (S L) ^ (-(1 : ℝ)) * ((L:ℝ) - (Lminus:ℝ)) := by
      have heq4 : C_sell * (2 * C_sell) * (2 * (S L) ^ (-(1 : ℝ))) *
          (((L:ℝ) - (Lminus:ℝ)) / C_sell) =
          4 * C_sell * (S L) ^ (-(1 : ℝ)) * ((L:ℝ) - (Lminus:ℝ)) := by
        field_simp
        ring
      rwa [heq4] at hstep4
    -- Substitute the crude-lower-bound reciprocal `(S L)^{-1} ≤ Cgrow cStar^{-3/2} ν^{-2} L^{-1/2} log^{9/2}L`.
    have hGrowThis := hGrowLowerL P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 L (le_trans hLstopLg' hL)
    have hSLinv_le : (S L) ^ (-(1 : ℝ)) ≤
        Cgrow * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * (L : ℝ) ^ (-((1 : ℝ) / 2)) *
          Real.log (L : ℝ) ^ ((9 : ℝ) / 2) := by
      have hlogLpos : (0:ℝ) < Real.log (L:ℝ) := lt_of_lt_of_le (by norm_num) hlogL3
      have hLpos2 : (0:ℝ) < (L:ℝ) := lt_of_lt_of_le one_pos hL1
      have hLHSpos : (0:ℝ) < Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
          Real.log (L:ℝ) ^ (-((9:ℝ)/2)) := by
        have h1 : (0:ℝ) < Cgrow⁻¹ := inv_pos.mpr hCgrowPos
        have h2 : (0:ℝ) < cStar ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hcStar _
        have h3 : (0:ℝ) < nu ^ (2:ℝ) := Real.rpow_pos_of_pos hnu _
        have h4 : (0:ℝ) < (L:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hLpos2 _
        have h5 : (0:ℝ) < Real.log (L:ℝ) ^ (-((9:ℝ)/2)) :=
          Real.rpow_pos_of_pos hlogLpos _
        positivity
      have hinv := inv_anti₀ hLHSpos hGrowThis
      have heq5 : (Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
          Real.log (L:ℝ) ^ (-((9:ℝ)/2)))⁻¹ =
          Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) * (L:ℝ) ^ (-((1:ℝ)/2)) *
            Real.log (L:ℝ) ^ ((9:ℝ)/2) := by
        have hCgrow_inv : Cgrow⁻¹ * Cgrow = 1 := inv_mul_cancel₀ hCgrowPos.ne'
        have hcStar_pair : cStar ^ ((3:ℝ)/2) * cStar ^ (-((3:ℝ)/2)) = 1 := by
          rw [← Real.rpow_add hcStar]; norm_num
        have hnu_pair : nu ^ (2:ℝ) * nu ^ (-(2:ℝ)) = 1 := by
          rw [← Real.rpow_add hnu]; norm_num
        have hL_pair : (L:ℝ) ^ ((1:ℝ)/2) * (L:ℝ) ^ (-((1:ℝ)/2)) = 1 := by
          rw [← Real.rpow_add hLpos2]; norm_num
        have hlog_pair : Real.log (L:ℝ) ^ (-((9:ℝ)/2)) * Real.log (L:ℝ) ^ ((9:ℝ)/2) = 1 := by
          rw [← Real.rpow_add hlogLpos]; norm_num
        have hprod :
            (Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
                Real.log (L:ℝ) ^ (-((9:ℝ)/2))) *
              (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) * (L:ℝ) ^ (-((1:ℝ)/2)) *
                Real.log (L:ℝ) ^ ((9:ℝ)/2)) = 1 := by
          calc
            (Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
                  Real.log (L:ℝ) ^ (-((9:ℝ)/2))) *
                (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) * (L:ℝ) ^ (-((1:ℝ)/2)) *
                  Real.log (L:ℝ) ^ ((9:ℝ)/2)) =
                (Cgrow⁻¹ * Cgrow) * (cStar ^ ((3:ℝ)/2) * cStar ^ (-((3:ℝ)/2))) *
                  (nu ^ (2:ℝ) * nu ^ (-(2:ℝ))) *
                  ((L:ℝ) ^ ((1:ℝ)/2) * (L:ℝ) ^ (-((1:ℝ)/2))) *
                  (Real.log (L:ℝ) ^ (-((9:ℝ)/2)) * Real.log (L:ℝ) ^ ((9:ℝ)/2)) := by ring
            _ = 1 * 1 * 1 * 1 * 1 := by
                rw [hCgrow_inv, hcStar_pair, hnu_pair, hL_pair, hlog_pair]
            _ = 1 := by ring
        have hLHSne : (Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
            Real.log (L:ℝ) ^ (-((9:ℝ)/2))) ≠ 0 := hLHSpos.ne'
        have hh :
            (Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
                Real.log (L:ℝ) ^ (-((9:ℝ)/2)))⁻¹ *
              ((Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
                    Real.log (L:ℝ) ^ (-((9:ℝ)/2))) *
                (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) * (L:ℝ) ^ (-((1:ℝ)/2)) *
                  Real.log (L:ℝ) ^ ((9:ℝ)/2))) =
              (Cgrow⁻¹ * cStar ^ ((3:ℝ)/2) * nu ^ (2:ℝ) * (L:ℝ) ^ ((1:ℝ)/2) *
                  Real.log (L:ℝ) ^ (-((9:ℝ)/2)))⁻¹ * 1 := by rw [hprod]
        rw [← mul_assoc, inv_mul_cancel₀ hLHSne, one_mul, mul_one] at hh
        exact hh.symm
      rw [heq5] at hinv
      have hSLinv_eq : (S L) ^ (-(1:ℝ)) = ((S L) ^ (1:ℝ))⁻¹ := Real.rpow_neg hSLpos.le 1
      rw [hSLinv_eq, Real.rpow_one]
      exact hinv
    refine ⟨Lminus, hLminus_lt, hLminus_ge, ?_⟩
    have hstep6 : S L - S Lminus ≤
        4 * C_sell * (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
            (L:ℝ) ^ (-((1:ℝ)/2)) * Real.log (L:ℝ) ^ ((9:ℝ)/2)) * ((L:ℝ) - (Lminus:ℝ)) := by
      have hLdiffnn : (0:ℝ) ≤ (L:ℝ) - (Lminus:ℝ) := by
        rw [hLdiff_eq]; exact hstepR_pos.le
      have hmul3 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hSLinv_le (by positivity : (0:ℝ) ≤ 4 * C_sell)) hLdiffnn
      linarith only [hstep5, hmul3]
    have hLminuscast : (0:ℝ) ≤ (Lminus:ℝ) := Nat.cast_nonneg _
    have hrpow_neg_half : (L:ℝ) ^ (-((1:ℝ)/2)) * ((L:ℝ) - (Lminus:ℝ)) ≤
        2 * (Real.sqrt (L:ℝ) - Real.sqrt (Lminus:ℝ)) := by
      have hLpos' : (0:ℝ) < (L:ℝ) := lt_of_lt_of_le one_pos hL1
      have heq6 : (L:ℝ) ^ (-((1:ℝ)/2)) = (Real.sqrt (L:ℝ))⁻¹ := by
        have := sbGrowUp_rpow_neg_half_eq hLpos'
        rwa [show -(1:ℝ)/2 = -((1:ℝ)/2) from by ring] at this
      rw [heq6]
      have := sbGrowUp_diff_div_sqrt_le hLminuscast hLpos'
      rwa [div_eq_inv_mul] at this
    have hfinal_coeff_nn : (0:ℝ) ≤
        4 * C_sell * (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
          Real.log (L:ℝ) ^ ((9:ℝ)/2)) := by
      have hlognn : (0:ℝ) ≤ Real.log (L:ℝ) ^ ((9:ℝ)/2) := by
        have : (0:ℝ) ≤ Real.log (L:ℝ) := by linarith only [hlogL3]
        exact Real.rpow_nonneg this _
      positivity
    have hmul4 :
        4 * C_sell * (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
            (L:ℝ) ^ (-((1:ℝ)/2)) * Real.log (L:ℝ) ^ ((9:ℝ)/2)) * ((L:ℝ) - (Lminus:ℝ)) ≤
        8 * C_sell * Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
          Real.log (L:ℝ) ^ ((9:ℝ)/2) * (Real.sqrt (L:ℝ) - Real.sqrt (Lminus:ℝ)) := by
      have heq7 :
          4 * C_sell * (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
              (L:ℝ) ^ (-((1:ℝ)/2)) * Real.log (L:ℝ) ^ ((9:ℝ)/2)) * ((L:ℝ) - (Lminus:ℝ)) =
          4 * C_sell * (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
              Real.log (L:ℝ) ^ ((9:ℝ)/2)) *
            ((L:ℝ) ^ (-((1:ℝ)/2)) * ((L:ℝ) - (Lminus:ℝ))) := by ring
      rw [heq7]
      have hmul5 := mul_le_mul_of_nonneg_left hrpow_neg_half hfinal_coeff_nn
      calc 4 * C_sell * (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
              Real.log (L:ℝ) ^ ((9:ℝ)/2)) * ((L:ℝ) ^ (-((1:ℝ)/2)) * ((L:ℝ) - (Lminus:ℝ))) ≤
            4 * C_sell * (Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
              Real.log (L:ℝ) ^ ((9:ℝ)/2)) * (2 * (Real.sqrt (L:ℝ) - Real.sqrt (Lminus:ℝ))) := hmul5
        _ = 8 * C_sell * Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
              Real.log (L:ℝ) ^ ((9:ℝ)/2) * (Real.sqrt (L:ℝ) - Real.sqrt (Lminus:ℝ)) := by ring
    linarith only [hstep6, hmul4]
  have hgoal := sbGrowUp_telescope
    (S := S) (Ccrude := Ccrude * nu⁻¹ * (1 + (Lstop:ℝ)))
    (C2 := 8 * C_sell * Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ))) (Lstar := Lstar)
    hC2nn hCrudeStop hStep
  intro L hL
  have hLstopL : Lstop ≤ L := le_trans hLstopLeLg hL
  have hLgAbsorbL : LgAbsorb ≤ L := le_trans hLgAbsorbLeLg hL
  have hfinal := hgoal L hLstopL
  have hLR : (Lstop : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLstopL
  have hL1' : (1 : ℝ) ≤ (L : ℝ) := by
    have h1 : (1 : ℝ) ≤ ((434 * C_sell) ^ 2 : ℝ) := by nlinarith only [hCsell1]
    linarith only [h1, hLstopR1, hLR]
  have hLexp3' : Real.exp 3 ≤ (L : ℝ) := le_trans hexp3 hLR
  have hlogL3' : (3 : ℝ) ≤ Real.log (L : ℝ) := sbGrowUp_log_ge_three hLexp3'
  have hsqrt_eq : Real.sqrt (L : ℝ) = (L : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hsqrtLstar_nonneg : (0 : ℝ) ≤ Real.sqrt Lstar := Real.sqrt_nonneg _
  have hsqrtL_nonneg : (0 : ℝ) ≤ Real.sqrt (L : ℝ) := Real.sqrt_nonneg _
  have hSL_eq : S L = sigmaBarInfinite nu L P := rfl
  rw [hSL_eq] at hfinal
  have hlogLnn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ ((9 : ℝ) / 2) := by
    have h0 : (0 : ℝ) ≤ Real.log (L : ℝ) := by linarith only [hlogL3']
    exact Real.rpow_nonneg h0 _
  -- Drop the `-√Lstar` term.
  have hcoeffnn : (0 : ℝ) ≤ 8 * C_sell * Cgrow * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ ((9 : ℝ) / 2) := by
    have h1 : (0:ℝ) ≤ 8 * C_sell * Cgrow := by nlinarith only [hCsellPos, hCgrowPos]
    positivity
  have hdrop : Real.sqrt (L : ℝ) - Real.sqrt Lstar ≤ Real.sqrt (L : ℝ) := by
    linarith only [hsqrtLstar_nonneg]
  have hdropped := mul_le_mul_of_nonneg_left hdrop hcoeffnn
  have hS_le1 : sigmaBarInfinite nu L P ≤
      Ccrude * nu⁻¹ * (1 + (Lstop : ℝ)) +
        8 * C_sell * Cgrow * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) *
          Real.log (L : ℝ) ^ ((9 : ℝ) / 2) * Real.sqrt (L : ℝ) := by
    linarith only [hfinal, hdropped]
  -- Absorb the crude term via `L ≥ LgAbsorb`.
  have hK0nn : (0 : ℝ) ≤ cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) := hK0pos.le
  have hLgAbsorbR : (LgAbsorb : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLgAbsorbL
  have hceil_le :
      ((Ccrude * nu⁻¹ * (1 + (Lstop : ℝ))) /
          ((3 : ℝ) ^ ((9 : ℝ) / 2) * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))) ^ 2 ≤
        (L : ℝ) :=
    le_trans (Nat.le_ceil _) hLgAbsorbR
  have hratio_nonneg : (0 : ℝ) ≤ (Ccrude * nu⁻¹ * (1 + (Lstop : ℝ))) /
      ((3 : ℝ) ^ ((9 : ℝ) / 2) * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)))) := by
    have h1 : (0:ℝ) ≤ Ccrude * nu⁻¹ * (1 + (Lstop : ℝ)) := by
      have hnuinv : (0:ℝ) ≤ nu⁻¹ := (inv_pos.mpr hnu).le
      have h2 : (0:ℝ) ≤ 1 + (Lstop:ℝ) := by positivity
      exact mul_nonneg (mul_nonneg (le_trans zero_le_one hCcrude1) hnuinv) h2
    have h2 : (0:ℝ) < (3:ℝ) ^ ((9:ℝ)/2) * (cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ))) :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hK0pos
    exact div_nonneg h1 h2.le
  have hratio_le_sqrt :
      (Ccrude * nu⁻¹ * (1 + (Lstop : ℝ))) /
          ((3 : ℝ) ^ ((9 : ℝ) / 2) * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)))) ≤
        Real.sqrt (L : ℝ) := by
    have h1 : Real.sqrt (((Ccrude * nu⁻¹ * (1 + (Lstop : ℝ))) /
        ((3 : ℝ) ^ ((9 : ℝ) / 2) * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))))) ^ 2) ≤
        Real.sqrt (L : ℝ) := Real.sqrt_le_sqrt hceil_le
    rwa [Real.sqrt_sq hratio_nonneg] at h1
  have hCcrude'_le :
      Ccrude * nu⁻¹ * (1 + (Lstop : ℝ)) ≤
        (3 : ℝ) ^ ((9 : ℝ) / 2) * (cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ))) *
          Real.sqrt (L : ℝ) := by
    have h2 : (0:ℝ) < (3:ℝ) ^ ((9:ℝ)/2) * (cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ))) :=
      mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hK0pos
    have h3 := mul_le_mul_of_nonneg_left hratio_le_sqrt h2.le
    rw [mul_div_cancel₀] at h3
    · exact h3
    · exact h2.ne'
  have hlogpow_ge3 : (3 : ℝ) ^ ((9 : ℝ) / 2) ≤ Real.log (L : ℝ) ^ ((9 : ℝ) / 2) :=
    Real.rpow_le_rpow (by norm_num) hlogL3' (by norm_num)
  have hCcrude'_le2 :
      Ccrude * nu⁻¹ * (1 + (Lstop : ℝ)) ≤
        cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) *
          Real.sqrt (L : ℝ) := by
    have h2 := mul_le_mul_of_nonneg_left hlogpow_ge3 hK0nn
    have h3 := mul_le_mul_of_nonneg_right h2 hsqrtL_nonneg
    linarith only [hCcrude'_le, h3]
  have hfinal2 : sigmaBarInfinite nu L P ≤
      (8 * C_sell * Cgrow + 1) * cStar ^ (-((3 : ℝ) / 2)) * nu ^ (-(2 : ℝ)) *
        Real.sqrt (L : ℝ) ^ (1 : ℕ) * Real.log (L : ℝ) ^ ((9 : ℝ) / 2) := by
    have hsum := add_le_add hCcrude'_le2 (le_refl
      (8 * C_sell * Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
        Real.log (L:ℝ) ^ ((9:ℝ)/2) * Real.sqrt (L:ℝ)))
    have heqfin : cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) * Real.log (L:ℝ) ^ ((9:ℝ)/2) *
          Real.sqrt (L:ℝ) +
        8 * C_sell * Cgrow * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
          Real.log (L:ℝ) ^ ((9:ℝ)/2) * Real.sqrt (L:ℝ) =
        (8 * C_sell * Cgrow + 1) * cStar ^ (-((3:ℝ)/2)) * nu ^ (-(2:ℝ)) *
          Real.sqrt (L:ℝ) ^ (1:ℕ) * Real.log (L:ℝ) ^ ((9:ℝ)/2) := by
      rw [pow_one]; ring
    rw [heqfin] at hsum
    linarith only [hS_le1, hsum]
  rw [pow_one, hsqrt_eq] at hfinal2
  exact hfinal2

end SuperdiffusionCLT.Section4.SigmaBarComparison
