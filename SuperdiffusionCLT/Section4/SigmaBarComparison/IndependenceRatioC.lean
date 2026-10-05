/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.SigmaBarComparison.IndependenceRatioB
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Section4.LNaught.Monotone
public import SuperdiffusionCLT.Section4.LNaught.Threshold
public import SuperdiffusionCLT.Section4.LNaught.LogCompare
public import SuperdiffusionCLT.Section4.LNaught.SstarLowerB
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

/-!
# The `≤ 1/8` absorption, from `lNaught_sstar_lower`

This file derives the absorption `e.L.vs.Lnaught` from
`SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower`
(`Section4/LNaught/SstarLowerB.lean`): `sbIndep_absorption_le_eighth` takes only
`hd : 2 ≤ d` (`lNaught_sstar_lower`'s own hypothesis, needed by the root
lower bound `sigmaBarStar_lower_bound` it is built on) and obtains `hSstarLower`
by applying `lNaught_sstar_lower d hd`, with **no extra conjunct on its own witness
`c`** (see below). It is combined with `lNaught_absorbs`,
`lNaught_ge` (`Section4/LNaught/Threshold.lean`), `ShellLawJ5.cStar_le_two`
(`Assumptions/ShellLaw/J5Consequences.lean`), a self-contained,
elementary lemma `sbIndep_lNaught_ge_linear` (`lNaught` grows at least
linearly in its leading constant `C`, proved directly from the
closed-form `lNaught` formula, not needing the sharp crossing machinery), and
`lNaught_mul_M_le` (`Section4/LNaught/LogCompare.lean`).

## The `M`-inflation

The crude ratio estimate below needs `c ≥ 256` for the first term's `≤ 1/16` step, but the
witness `c` of the root lower bound is of order `c_r² / 2^10` (`c_r` the root bound's own
constant), far below `1`, not `256`. So the argument does not assume anything on `c`:
instead, `M`-inflate
`hSstarLower`'s own `M`-argument by `K' := max 1 (256 / c)`, so that
`256 ≤ c * K'` **unconditionally**, for whatever (possibly tiny) `c > 0`
`lNaught_sstar_lower` supplies. Concretely, `hSstarLower` is
applied at `M := K' * (C * M)`; the
needed threshold `lNaught C0star (K' * (C*M)) ... ≤ ell` is recovered
from the *standing* `lNaught C (C*M) ... ≤ ell` (`hLnaught`) via

```
lNaught_mul_M_le (C M alpha cStar nu K K' : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (halpha : alpha < 1) (hcStar : 0 < cStar) (hnu : 0 < nu) (hK : 0 ≤ K)
    (hK' : 1 ≤ K') :
    lNaught C (K' * M) alpha cStar nu K ≤
      lNaught (C * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ)) M alpha cStar nu K
```

(applied directly at its own `C := C0star`, `M := C * M`) followed by
`lNaught_mono_const`, using that the output
threshold `C0` is chosen `≥ Cthresh2 := C0star * K' * (1 + log K' / log 2)^12`
(a fixed real, since `K'` depends only on `c` and `C0star`, not on the later
universally-quantified `C`).

## The absorption

`hSstarLower`'s conclusion, applied at `L' := ell`, `h := ell` with the
(now `K'`-inflated) substitution `M ↦ K' * (C * M)`, gives
`shom_ell² ≥ c * K' * (C*M) * ell^α log³ ell ≥ 256 * (C*M) * ell^α log³ ell`
(using `256 ≤ c * K'`). Substituted into the target display's first term
`C * M * L^α * shom_ell⁻² * log³ L`, the factor `C * M` cancels **exactly**
against the same factor in the lower bound, leaving `ratio / 256` where
`ratio := (L^α log³L)/(ell^α log³ell) ≤ 16` (from `L ≤ 2 ell`, via
`lNaught_absorbs`, and `ell ≥ 9`, via `lNaught_ge`), giving `≤ 1/16` on the
first term with **no hypothesis on `c` beyond `0 < c`**. The second term
`C * L^{-99}` needs no hypothesis on `c` either: it is handled by
`sbIndep_lNaught_ge_linear` alone (`L ≥ ell ≥ lNaught C (C*M) ... ≥ 16 C`, so
`L^{99} ≥ L ≥ 16 C`, giving `C * L^{-99} ≤ 1/16`).

`sbIndep_absorption_le_eighth`'s conclusion also returns the byproduct fact
`256 * C ≤ shom_ell²` (from the same `hInfSq256` used for the first term, via
`M ≥ 1` and `ell^α log³ell ≥ 1` at `ell ≥ 9`): `sbIndep_mainB` uses this to
convert its own near-additivity bound's `σ̄_ell⁻¹`-carrying second term
into the `σ̄_ell⁻¹`-free form this theorem's own second term already is
(the role the deleted `hLvsLnaught`'s first conjunct used to play).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.SigmaBarComparison

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## `sigmaBarInfinite` dominates `sigmaBarStarScalar` at any finite cube -/

/-- `σ̄_m ≥ σ̄_m(cu_n)` for every finite cube index `n`: `σ̄_m` is the
inverse of an infimum (`sigmaBarStarInvLimit`), which lies below every term of
the sequence it is the infimum of, and inverting (both sides positive)
reverses the order. -/
theorem sbIndep_sigmaBarStarScalar_le_sigmaBarInfinite {P : ProbabilityMeasure (ShellSeq d)}
    {nu : ℝ} (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m n : ℕ) :
    sigmaBarStarScalar nu m P (cubeSet (originCube d (n : ℤ))) ≤ sigmaBarInfinite nu m P := by
  have hpos := sigmaBarStarInvSeq_pos hnu m hPrefix hJ2 hJ3 hJ4 n
  rw [sigmaBarStarScalar_eq_inv hnu m hJ4 (n : ℤ) hpos, sigmaBarInfinite]
  have hle : sigmaBarStarInvLimit nu m P ≤ sigmaBarStarInvSeq nu m P n :=
    sigmaBarStarInvLimit_le hnu m hPrefix hJ2 hJ3 hJ4 n
  have hlimpos : 0 < sigmaBarStarInvLimit nu m P :=
    sigmaBarStarInvLimit_pos hnu m hPrefix hJ2 hJ3 hJ4
  exact inv_anti₀ hlimpos hle

theorem sbIndep_sigmaBarStarScalar_pos {P : ProbabilityMeasure (ShellSeq d)}
    {nu : ℝ} (hnu : 0 < nu) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (m n : ℕ) :
    0 < sigmaBarStarScalar nu m P (cubeSet (originCube d (n : ℤ))) := by
  have hpos := sigmaBarStarInvSeq_pos hnu m hPrefix hJ2 hJ3 hJ4 n
  rw [sigmaBarStarScalar_eq_inv hnu m hJ4 (n : ℤ) hpos]
  exact inv_pos.2 hpos

/-! ## A raw, elementary linear-in-`C` lower bound on `lNaught` -/

/-- **`lNaught` grows at least linearly in its leading constant `C`**, once
`C ≥ 128` and `M ≥ C`: `16 * C ≤ lNaught C M alpha cStar nu K`. This is a
crude, self-contained bound (elementary monotonicity of `Real.rpow`/`log`,
not the sharp `lNaught_crossing_core` machinery of `lNaught_threshold`): the
log-argument `2 + (M+1+K)cStar⁻³/(nu(1-alpha))` clears `Real.exp 1` once
`M ≥ C ≥ 128`, so the `log^12` factor is `≥ 1` and can be dropped; the
denominator `(1-alpha)^12 nu^4 ≤ 1` can be dropped too; what remains,
`C * (M+1+K) * cStar⁻³ ≥ C * C / 8 ≥ 16 C` (using `C ≥ 128`), is already the
target once the outer `^{1/(1-alpha)}` (exponent `≥ 1` on a base `≥ 1`) only
increases it further. Used only for the `C * L^{-99} ≤ 1/16` half of
`sbIndep_absorption_le_eighth`. -/
theorem sbIndep_lNaught_ge_linear {C M alpha cStar nu K : ℝ}
    (hC128 : (128 : ℝ) ≤ C) (hMC : C ≤ M) (hcStar : 0 < cStar) (hcStar2 : cStar ≤ 2)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : 0 ≤ K) (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    16 * C ≤ SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le (by norm_num) hC128
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le hCpos hMC
  have hcStar3ge : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hcStar hcStar2 (by norm_num : (-(3 : ℝ)) ≤ 0)
    have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [h2] at h; exact h
  have hcStar3pos : (0 : ℝ) < cStar ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hcStar _
  have hMK1 : M ≤ M + 1 + K := by linarith only [hK]
  have hN : (16 : ℝ) * C ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have step1 : C * M * cStar ^ (-(3 : ℝ)) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hcStar3pos.le
      apply mul_le_mul_of_nonneg_left hMK1 hCpos.le
    have step2 : C * M * (1 / 8 : ℝ) ≤ C * M * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcStar3ge (mul_pos hCpos hMpos).le
    have step3 : C * C * (1 / 8 : ℝ) ≤ C * M * (1 / 8 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      apply mul_le_mul_of_nonneg_left hMC hCpos.le
    have step4 : (16 : ℝ) * C ≤ C * C * (1 / 8 : ℝ) := by
      have hh : (0 : ℝ) ≤ (C - 128) * C := mul_nonneg (by linarith only [hC128]) hCpos.le
      nlinarith only [hh]
    linarith only [step1, step2, step3, step4]
  have halphapos : (0 : ℝ) < 1 - alpha := by linarith only [halpha1]
  have halphale1 : (1 - alpha) ≤ 1 := by linarith only [halpha0]
  have hD1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) :=
          Real.rpow_le_rpow halphapos.le halphale1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hD1pos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) := Real.rpow_pos_of_pos halphapos _
  have hD2 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hD2pos : (0 : ℝ) < nu ^ (4 : ℝ) := Real.rpow_pos_of_pos hnu _
  have hDpos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := mul_pos hD1pos hD2pos
  have hDle1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * 1 :=
          mul_le_mul hD1 hD2 hD2pos.le (by norm_num)
      _ = 1 := by norm_num
  have hNumNonneg : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have hMK0 : (0 : ℝ) ≤ M + 1 + K := by linarith only [hMpos, hK]
    positivity
  have hDivGe : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    rw [le_div_iff₀ hDpos]
    exact mul_le_of_le_one_right hNumNonneg hDle1
  have hnua_pos : (0 : ℝ) < nu * (1 - alpha) := mul_pos hnu halphapos
  have hnua_le1 : nu * (1 - alpha) ≤ 1 := by
    calc nu * (1 - alpha) ≤ 1 * 1 := mul_le_mul hnu1 halphale1 halphapos.le (by norm_num)
      _ = 1 := by norm_num
  have hFracGe : (16 : ℝ) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    have hnum : (16 : ℝ) * (nu * (1 - alpha)) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      have h1 : M * cStar ^ (-(3 : ℝ)) ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hMK1 hcStar3pos.le
      have h2 : M * (1 / 8 : ℝ) ≤ M * cStar ^ (-(3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcStar3ge hMpos.le
      have h3 : C * (1 / 8 : ℝ) ≤ M * (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_right hMC (by norm_num)
      have h4 : (16 : ℝ) * (nu * (1 - alpha)) ≤ (16 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hnua_le1 (by norm_num)
      have h5 : (16 : ℝ) * 1 ≤ C * (1 / 8 : ℝ) := by nlinarith only [hC128]
      linarith only [h1, h2, h3, h4, h5]
    rw [le_div_iff₀ hnua_pos]
    exact hnum
  have hArgGe : (18 : ℝ) ≤ 2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha)) := by
    linarith only [hFracGe]
  have he18 : Real.exp 1 < (18 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlogArgge1 :
      (1 : ℝ) ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans he18.le hArgGe)
    rwa [Real.log_exp] at h
  have hlog12ge1 :
      (1 : ℝ) ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^
        (12 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (12 : ℝ) := (Real.one_rpow 12).symm
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hlogArgge1 (by norm_num)
  have hDivNonneg : (0 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) :=
    div_nonneg hNumNonneg hDpos.le
  have hInnerGe : (16 : ℝ) * C ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    calc (16 : ℝ) * C ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := hN
      _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := hDivGe
      _ = (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) * 1 :=
          by ring
      _ ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
          mul_le_mul_of_nonneg_left hlog12ge1 hDivNonneg
  have hInnerGe1 : (1 : ℝ) ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have h16C1 : (1 : ℝ) ≤ 16 * C := by nlinarith only [hC128]
    linarith only [h16C1, hInnerGe]
  have hexp_ge1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ halphapos]; linarith only [halphale1]
  calc (16 : ℝ) * C ≤
      (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := hInnerGe
    _ = _ ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ ^ ((1 : ℝ) / (1 - alpha)) := Real.rpow_le_rpow_of_exponent_le hInnerGe1 hexp_ge1

/-! ## The `≤ 1/8` absorption -/

/-- **The absorption `RHS(C) ≤ 1/8`**, derived from `lNaught_sstar_lower`
(the printed absorption `e.L.vs.Lnaught`), `lNaught_absorbs`,
`lNaught_ge` (`Section4/LNaught/Threshold.lean`), `ShellLawJ5.cStar_le_two`,
and `lNaught_mul_M_le` (`Section4/LNaught/LogCompare.lean`), all applied
directly; the only hypothesis this
theorem carries is `hd : 2 ≤ d`, `lNaught_sstar_lower`'s own requirement
(inherited from the root bound `sigmaBarStar_lower_bound`, which is
proved only for `d ≥ 2`, matching the standing scope of the paper). See the module docstring
for the `M`-inflation mechanism `lNaught_mul_M_le` drives; no hypothesis `256 ≤ c` on
`lNaught_sstar_lower`'s own witness `c` is needed. -/
theorem sbIndep_absorption_le_eighth (hd : 2 ≤ d) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ (nu cStar K : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : ProbabilityMeasure (ShellSeq d))
          (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P),
          ShellLawJ1Restriction d P → ShellLawJ4 d P → ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ alpha M : ℝ, 0 ≤ alpha → alpha < 1 → 1 ≤ M →
            ∀ L ell : ℕ, ell ≤ L →
              SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤
                  (ell : ℝ) →
              (L : ℝ) - M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (ell : ℝ) →
              (256 : ℝ) * C ≤ sigmaBarInfinite nu ell P ^ 2 ∧
                C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
                      Real.log (L : ℝ) ^ (3 : ℝ) +
                    C * (L : ℝ) ^ (-(99 : ℝ)) ≤ (1 : ℝ) / 8 := by
  obtain ⟨C0star, hC0star1, c, hcpos, hSstarLower⟩ :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_sstar_lower d hd
  obtain ⟨CA0, hCA01, hAbsorbs⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_absorbs
  obtain ⟨CG0, hCG01, hGe⟩ := SuperdiffusionCLT.Section4.LNaught.lNaught_ge
  -- `M`-inflation: `lNaught_sstar_lower`'s witness `c` may be far below `256`
  -- (`c` is of order `c_r²/2^10`), so inflate its
  -- own `M`-argument by `K' := max 1 (256/c)`, giving `256 ≤ c * K'`
  -- unconditionally (no hypothesis on `c` itself needed beyond `0 < c`).
  set K' : ℝ := max 1 (256 / c) with hK'def
  have hK'1 : (1 : ℝ) ≤ K' := le_max_left _ _
  have hK'ge : (256 / c : ℝ) ≤ K' := le_max_right _ _
  have hcK'256 : (256 : ℝ) ≤ c * K' := by
    have h := mul_le_mul_of_nonneg_left hK'ge hcpos.le
    have heq : c * (256 / c) = 256 := by field_simp
    linarith only [h, heq]
  have hlogK'nn : (0 : ℝ) ≤ Real.log K' := Real.log_nonneg hK'1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbaseK'pos : (0 : ℝ) < 1 + Real.log K' / Real.log 2 := by positivity
  have hpow12pos : (0 : ℝ) < (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) :=
    Real.rpow_pos_of_pos hbaseK'pos _
  set Cthresh2 : ℝ := C0star * K' * (1 + Real.log K' / Real.log 2) ^ (12 : ℝ) with hCthresh2def
  have hCthresh2pos : (0 : ℝ) < Cthresh2 := by
    rw [hCthresh2def]
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one hC0star1) (lt_of_lt_of_le zero_lt_one hK'1))
      hpow12pos
  refine ⟨max 128 (max C0star (max CA0 (max CG0 Cthresh2))),
    le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro C hCC0 nu cStar K hnu hnu1 P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 alpha M hα0 hα1 hM L ell hell
    hLnaught hscale
  have hC128 : (128 : ℝ) ≤ C := le_trans (le_max_left _ _) hCC0
  have hCC0star : C0star ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCC0
  have hCCA0 : CA0 ≤ C :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hCC0
  have hCCG0 : CG0 ≤ C :=
    le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hCC0
  have hCCthresh2 : Cthresh2 ≤ C :=
    le_trans (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hCC0
  have hC2 : (2 : ℝ) ≤ C := le_trans (by norm_num) hC128
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC2
  have hCM1 : (1 : ℝ) ≤ C * M := le_trans hM (le_mul_of_one_le_left (le_trans zero_le_one hM) hC1)
  have hCMpos : (0 : ℝ) < C * M := lt_of_lt_of_le zero_lt_one hCM1
  have hcStar2 := hJ5.cStar_le_two
  have hcStarpos := hJ5.cStar_pos
  have hKnn : (0 : ℝ) ≤ K := hJ5.K_pos.le
  have hellL_le : (ell : ℝ) ≤ (L : ℝ) := by exact_mod_cast hell
  have hLnaughtAtL : SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K ≤
      (L : ℝ) := le_trans hLnaught hellL_le
  -- Step 1: `ell ≥ L/2` (crude), via `lNaught_absorbs` at `M ↦ C*M`.
  have hAbsorbsAtL := hAbsorbs C hCCA0 (C * M) hCM1 alpha hα0 hα1 cStar hcStarpos hcStar2 nu hnu
    hnu1 K hKnn L hLnaughtAtL
  have hML_le : M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤ (L : ℝ) / 2 := by
    have heq : (C * M) * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) =
        C * (M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
    rw [heq] at hAbsorbsAtL
    have hCnn : (0 : ℝ) ≤ C := le_trans zero_le_one hC1
    have hMLnn : (0 : ℝ) ≤ M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) := by
      have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ alpha := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hlog0 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
      have hlog30 : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
      have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM
      positivity
    nlinarith only [hAbsorbsAtL, hC1, hMLnn]
  have hell2L : (L : ℝ) / 2 ≤ (ell : ℝ) := by linarith only [hscale, hML_le]
  have hL2ell : (L : ℝ) ≤ 2 * (ell : ℝ) := by linarith only [hell2L]
  -- Step 2: `ell ≥ 9` (via `lNaught_ge`).
  have hGeAtEll : (8 : ℝ) < SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar
      nu K := hGe C hCCG0 (C * M) hCM1 alpha hα0 hα1 cStar hcStarpos hcStar2 nu hnu hnu1 K hKnn
  have hell8 : (8 : ℝ) < (ell : ℝ) := lt_of_lt_of_le hGeAtEll hLnaught
  have hell9 : (9 : ℕ) ≤ ell := by exact_mod_cast hell8
  have hellRpos : (0 : ℝ) < (ell : ℝ) := by
    have : (0 : ℝ) < (9 : ℝ) := by norm_num
    calc (0 : ℝ) < 9 := this
      _ ≤ (ell : ℝ) := by exact_mod_cast hell9
  have hLRpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le hellRpos hellL_le
  -- Step 3: the `p.sstar.lower.bound`-style estimate at `L' := ell`, `h := ell`,
  -- with `hSstarLower`'s own `M`-argument inflated to `K' * (C*M)`: the needed
  -- threshold `lNaught C0star (K' * (C*M)) ... ≤ ell` follows from the
  -- standing `hLnaught : lNaught C (C*M) ... ≤ ell` via
  -- `lNaught_mul_M_le` (at its own `C`-argument `:= C0star`,
  -- `M`-argument `:= C*M`) followed by `lNaught_mono_const` (using
  -- `Cthresh2 ≤ C`, i.e. `hCCthresh2`).
  have hCMnn : (0 : ℝ) ≤ C * M := hCMpos.le
  have hC0starnn : (0 : ℝ) ≤ C0star := le_trans zero_le_one hC0star1
  have hMulMAtEll := SuperdiffusionCLT.Section4.LNaught.lNaught_mul_M_le C0star (C * M)
    alpha cStar nu K K' hC0starnn hCMnn hα1 hcStarpos hnu hKnn hK'1
  have hMonoC : SuperdiffusionCLT.Frozen.Section4.lNaught Cthresh2 (C * M) alpha cStar nu K ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K :=
    SuperdiffusionCLT.Section4.LNaught.lNaught_mono_const hCthresh2pos.le hCCthresh2 hCMnn
      hKnn hcStarpos hnu hα1
  have hLnaughtK' : SuperdiffusionCLT.Frozen.Section4.lNaught C0star (K' * (C * M)) alpha
      cStar nu K ≤ (ell : ℝ) :=
    le_trans hMulMAtEll (le_trans hMonoC hLnaught)
  have hK'CM1 : (1 : ℝ) ≤ K' * (C * M) := le_trans hCM1 (le_mul_of_one_le_left hCMpos.le hK'1)
  have hSstarAtEll := hSstarLower C0star le_rfl (K' * (C * M)) hK'CM1 alpha hα0 hα1 cStar
    hcStarpos hcStar2 nu hnu hnu1 K hKnn P hPrefix hJ2 hJ3 hJ1V2 hJ4 hJ5 ell hLnaughtK' ell
    (by linarith only [hellRpos]) le_rfl
  have hStarScalarLe := sbIndep_sigmaBarStarScalar_le_sigmaBarInfinite (d := d) hnu hPrefix hJ2
    hJ3 hJ4 ell ell
  have hStarScalarPos := sbIndep_sigmaBarStarScalar_pos (d := d) hnu hPrefix hJ2 hJ3 hJ4 ell ell
  have hShomEllPos : 0 < sigmaBarInfinite nu ell P := lt_of_lt_of_le hStarScalarPos hStarScalarLe
  -- Step 4: the `ell`-side numeric facts (`log ell > 1`, `L ≤ 2 ell`, `ell ≥ 9`).
  have hellR9 : (9 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell9
  have hLR9 : (9 : ℝ) ≤ (L : ℝ) := le_trans hellR9 hellL_le
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := le_trans (by norm_num) hLR9
  have he9 : Real.exp 1 < (9 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlogellgt1 : (1 : ℝ) < Real.log (ell : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he9 hellR9)
    rwa [Real.log_exp] at h
  have hellalphanonneg : (0 : ℝ) ≤ (ell : ℝ) ^ alpha := Real.rpow_nonneg hellRpos.le alpha
  have hlog3ellnonneg : (0 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) :=
    Real.rpow_nonneg (by linarith only [hlogellgt1]) 3
  have hlogLnonneg : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  -- Step 5: the ratio bound `L^α log³L ≤ 16 * ell^α log³ell`.
  have hLalpha_le : (L : ℝ) ^ alpha ≤ 2 * (ell : ℝ) ^ alpha := by
    have h1 : (L : ℝ) ^ alpha ≤ (2 * (ell : ℝ)) ^ alpha :=
      Real.rpow_le_rpow hLRpos.le hL2ell hα0
    have h2 : (2 * (ell : ℝ)) ^ alpha = (2 : ℝ) ^ alpha * (ell : ℝ) ^ alpha :=
      Real.mul_rpow (by norm_num) hellRpos.le
    have h3 : (2 : ℝ) ^ alpha ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
    have h4 : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one 2
    calc (L : ℝ) ^ alpha ≤ (2 * (ell : ℝ)) ^ alpha := h1
      _ = (2 : ℝ) ^ alpha * (ell : ℝ) ^ alpha := h2
      _ ≤ (2 : ℝ) ^ (1 : ℝ) * (ell : ℝ) ^ alpha :=
          mul_le_mul_of_nonneg_right h3 hellalphanonneg
      _ = 2 * (ell : ℝ) ^ alpha := by rw [h4]
  have hlogL_le : Real.log (L : ℝ) ≤ 2 * Real.log (ell : ℝ) := by
    have h1 : Real.log (L : ℝ) ≤ Real.log (2 * (ell : ℝ)) := Real.log_le_log hLRpos hL2ell
    have h2 : Real.log (2 * (ell : ℝ)) = Real.log 2 + Real.log (ell : ℝ) :=
      Real.log_mul (by norm_num) hellRpos.ne'
    have h3 : Real.log (2 : ℝ) < 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [h1, h2, h3, hlogellgt1]
  have hlog3_le : Real.log (L : ℝ) ^ (3 : ℝ) ≤ 8 * Real.log (ell : ℝ) ^ (3 : ℝ) := by
    have h1 : Real.log (L : ℝ) ^ (3 : ℝ) ≤ (2 * Real.log (ell : ℝ)) ^ (3 : ℝ) :=
      Real.rpow_le_rpow hlogLnonneg hlogL_le (by norm_num)
    have h2 : (2 * Real.log (ell : ℝ)) ^ (3 : ℝ) =
        (2 : ℝ) ^ (3 : ℝ) * Real.log (ell : ℝ) ^ (3 : ℝ) :=
      Real.mul_rpow (by norm_num) (by linarith only [hlogellgt1])
    have h3 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    calc Real.log (L : ℝ) ^ (3 : ℝ) ≤ (2 * Real.log (ell : ℝ)) ^ (3 : ℝ) := h1
      _ = (2 : ℝ) ^ (3 : ℝ) * Real.log (ell : ℝ) ^ (3 : ℝ) := h2
      _ = 8 * Real.log (ell : ℝ) ^ (3 : ℝ) := by rw [h3]
  have hlog3Lnonneg : (0 : ℝ) ≤ Real.log (L : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlogLnonneg 3
  have hRatio : (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
      16 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by
    calc (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
          (2 * (ell : ℝ) ^ alpha) * Real.log (L : ℝ) ^ (3 : ℝ) :=
          mul_le_mul_of_nonneg_right hLalpha_le hlog3Lnonneg
      _ ≤ (2 * (ell : ℝ) ^ alpha) * (8 * Real.log (ell : ℝ) ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog3_le (by positivity)
      _ = 16 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by ring
  -- Step 6: the first term `≤ 1/16`. `256 ≤ c * K'` (`hcK'256`) is already
  -- baked into `hSstarAtEll`'s `M`-argument `K' * (C*M)`, so no `hkey`
  -- division step is needed.
  have hEnn : (0 : ℝ) ≤ (C * M) * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) :=
    mul_nonneg hCMpos.le (mul_nonneg hellalphanonneg hlog3ellnonneg)
  have hInfSq256 : (256 : ℝ) * (C * M) * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) ≤
      sigmaBarInfinite nu ell P ^ 2 := by
    calc (256 : ℝ) * (C * M) * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)
        = 256 * ((C * M) * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) := by ring
      _ ≤ (c * K') * ((C * M) * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) :=
          mul_le_mul_of_nonneg_right hcK'256 hEnn
      _ = c * (K' * (C * M)) * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by ring
      _ ≤ sigmaBarStarScalar nu ell P (cubeSet (originCube d (ell : ℤ))) ^ 2 := hSstarAtEll
      _ ≤ sigmaBarInfinite nu ell P ^ 2 := pow_le_pow_left₀ hStarScalarPos.le hStarScalarLe 2
  have hNumBound : C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ) ≤
      (1 / 16 : ℝ) * sigmaBarInfinite nu ell P ^ 2 := by
    calc C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)
        = C * M * ((L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) := by ring
      _ ≤ C * M * (16 * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hRatio hCMpos.le
      _ = (1 / 16 : ℝ) * (256 * (C * M) * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) := by
          ring
      _ ≤ (1 / 16 : ℝ) * sigmaBarInfinite nu ell P ^ 2 :=
          mul_le_mul_of_nonneg_left hInfSq256 (by norm_num)
  have hShomEllSqPos : (0 : ℝ) < sigmaBarInfinite nu ell P ^ 2 := pow_pos hShomEllPos 2
  have hrpow2 : sigmaBarInfinite nu ell P ^ (2 : ℝ) = sigmaBarInfinite nu ell P ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hShomEllRpow :
      sigmaBarInfinite nu ell P ^ (-(2 : ℝ)) = (sigmaBarInfinite nu ell P ^ 2)⁻¹ := by
    rw [Real.rpow_neg hShomEllPos.le, hrpow2]
  have hterm1eq : C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) =
      (C * M * (L : ℝ) ^ alpha * Real.log (L : ℝ) ^ (3 : ℝ)) *
        (sigmaBarInfinite nu ell P ^ 2)⁻¹ := by
    rw [hShomEllRpow]; ring
  have hterm1_le : C * M * (L : ℝ) ^ alpha * (sigmaBarInfinite nu ell P) ^ (-(2 : ℝ)) *
      Real.log (L : ℝ) ^ (3 : ℝ) ≤ (1 / 16 : ℝ) := by
    rw [hterm1eq, ← div_eq_mul_inv, div_le_iff₀ hShomEllSqPos]
    exact hNumBound
  -- Step 7: the second term `≤ 1/16`, via `sbIndep_lNaught_ge_linear`.
  have hMC' : C ≤ C * M := le_mul_of_one_le_right (le_trans zero_le_one hC1) hM
  have hLinGe : (16 : ℝ) * C ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C (C * M) alpha cStar nu K :=
    sbIndep_lNaught_ge_linear hC128 hMC' hcStarpos hcStar2 hnu hnu1 hKnn hα0 hα1
  have hL16C : (16 : ℝ) * C ≤ (L : ℝ) := le_trans hLinGe hLnaughtAtL
  have hLrpow99pos : (0 : ℝ) < (L : ℝ) ^ (99 : ℝ) := Real.rpow_pos_of_pos hLRpos _
  have hL99 : (L : ℝ) ≤ (L : ℝ) ^ (99 : ℝ) := by
    calc (L : ℝ) = (L : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (L : ℝ) ^ (99 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hL99C : (16 : ℝ) * C ≤ (L : ℝ) ^ (99 : ℝ) := le_trans hL16C hL99
  have hterm2 : C * (L : ℝ) ^ (-(99 : ℝ)) ≤ (1 / 16 : ℝ) := by
    rw [Real.rpow_neg hLRpos.le, ← div_eq_mul_inv, div_le_iff₀ hLrpow99pos]
    linarith only [hL99C]
  -- Step 8: `256 * C ≤ shom_ell²`, a byproduct of `hInfSq256` (used by
  -- `sbIndep_mainB` to convert its own near-additivity bound's `σ̄_ell⁻¹`-
  -- carrying second term into the `σ̄_ell⁻¹`-free form this theorem's own
  -- second term already is), via `M ≥ 1`.
  have hSigmaSq : (256 : ℝ) * C ≤ sigmaBarInfinite nu ell P ^ 2 := by
    have h256Cnn : (0 : ℝ) ≤ 256 * C := by linarith only [hC128]
    calc (256 : ℝ) * C = 256 * C * 1 := by ring
      _ ≤ 256 * C * M := mul_le_mul_of_nonneg_left hM h256Cnn
      _ = 256 * (C * M) := by ring
      _ ≤ 256 * (C * M) * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by
          have hCM256nn : (0 : ℝ) ≤ 256 * (C * M) := by positivity
          have hprodge1 : (1 : ℝ) ≤ (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by
            have hell1 : (1 : ℝ) ≤ (ell : ℝ) := le_trans (by norm_num) hellR9
            have hellalphage1 : (1 : ℝ) ≤ (ell : ℝ) ^ alpha := by
              calc (1 : ℝ) = (ell : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
                _ ≤ (ell : ℝ) ^ alpha := Real.rpow_le_rpow_of_exponent_le hell1 hα0
            have hlog3ellge1 : (1 : ℝ) ≤ Real.log (ell : ℝ) ^ (3 : ℝ) := by
              calc (1 : ℝ) = (1 : ℝ) ^ (3 : ℝ) := (Real.one_rpow 3).symm
                _ ≤ Real.log (ell : ℝ) ^ (3 : ℝ) :=
                    Real.rpow_le_rpow (by norm_num) hlogellgt1.le (by norm_num)
            calc (1 : ℝ) = 1 * 1 := by norm_num
              _ ≤ (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) :=
                  mul_le_mul hellalphage1 hlog3ellge1 (by norm_num)
                    (by linarith only [hellalphage1])
          calc 256 * (C * M) = 256 * (C * M) * 1 := by ring
            _ ≤ 256 * (C * M) * ((ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ)) :=
                mul_le_mul_of_nonneg_left hprodge1 hCM256nn
            _ = 256 * (C * M) * (ell : ℝ) ^ alpha * Real.log (ell : ℝ) ^ (3 : ℝ) := by ring
      _ ≤ sigmaBarInfinite nu ell P ^ 2 := hInfSq256
  exact ⟨hSigmaSq, by linarith only [hterm1_le, hterm2]⟩

end

end SuperdiffusionCLT.Section4.SigmaBarComparison
