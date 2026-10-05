/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.Launch

/-!
# Package D3, part 1: the geometric iteration core of node 24 (`e.prime.step.one`)

Proof of `t.weaker.P3` of [AK], Step 2. The statement is
`SuperdiffusionCLT.Frozen.Section4.akhc_weakerP3`;
`Θ_n = thetaCutoff nu L P n`, `Θ₀ = thetaCutoff nu L P 0`.

## Main results here

* `akhcOne_geometricBound`: the pure real-analysis core of the `n`-fold iteration
  ("iterating this `n` times"): for `σ < 4` and a sequence with
  `a(j+1) ≤ 1 + (σ/4) a(j)` for every `j < n`, `a n ≤ 1/(1-σ/4) + (σ/4)^n a 0`.
* `akhcOne_tailSmall`: `(σ/4)^n * a0 ≤ σ/2` given `0 < σ < 1`, `1 ≤ a0` and
  `Real.log (3*a0) ≤ n` (`n ≥ 1` follows since `a0 ≥ 1` gives `log(3a0) ≥ log 3 > 1`).
* `akhcOne_geoBoundOneSigma`: `1/(1-σ/4) ≤ 1 + σ/2` for `0 < σ < 1`.
* `akhcOne_iterate_bound`: combines the three above into the closing numeric estimate
  — `a n ≤ 1 + σ`, given `0 < σ < 1`, `1 ≤ a 0`, `Real.log (3 * a 0) ≤ n`
  and the one-step recursion.

## The iteration count

The printed lower bound `m₀(σ,δ) ≥ 2log(3Θ₀)·N` for `m₀` (node 22, `e.prime.m.naught.lower.bound`)
is stated against the **printed**, uncorrected horizon `N = 2L⌈2δ⁻¹|log σ|⌉`, whereas the one-step
bound and pigeonhole dichotomy here use the corrected horizon `N′` (`akhcLaunchNprimeNat`; route W,
plan §6, F018/F021). Hence `akhcOne_iterate_bound` below is stated purely in terms of an abstract
iteration count `n` with `Real.log (3 * a 0) ≤ n` — a *weaker*, sufficient substitute for the
source's own `2 log(3Θ₀) ≤ n` (see `akhcOne_tailSmall`). The supply of this `n` from the launch
delay `m₀` and the corrected horizon `N′` is carried as an explicit hypothesis on `n` (or, in the
final assembly, on `m₀`) rather than smuggled.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step2

noncomputable section

/-! ## The abstract geometric iteration (pure real analysis) -/

/-- **The `n`-fold iteration bound**, the algebraic core of "iterating this `n` times":
given `a (j+1) ≤ 1 + (σ/4) a j` for every `j < n`, then
`a n ≤ 1/(1-σ/4) + (σ/4)^n * a 0`. No probability content: pure induction on `n`. -/
theorem akhcOne_geometricBound {sigma : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma4 : sigma < 4) :
    ∀ (a : ℕ → ℝ) (n : ℕ), (∀ j : ℕ, j < n → a (j + 1) ≤ 1 + sigma / 4 * a j) →
      a n ≤ 1 / (1 - sigma / 4) + (sigma / 4) ^ n * a 0 := by
  have hden : (0 : ℝ) < 1 - sigma / 4 := by linarith only [hsigma4]
  have hne : (1 - sigma / 4 : ℝ) ≠ 0 := hden.ne'
  intro a n
  induction n with
  | zero =>
      intro _
      have h0 : (0 : ℝ) ≤ 1 / (1 - sigma / 4) := le_of_lt (div_pos (by norm_num) hden)
      have heq : (sigma / 4 : ℝ) ^ 0 * a 0 = a 0 := by ring
      rw [heq]
      linarith only [h0]
  | succ n ih =>
      intro hrec
      have hstep := hrec n (Nat.lt_succ_self n)
      have ihn := ih (fun j hj => hrec j (hj.trans (Nat.lt_succ_self n)))
      have hpos : (0 : ℝ) ≤ sigma / 4 := by linarith only [hsigma0]
      have hmono : sigma / 4 * a n ≤
          sigma / 4 * (1 / (1 - sigma / 4) + (sigma / 4) ^ n * a 0) :=
        mul_le_mul_of_nonneg_left ihn hpos
      have hval : (1 : ℝ) + sigma / 4 * (1 / (1 - sigma / 4)) = 1 / (1 - sigma / 4) := by
        rw [eq_div_iff hne, add_mul, one_mul, mul_assoc, one_div_mul_cancel hne, mul_one]
        ring
      have hpow : sigma / 4 * ((sigma / 4) ^ n * a 0) = (sigma / 4) ^ (n + 1) * a 0 := by
        ring
      have hkey : 1 + sigma / 4 * (1 / (1 - sigma / 4) + (sigma / 4) ^ n * a 0) =
          1 / (1 - sigma / 4) + (sigma / 4) ^ (n + 1) * a 0 := by
        calc 1 + sigma / 4 * (1 / (1 - sigma / 4) + (sigma / 4) ^ n * a 0)
            = (1 + sigma / 4 * (1 / (1 - sigma / 4))) + sigma / 4 * ((sigma / 4) ^ n * a 0) := by
              ring
          _ = 1 / (1 - sigma / 4) + (sigma / 4) ^ (n + 1) * a 0 := by rw [hval, hpow]
      linarith only [hstep, hmono, hkey]

/-! ## The two closing numeric estimates -/

/-- `1/(1-σ/4) ≤ 1+σ/2` for `0 < σ < 1`: equivalent to `σ(2-σ) ≥ 0`. -/
theorem akhcOne_geoBoundOneSigma {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) :
    1 / (1 - sigma / 4) ≤ 1 + sigma / 2 := by
  have hden : (0 : ℝ) < 1 - sigma / 4 := by linarith only [hsigma1]
  rw [div_le_iff₀ hden]
  nlinarith only [hsigma0, hsigma1]

/-- **The geometric tail is small.** For `0 < σ < 1`, `1 ≤ a0` and `Real.log (3 * a0) ≤ n`,
`(σ/4)^n * a0 ≤ σ/2`. Uses `σ^n ≤ σ` (from `0 < σ < 1`, `1 ≤ n`, itself forced by
`1 ≤ log 3 ≤ log (3 a0) ≤ n`) and `a0 ≤ 2 · 4^n` (from `log(3a0) ≤ n < n log 4`, since
`log 4 > 1`). -/
theorem akhcOne_tailSmall {sigma a0 : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ha0 : 1 ≤ a0) {n : ℕ} (hn : Real.log (3 * a0) ≤ (n : ℝ)) :
    (sigma / 4) ^ n * a0 ≤ sigma / 2 := by
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have hexp1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) hexp1
  have h3a0 : (3 : ℝ) ≤ 3 * a0 := by nlinarith only [ha0]
  have hlog3a0 : Real.log 3 ≤ Real.log (3 * a0) :=
    (Real.log_le_log_iff (by norm_num) (by linarith only [h3a0])).mpr h3a0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith only [hlog3, hlog3a0, hn]
  have hn1' : 1 ≤ n := by exact_mod_cast hn1
  -- `σ^n ≤ σ` for `0 ≤ σ ≤ 1`, `1 ≤ n`.
  have hsigman : sigma ^ n ≤ sigma := by
    calc sigma ^ n = sigma ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn1']
      _ = sigma ^ (n - 1) * sigma := by rw [pow_succ]
      _ ≤ 1 * sigma := by
          have hpow1 : sigma ^ (n - 1) ≤ 1 :=
            pow_le_one₀ hsigma0.le hsigma1.le
          exact mul_le_mul_of_nonneg_right hpow1 hsigma0.le
      _ = sigma := one_mul sigma
  -- `4^n ≥ 2 a0` from `log(3a0) ≤ n` and `log 4 > 1`.
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    calc (1 : ℝ) < Real.log 3 := hlog3
      _ ≤ Real.log 4 := (Real.log_le_log_iff (by norm_num) (by norm_num)).mpr (by norm_num)
  have h2a0 : Real.log (2 * a0) ≤ Real.log (3 * a0) := by
    have h23 : (2 : ℝ) * a0 ≤ 3 * a0 := by nlinarith only [ha0]
    exact (Real.log_le_log_iff (by nlinarith only [ha0]) (by linarith only [h3a0])).mpr h23
  have h4n : Real.log (2 * a0) ≤ (n : ℝ) * Real.log 4 := by
    have h1 : Real.log (2 * a0) ≤ (n : ℝ) := by linarith only [h2a0, hn]
    have h2 : (n : ℝ) ≤ (n : ℝ) * Real.log 4 := by
      nlinarith only [hlog4, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
    linarith only [h1, h2]
  have hpow4 : (n : ℝ) * Real.log 4 = Real.log ((4 : ℝ) ^ n) := by
    rw [Real.log_pow]
  have h4nb : Real.log (2 * a0) ≤ Real.log ((4 : ℝ) ^ n) := by rw [hpow4] at h4n; exact h4n
  have h2a0le : (2 : ℝ) * a0 ≤ (4 : ℝ) ^ n :=
    (Real.log_le_log_iff (by nlinarith only [ha0]) (by positivity)).mp h4nb
  have ha04n : a0 / (4 : ℝ) ^ n ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (4:ℝ) ^ n)]
    linarith only [h2a0le]
  have hexpand : (sigma / 4) ^ n * a0 = sigma ^ n * (a0 / (4 : ℝ) ^ n) := by
    rw [div_pow]; ring
  rw [hexpand]
  have hsigman0 : 0 ≤ sigma ^ n := by positivity
  have ha04n0 : 0 ≤ a0 / (4 : ℝ) ^ n := by positivity
  calc sigma ^ n * (a0 / (4 : ℝ) ^ n) ≤ sigma * (a0 / (4 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_right hsigman ha04n0
    _ ≤ sigma * (1 / 2) := mul_le_mul_of_nonneg_left ha04n hsigma0.le
    _ = sigma / 2 := by ring

/-- **The closing numeric estimate of Step 2's iteration**: given the
one-step recursion `a(j+1) ≤ 1+(σ/4)a(j)` for `j < n`, `0 < σ < 1`, `1 ≤ a0` and
`Real.log (3 * a0) ≤ n`, then `a n ≤ 1 + σ`. -/
theorem akhcOne_iterate_bound {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    {a : ℕ → ℝ} (ha0 : 1 ≤ a 0) {n : ℕ} (hn : Real.log (3 * a 0) ≤ (n : ℝ))
    (hrec : ∀ j : ℕ, j < n → a (j + 1) ≤ 1 + sigma / 4 * a j) :
    a n ≤ 1 + sigma := by
  have hgeo := akhcOne_geometricBound hsigma0.le (by linarith only [hsigma1] : sigma < 4) a n hrec
  have hone := akhcOne_geoBoundOneSigma hsigma0 hsigma1
  have htail := akhcOne_tailSmall hsigma0 hsigma1 ha0 hn
  linarith only [hgeo, hone, htail]

/-! ## Node 39: `…step2.one.step.bound.route.trivial` -/

end

end SuperdiffusionCLT.AKHC61.Step2
