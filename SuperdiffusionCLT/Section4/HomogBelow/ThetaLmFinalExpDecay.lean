/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
**The exponential-remainder bound** for the Step 2/Step 3 assembly in the proof of
`p.homog.below`.

The conclusion of [AK, Theorem 6.1] (`homogBelow_akhcApplication`'s `hStep`,
`ThetaLmAssemblyAKHCApp.lean`) leaves, after each of Step 3's two
applications, an additive error term `C61 * 3 ^ (-(kappa * (n - m -
4*m0)))`, where the gap `n - m - 4*m0` collapses to exactly `m0` at both
applications (`homogBelow_scaleDefs`'s `mtilde+4*m0≤n` together with
`n=mtilde+5*m0`, and similarly `mtilde'+4*m0≤m` with `m=mtilde'+5*m0`).
Since `m0 := ⌈Cprime * (Real.log N)^2⌉₊` for the log-argument `N` used by
either branch of the `m₀`-threshold (`M0ThresholdB.lean`'s `N := L`,
`M0ThresholdC.lean`'s `N := m`), this file proves that `C61 * 3 ^
(-(kappa*m0))` is dominated by any fixed negative power of `N`, once
`Cprime` is large enough (depending on `kappa, C61` and the target power
`p`) — this is the third smallness-style threshold, matching the paper's own
`3^{-κm0}≤m̃^{-6000}` estimate in the proof of `p.homog.below`. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

/-- `1 < Real.log 3`. -/
private theorem homogBelow_one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
  linarith only [Real.exp_one_lt_d9]

/-- **The exponential-remainder bound**: for any decay rate `kappa > 0`
(matching `min alpha61 (1/4)` in `homogBelow_akhcApplication`'s remainder
term), constant `C61 ≥ 1`, and target power `p` (any sign; used at `p ≥ 0`,
e.g. `p = 3000` or `p = 6000`), there is a threshold `C0` such that for
every `Cprime ≥ C0` and every natural `N ≥ 3`, setting `m0 :=
⌈Cprime * (Real.log N)^2⌉₊`, `C61 * 3 ^ (-(kappa * m0)) ≤ N ^ (-p)`. -/
theorem homogBelow_expDecay_le_polyDecay
    (kappa : ℝ) (hkappa : 0 < kappa)
    (C61 : ℝ) (hC61 : 1 ≤ C61)
    (p : ℝ) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ Cprime : ℝ, C0 ≤ Cprime →
      ∀ N : ℕ, 3 ≤ N →
        C61 * (3:ℝ) ^ (-(kappa * ((⌈Cprime * (Real.log (N:ℝ)) ^ 2⌉₊ : ℕ) : ℝ))) ≤
          (N:ℝ) ^ (-(p)) := by
  have hlog3pos : (0:ℝ) < Real.log 3 := lt_trans one_pos homogBelow_one_lt_log_three
  refine ⟨max 1 ((p + Real.log C61 + 1) / (kappa * Real.log 3)), le_max_left _ _, ?_⟩
  intro Cprime hCprime N hN3
  have hCpos : (0:ℝ) < Cprime := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hCprime)
  have hNR3 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN3
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith only [hNR3]
  have hlogN1 : (1:ℝ) ≤ Real.log (N:ℝ) := by
    have hmono : Real.log (3:ℝ) ≤ Real.log (N:ℝ) :=
      Real.log_le_log (by norm_num) hNR3
    linarith only [hmono, homogBelow_one_lt_log_three]
  have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := le_trans zero_le_one hlogN1
  have hlogNsqge : Real.log (N:ℝ) ≤ (Real.log (N:ℝ)) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlogN1 hlogN0
    have hsq : (Real.log (N:ℝ)) ^ 2 = Real.log (N:ℝ) * Real.log (N:ℝ) := sq (Real.log (N:ℝ))
    rw [hsq]
    linarith only [h]
  have hCprimeBound : (p + Real.log C61 + 1) / (kappa * Real.log 3) ≤ Cprime :=
    le_trans (le_max_right _ _) hCprime
  have hkl3pos : (0:ℝ) < kappa * Real.log 3 := mul_pos hkappa hlog3pos
  have hCprimeIneq : p + Real.log C61 + 1 ≤ kappa * Real.log 3 * Cprime := by
    rw [div_le_iff₀ hkl3pos] at hCprimeBound
    linarith only [hCprimeBound]
  set m0 : ℕ := ⌈Cprime * (Real.log (N:ℝ)) ^ 2⌉₊ with hm0def
  have hm0ge : Cprime * (Real.log (N:ℝ)) ^ 2 ≤ (m0 : ℝ) := Nat.le_ceil _
  -- Step 1: `kappa*log3*Cprime*logN² ≤ kappa*m0*log3`.
  have hstep1 : kappa * Real.log 3 * (Cprime * (Real.log (N:ℝ)) ^ 2) ≤
      kappa * (m0 : ℝ) * Real.log 3 := by
    have h := mul_le_mul_of_nonneg_left hm0ge hkl3pos.le
    linarith only [h]
  -- Step 2: `kappa*log3*Cprime*logN ≤ kappa*log3*Cprime*logN²`.
  have hCprimeNonneg : (0:ℝ) ≤ kappa * Real.log 3 * Cprime :=
    mul_nonneg hkl3pos.le hCpos.le
  have hstep2 : kappa * Real.log 3 * Cprime * Real.log (N:ℝ) ≤
      kappa * Real.log 3 * Cprime * (Real.log (N:ℝ)) ^ 2 :=
    mul_le_mul_of_nonneg_left hlogNsqge hCprimeNonneg
  -- Step 3: `logN*(p+logC61+1) ≤ logN*(kappa*log3*Cprime)`.
  have hstep3 : Real.log (N:ℝ) * (p + Real.log C61 + 1) ≤
      Real.log (N:ℝ) * (kappa * Real.log 3 * Cprime) :=
    mul_le_mul_of_nonneg_left hCprimeIneq hlogN0
  -- Step 4: `logC61 ≤ logN*(logC61+1)`, using `logN ≥ 1` and `logC61 ≥ 0`.
  have hlogC61nonneg : (0:ℝ) ≤ Real.log C61 := Real.log_nonneg hC61
  have hstep4 : Real.log C61 ≤ Real.log (N:ℝ) * (Real.log C61 + 1) := by
    nlinarith only [hlogN1, hlogC61nonneg]
  -- Assemble: `p*logN + logC61 ≤ kappa*m0*log3`.
  have hassemble : p * Real.log (N:ℝ) + Real.log C61 ≤ kappa * (m0 : ℝ) * Real.log 3 := by
    nlinarith only [hstep1, hstep2, hstep3, hstep4]
  -- Convert to the `rpow`/`exp` inequality.
  have hC61pos : (0:ℝ) < C61 := lt_of_lt_of_le one_pos hC61
  have hlhs_eq : C61 * (3:ℝ) ^ (-(kappa * ((m0 : ℕ) : ℝ))) =
      Real.exp (Real.log C61 + Real.log 3 * -(kappa * (m0 : ℝ))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), Real.exp_add, Real.exp_log hC61pos]
  have hrhs_eq : (N:ℝ) ^ (-(p)) = Real.exp (Real.log (N:ℝ) * -p) := by
    rw [Real.rpow_def_of_pos hNpos]
  rw [hlhs_eq, hrhs_eq]
  apply Real.exp_le_exp.mpr
  nlinarith only [hassemble]

end SuperdiffusionCLT.Section4.HomogBelow
