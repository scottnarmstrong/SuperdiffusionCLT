/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.LNaught.Monotone

/-!
**`lNaught` grows at least
linearly in its own first (threshold) argument `C`, uniformly over every
other valid parameter.** This is the key fact that resolves an apparent
circularity in the Step 3 scale-positivity argument: naively, if
`m₀ := ⌈C·log²L⌉₊` uses the *same* `C` as the `lNaught C ... ≤ L` threshold,
one might think discharging `C·log²L ≤ M·L^α·log³L` (via
`ThetaLmGrowthRate.lean`'s `homogBelow_logSq_le_rpow_logCube`, which needs
`L ≥ exp(C₁)` for the relevant `C₁`) requires `L` to grow *exponentially* in
`C` — but `lNaught(C,...)` only grows *polynomially* in `C` (literally:
`lNaught(C,...) = (C·const)^{1/(1-α)}`), so `L ≥ lNaught(C,...)` alone can
never force `L ≥ exp(K·C)` for `C` unbounded.

**The resolution**: the `C₁` fed to
`homogBelow_logSq_le_rpow_logCube` must be a constant that is chosen
*before*, and independently of, the theorem's own final combined constant
`C_final` — e.g. `M0ThresholdB.lean`'s own minimal threshold `C₀` (which
depends only on `C₆₁, Cmix, Cellip, d`), used as `m₀`'s coefficient
*directly* (not `C_final`). Since `C₁ := C₀` is then fixed *first*, one only
needs `C_final` (chosen *after*, as a `max` of several such fixed
thresholds, exactly the standing idiom) large enough that
`lNaught(C_final,...) ≥ exp(K·C₀)` — a **non-circular** threshold choice,
made possible by *this* file's fact that `lNaught(C,...) → ∞` as `C → ∞`,
uniformly over the other (adversarial) parameters, since the growth is at
least linear: `lNaught(C,M,α,c⋆,ν,K) ≥ (log 2)^12/4 · C` for `C` large
enough (`C ≥ max(1, 4/(log 2)^12)`), the worst case over `M,α,c⋆,ν,K` being
`M=1` (smallest, since `hM:1≤M` is the only floor and `lNaught` is
increasing in `M`), `α=0` (smallest allowed, minimizing the outer exponent
`1/(1-α)=1` and the `(1-α)^{-12}` factor), `c⋆=2` (largest allowed,
minimizing `c⋆^{-3}`), `ν=1` (largest allowed, minimizing `ν^{-4}`), `K=0`
(smallest allowed). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open SuperdiffusionCLT.Section4.LNaught

/-- **`lNaught` grows at least linearly in its own first argument `C`**,
once `C` is past an absolute (parameter-independent) threshold. -/
theorem homogBelow_lNaught_ge_linear :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ C : ℝ, C0 ≤ C →
      ∀ M : ℝ, 1 ≤ M → ∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      ∀ cStar : ℝ, 0 < cStar → cStar ≤ 2 →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 → ∀ K : ℝ, 0 ≤ K →
      (Real.log 2) ^ (12 : ℝ) / 4 * C ≤
        SuperdiffusionCLT.Frozen.Section4.lNaught C M alpha cStar nu K := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2pow_pos : (0 : ℝ) < (Real.log 2) ^ (12 : ℝ) := Real.rpow_pos_of_pos hlog2pos _
  refine ⟨max 1 (4 / (Real.log 2) ^ (12 : ℝ)), le_max_left _ _, ?_⟩
  intro C hC M hM alpha halpha0 halpha1 cStar hcStar hcStar2 nu hnu hnu1 K hK
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_max_left _ _) hC
  have hCbig : 4 / (Real.log 2) ^ (12 : ℝ) ≤ C := le_trans (le_max_right _ _) hC
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  -- BASE := lNaughtInner C M alpha cStar nu K ≥ (log 2)^12/4 * C.
  have hMK2 : (2 : ℝ) ≤ M + 1 + K := by linarith only [hM, hK]
  have hcStarpow : (2 : ℝ) ^ (-(3 : ℝ)) ≤ cStar ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hcStar hcStar2 (by norm_num)
  have hcStarpow_eq : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
    rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hcStarpow_ge : (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := by rw [← hcStarpow_eq]; exact hcStarpow
  have h1malpha_le1 : (1 - alpha) ^ (12 : ℝ) ≤ 1 := by
    have h0le : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha1]
    have h1 : 1 - alpha ≤ 1 := by linarith only [halpha0]
    calc (1 - alpha) ^ (12 : ℝ) ≤ (1 : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow h0le h1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hnu4_le1 : nu ^ (4 : ℝ) ≤ 1 := by
    calc nu ^ (4 : ℝ) ≤ (1 : ℝ) ^ (4 : ℝ) := Real.rpow_le_rpow hnu.le hnu1 (by norm_num)
      _ = 1 := Real.one_rpow _
  have hdenom_pos : (0 : ℝ) < (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) := denom_pos hnu halpha1
  have hdenom_le1 : (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 := by
    have h1ma_nonneg : (0 : ℝ) ≤ (1 - alpha) ^ (12 : ℝ) :=
      Real.rpow_nonneg (by linarith only [halpha1]) _
    have hnu4_nonneg : (0 : ℝ) ≤ nu ^ (4 : ℝ) := Real.rpow_nonneg hnu.le _
    calc (1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ) ≤ 1 * 1 :=
          mul_le_mul h1malpha_le1 hnu4_le1 hnu4_nonneg (by norm_num)
      _ = 1 := mul_one 1
  have hnum_nonneg : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have hcpow_nonneg : (0 : ℝ) ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg hcStar.le _
    have hCMK : (0 : ℝ) ≤ C * (M + 1 + K) :=
      mul_nonneg (by linarith only [hC1]) (by linarith only [hMK2])
    exact mul_nonneg hCMK hcpow_nonneg
  have hfrac_ge : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := by
    rw [le_div_iff₀ hdenom_pos]
    calc C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) * ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) ≤
          C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hdenom_le1 hnum_nonneg
      _ = C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := mul_one _
  have hnumbound : 2 * ((1 : ℝ) / 8) * C ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have step : C * 2 * (1 / 8) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
      have hcnn : (0 : ℝ) ≤ C := hC1.trans' zero_le_one
      calc C * 2 * (1 / 8) ≤ C * (M + 1 + K) * (1 / 8) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hMK2 hcnn) (by norm_num)
        _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) :=
            mul_le_mul_of_nonneg_left hcStarpow_ge
              (mul_nonneg hcnn (by linarith only [hMK2]))
    linarith only [step]
  have hlogargge2 := log_arg_ge_two (by linarith only [hM] : (0:ℝ) ≤ M) hK hcStar hnu halpha1
  have hlogge : Real.log 2 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) :=
    Real.log_le_log (by norm_num) hlogargge2
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := hlog2pos.le
  have hlogpow_ge : (Real.log 2) ^ (12 : ℝ) ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
    Real.rpow_le_rpow hlog2nn hlogge (by norm_num)
  have hlogpow_nn : (0 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) := hlog2pow_pos.le
  have hfracnn : (0 : ℝ) ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
      ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := div_nonneg hnum_nonneg hdenom_pos.le
  have hbase_ge : (Real.log 2) ^ (12 : ℝ) / 4 * C ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have hstep1 : (Real.log 2) ^ (12 : ℝ) / 4 * C =
        (2 * (1 / 8) * C) * (Real.log 2) ^ (12 : ℝ) := by ring
    rw [hstep1]
    calc (2 * (1 / 8) * C) * (Real.log 2) ^ (12 : ℝ) ≤
          (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
              ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) * (Real.log 2) ^ (12 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hlogpow_nn
            calc 2 * (1 / 8) * C = 2 * ((1:ℝ)/8) * C := by ring
              _ ≤ C * (M + 1 + K) * cStar ^ (-(3:ℝ)) := by linarith only [hnumbound]
              _ ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
                  ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) := hfrac_ge
      _ ≤ (C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) /
              ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ))) *
            Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) :=
          mul_le_mul_of_nonneg_left hlogpow_ge hfracnn
  have hbase_ge1 : (1 : ℝ) ≤
      C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) := by
    have h4C : (4 : ℝ) ≤ (Real.log 2) ^ (12 : ℝ) * C := by
      rw [div_le_iff₀ hlog2pow_pos] at hCbig
      linarith only [hCbig]
    have hstep : (1:ℝ) ≤ (Real.log 2)^(12:ℝ)/4 * C := by nlinarith only [h4C]
    linarith only [hstep, hbase_ge]
  set BASE : ℝ := C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 - alpha) ^ (12 : ℝ) * nu ^ (4 : ℝ)) *
        Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 - alpha))) ^ (12 : ℝ) with hBASEdef
  have hexp_ge1 : (1 : ℝ) ≤ (1 : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ (one_minus_alpha_pos halpha1)]
    linarith only [halpha0]
  have hfinal : BASE ≤ BASE ^ ((1 : ℝ) / (1 - alpha)) :=
    Real.self_le_rpow_of_one_le hbase_ge1 hexp_ge1
  linarith only [hbase_ge, hfinal]

end SuperdiffusionCLT.Section4.HomogBelow
