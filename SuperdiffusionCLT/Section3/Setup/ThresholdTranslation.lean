/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section3.Setup.QuenchedLowerBound
public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly

/-!
# The threshold translation of the Section 3 root

The root statement `Frozen.Section3.sigmaBarStar_lower_bound` receives from its
caller a single threshold hypothesis, the display `e.L.vs.nu` of the paper, read
with the correction of the nondegeneracy logarithm (see `ERRATA.md`):

```
C * c⋆⁻³ * (log³(3 + ν⁻¹ + c⋆⁻¹) log log(3 + ν⁻¹ + c⋆⁻¹)
           + (1 + K) * log(3 + ν⁻¹ + K)) ≤ m,   m ≤ L ≤ 2m .
```

The root composition consumes eleven threshold conditions in
place of it: the constant choices `c₀`, `Cenv`, `Knd`, `CL`, `Ceta`; the
largeness `8056 ≤ K log 3` of the J5 constant; the shapes of `e.L.vs.nu` at
`L` (`11 ≤ log(ν⁻¹L)`, `log Cenv ≤ log(ν⁻¹L)`, the window shape, the depth
shape `CM L^{-500} ≤ c⋆/8`, the shape at the optimal window, the tail shape
`4CB log²(ν⁻¹L) ≤ L`, `4Ceta ≤ ν⁻¹L`); and `hde1` (`δ + η_L ≤ 1`).  This file
carries the first translations.

## What is proved here

* The two **term bridges** of the threshold (`frozenThreshold_term_bounds`):
  each summand of `eLvsNuTerm`, scaled by `C`, is below `L · c⋆³`.  Every
  shape whose right side is `O(c⋆³ L)` reduces to one of them.
* The first shape that follows from the threshold under `c⋆ ≤ 1`: `1 ≤ m ≤ L`
  (`frozenThreshold_one_le_L`).

## What is *not* here

The remaining shapes of `e.L.vs.nu` — `log Cenv ≤ log(ν⁻¹L)`, the window shape
`20(K log²(ν⁻¹L)+1)(C log(Cν⁻¹L)) ≤ δL`, the shape at the optimal window
`4CM(1+Knd+K log(ν⁻¹L)) log(ν⁻¹L) ≤ optimalWindowConst·c⋆³·L`, the tail shape
`4CB log²(ν⁻¹L) ≤ L` and the depth shape `CM·L^{-500} ≤ c⋆/8` — need the
quantitative comparison of `log(ν⁻¹L)` with the threshold terms of
`eLvsNuTerm`, that is, the content of the corrected threshold beyond the two term
bridges above.  Two structural facts are recorded here:

* with `c⋆ ≤ 1` the threshold term `log(3+ν⁻¹+c⋆⁻¹)` is at least `log 4 > 1`,
  so the cube term dominates: this is the route to the printed shape `11 ≤ log(ν⁻¹L)`;
* for `c⋆ ≥ 1` the threshold tends to zero as `c⋆` grows, so no single
  constant `C` makes `11 ≤ log(ν⁻¹L)` hold for all `c⋆ > 0` (take `ν = 1`,
  `K = 1`, `L = m = 3` and `c⋆` large).  The composition must therefore supply
  the `c⋆ ≤ 1` reading of the shape block or split the range of `c⋆`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

noncomputable section

/-! ## The arithmetic of the printed constants `log 3`, `log 4` -/

/-- `1 < log 3`: the positivity with room to spare of the iterated logarithm
of `e.L.vs.nu`. -/
private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlt : Real.log (Real.exp 1) < Real.log 3 :=
    Real.log_lt_log (Real.exp_pos 1) hexp
  rw [Real.log_exp] at hlt
  exact hlt

/-! ## The threshold term of `e.L.vs.nu` -/

/-- The bracket of the threshold `e.L.vs.nu` of the paper, read
with the correction of the nondegeneracy logarithm: exactly the
two summands that the hypothesis of the root carries. -/
def eLvsNuTerm (nu cStar K : ℝ) : ℝ :=
  Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) +
    (1 + K) * Real.log (3 + nu⁻¹ + K)

/-- The first summand of `eLvsNuTerm` is nonnegative: `log(3+ν⁻¹+c⋆⁻¹) ≥ 1`
makes the iterated logarithm nonnegative. -/
theorem eLvsNuTerm_term_one_nonneg {nu cStar : ℝ} (hnu : 0 < nu)
    (hcStar : 0 < cStar) :
    (0 : ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
        Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) := by
  have h1 : (0 : ℝ) ≤ nu⁻¹ := inv_nonneg.2 hnu.le
  have h2 : (0 : ℝ) ≤ cStar⁻¹ := inv_nonneg.2 hcStar.le
  have hX : (3 : ℝ) ≤ 3 + nu⁻¹ + cStar⁻¹ := by linarith only [h1, h2]
  have hlogX : (1 : ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) :=
    le_trans one_lt_log_three.le (Real.log_le_log (by norm_num) hX)
  have hpos0 : (0 : ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) := by
    linarith only [hlogX]
  exact mul_nonneg (pow_nonneg hpos0 3) (Real.log_nonneg hlogX)

/-- The second summand of `eLvsNuTerm` is positive. -/
theorem eLvsNuTerm_term_two_pos {nu K : ℝ} (hnu : 0 < nu) (hK : 0 ≤ K) :
    (0 : ℝ) < (1 + K) * Real.log (3 + nu⁻¹ + K) := by
  have h1 : (0 : ℝ) ≤ nu⁻¹ := inv_nonneg.2 hnu.le
  have hX : (1 : ℝ) < 3 + nu⁻¹ + K := by linarith only [h1, hK]
  exact mul_pos (by linarith only [hK]) (Real.log_pos hX)

/-- `eLvsNuTerm` is positive. -/
theorem eLvsNuTerm_pos {nu cStar K : ℝ} (hnu : 0 < nu) (hcStar : 0 < cStar)
    (hK : 0 ≤ K) : (0 : ℝ) < eLvsNuTerm nu cStar K := by
  rw [eLvsNuTerm]
  have h1 : (0 : ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) :=
    eLvsNuTerm_term_one_nonneg hnu hcStar
  have h2 : (0 : ℝ) < (1 + K) * Real.log (3 + nu⁻¹ + K) :=
    eLvsNuTerm_term_two_pos hnu hK
  linarith only [h1, h2]

/-! ## The term bridges of the threshold -/

/-- **The two term bridges of the threshold** of
`Frozen.Section3.sigmaBarStar_lower_bound`: each summand of
`eLvsNuTerm`, scaled by the constant `C` of the root, is below `L · c⋆³`.
Division-free form of `summand ≤ m c⋆³ / C` under `C · c⋆⁻³ · eLvsNuTerm ≤ m`
and `m ≤ L`. -/
theorem frozenThreshold_term_bounds {C nu cStar K : ℝ} {m L : ℕ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hK : 0 ≤ K) (hC : (0 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ))
    (hmL : m ≤ L) :
    (1 + K) * Real.log (3 + nu⁻¹ + K) * C ≤ (L : ℝ) * cStar ^ (3 : ℕ) ∧
      Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) * C ≤
        (L : ℝ) * cStar ^ (3 : ℕ) := by
  have hcpow3 : cStar ^ ((3 : ℝ)) = cStar ^ (3 : ℕ) := Real.rpow_natCast cStar 3
  have hadd : cStar ^ (-(3 : ℝ)) * cStar ^ ((3 : ℝ)) = (1 : ℝ) := by
    rw [← Real.rpow_add (by linarith only [hcStar]),
      show ((-(3 : ℝ)) + (3 : ℝ)) = 0 by norm_num, Real.rpow_zero]
  have hpos : (0 : ℝ) ≤ cStar ^ ((3 : ℝ)) := Real.rpow_nonneg hcStar.le _
  have hge := mul_le_mul_of_nonneg_right hft hpos
  have hcancel : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K *
      cStar ^ ((3 : ℝ)) = eLvsNuTerm nu cStar K * C := by
    calc C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K * cStar ^ ((3 : ℝ))
        = (C * eLvsNuTerm nu cStar K) * (cStar ^ (-(3 : ℝ)) * cStar ^ ((3 : ℝ))) := by
          ring
      _ = C * eLvsNuTerm nu cStar K := by rw [hadd, mul_one]
      _ = eLvsNuTerm nu cStar K * C := by ring
  have hkey : eLvsNuTerm nu cStar K * C ≤ (m : ℝ) * cStar ^ ((3 : ℝ)) := by
    rw [hcancel] at hge
    exact hge
  have hstep : (m : ℝ) * cStar ^ ((3 : ℝ)) ≤ (L : ℝ) * cStar ^ ((3 : ℝ)) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hmL) hpos
  have hkeyR : eLvsNuTerm nu cStar K * C ≤ (L : ℝ) * cStar ^ ((3 : ℝ)) := by
    linarith only [hkey, hstep]
  have hkeyL : eLvsNuTerm nu cStar K * C ≤ (L : ℝ) * cStar ^ (3 : ℕ) := by
    rw [← hcpow3]
    exact hkeyR
  have hsplit : eLvsNuTerm nu cStar K * C =
      (Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
          Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) * C) +
        ((1 + K) * Real.log (3 + nu⁻¹ + K) * C) := by
    rw [eLvsNuTerm]
    ring
  have hT1 : (0 : ℝ) ≤ Real.log (3 + nu⁻¹ + cStar⁻¹) ^ 3 *
      Real.log (Real.log (3 + nu⁻¹ + cStar⁻¹)) * C :=
    mul_nonneg (eLvsNuTerm_term_one_nonneg hnu hcStar) hC
  have hT2 : (0 : ℝ) ≤ (1 + K) * Real.log (3 + nu⁻¹ + K) * C :=
    mul_nonneg (eLvsNuTerm_term_two_pos hnu hK).le hC
  constructor
  · linarith only [hkeyL, hsplit, hT1]
  · linarith only [hkeyL, hsplit, hT2]

/-! ## The first shapes of `e.L.vs.nu` -/

/-- **The threshold forces `m` positive**: `1 ≤ m ≤ L`.  With `c⋆ ≤ 1` the
threshold is at least `C · 2 log 3`, independently of `ν` and `K`; this
is the first shape of `e.L.vs.nu`. -/
theorem frozenThreshold_one_le_L {C nu cStar K : ℝ} {m L : ℕ}
    (hnu : 0 < nu) (hcStar : 0 < cStar) (hK : 0 ≤ K) (hC : (1 : ℝ) ≤ C)
    (hft : C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ))
    (hmL : m ≤ L) :
    1 ≤ m ∧ 1 ≤ L := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hscale : (0 : ℝ) < cStar ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hcStar.le]
    exact inv_pos.2 (Real.rpow_pos_of_pos hcStar (3 : ℝ))
  have hterm := eLvsNuTerm_pos hnu hcStar hK
  have hprod : (0 : ℝ) < C * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K :=
    mul_pos (mul_pos hC0 hscale) hterm
  have hm : (0 : ℝ) < (m : ℝ) := by
    have hnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith only [hnn, hft, hprod]
  have hm1 : (1 : ℕ) ≤ m := by
    have hm0 : (0 : ℕ) < m := Nat.cast_pos.1 hm
    omega
  exact ⟨hm1, by omega⟩

end

end SuperdiffusionCLT.Section3.Setup