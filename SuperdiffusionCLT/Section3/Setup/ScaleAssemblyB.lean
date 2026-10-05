/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.ScaleAssembly
public import SuperdiffusionCLT.Section3.Terms.MasterInequality

/-!
# The root's own steps: from the scale selection to `e.sstar.lower.bound`

The file `ScaleAssembly` chose the window, produced the `ScaleSelection` and
discharged the three scale conditions that `Terms.master_inequality` consumes.
This file discharges the ten hypotheses of `Terms.sstar_lower_bound_of_terms`,
instantiates the homogenization statement, removes the pigeonhole scale and
composes everything.

## What is proved here

* `smallness_relative` — `C(δ + L^{-1000})^{1/2}` below `¼c⋆`, from
  `δ = c₀c⋆²` with `C√c₀ ≤ 1/8`, which is the print's "the choice of
  `c₀` ensures the relative smallness condition `Cδ^{1/2} ≤ ¼c⋆`".
* `smallness_absolute` — the same factor below `2C + 1`, from `δ ≤ 1` and
  `L ≥ 1` alone; this is the factor the print keeps on `σ̄_ℓ(cu_n)`
  and absorbs into its unspecified constant `c(d)`, and it uses no upper bound
  on `c⋆`.
* `lowerOrder_absorption` — `C(1 + K_nd + K log(ν⁻¹L)) ≤ ¼c⋆h`, from
  `e.h.optimized.size` and the threshold `e.L.vs.nu`.
* `logEnvelopeConst`, `q_envelope` — `(ℓ − n + log²(ν⁻¹ℓ))⁴ ≤ Cq log⁸(ν⁻¹L)`.
* `log_pigeon_range` — the comparability of `log(ν⁻¹L)` with `log(ν⁻¹m)` over
  the pigeonhole range `m ∈ [L/4, L/2]`.
* `exists_bell_bound` — the statement
  `Frozen.Section3.sigmaBar_le_sigmaBarStar_homogenization` at `(n, ℓ, L)`,
  with `σ̄_{ℓ,*}(cu_n)` written as `(sigmaBarStarInvSeq nu ℓ P n)⁻¹`.
* `sigmaBarStarScalar_originCube_mono` and `lower_bound_transfer` — the removal of the
  pigeonhole scale.
* `master_inequality_of_selection` — `Terms.master_inequality` with `hha`,
  `haK`, `hEta`, `hCrude` and `hScaleCond` discharged from the scale
  selection, so that only the five term bounds and the master identity remain.

## What is not proved here

The composition of these steps into the root theorem carries, as explicit hypotheses,
exactly the bridges not proved in this file:

* the master inequality at the selected scales, which
  `master_inequality_of_selection` reduces to the five term bounds
  `l.LHS.term1`, `e.RHS.term1`-`e.RHS.term4` and the master identity
  `e.ellsep.testing`;
* the two balanced localization comparisons, whose source is
  `Frozen.Section2.cutoff_localization` (the printed `e.localization.s.star`),
  not the averaged gauged comparison `localization_average` of
  `Frozen/Section2/LocalizationAverage.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Terms
open scoped ENNReal

noncomputable section

/-! ## The smallness of `(δ + L^{-1000})^{1/2}` -/

/-- Subadditivity of the square root, used once to split
`(δ + L^{-1000})^{1/2}` into the `δ`-part, which the choice of `c₀` controls,
and the `L`-part, which the threshold `e.L.vs.nu` controls. -/
private theorem sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsy : (0 : ℝ) ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hx' : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt hx
  have hy' : Real.sqrt y ^ (2 : ℕ) = y := Real.sq_sqrt hy
  have hcross : (0 : ℝ) ≤ 2 * (Real.sqrt x * Real.sqrt y) := by positivity
  have hkey : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ (2 : ℕ) := by
    have hexp : (Real.sqrt x + Real.sqrt y) ^ (2 : ℕ) =
        Real.sqrt x ^ (2 : ℕ) + 2 * (Real.sqrt x * Real.sqrt y) +
          Real.sqrt y ^ (2 : ℕ) := by ring
    rw [hexp, hx', hy']
    linarith only [hcross]
  have hfin := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_sq (by linarith only [hsx, hsy])] at hfin

/-- `(δ + L^{-1000})^{1/2} = √δ + L^{-500}` up to the subadditivity of the
square root, with `√δ = √c₀ c⋆` for the print's `δ = c₀c⋆²`. -/
theorem masterSmallness_le {CM c0 cStar : ℝ} {L : ℕ}
    (hCM : 0 ≤ CM) (hc0 : 0 ≤ c0) (hcStar : 0 ≤ cStar) :
    CM * (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) ≤
      CM * (Real.sqrt c0 * cStar) + CM * (L : ℝ) ^ (-(500 : ℝ)) := by
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ smallnessParameter c0 cStar := smallnessParameter_nonneg hc0
  have he : (0 : ℝ) ≤ (L : ℝ) ^ (-(1000 : ℝ)) := Real.rpow_nonneg hLnn _
  have hsum : (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) =
      Real.sqrt (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) :=
    (Real.sqrt_eq_rpow _).symm
  have hsplit := sqrt_add_le_add_sqrt hd he
  have hdelta : Real.sqrt (smallnessParameter c0 cStar) = Real.sqrt c0 * cStar :=
    sqrt_smallnessParameter hc0 hcStar
  have hLhalf : Real.sqrt ((L : ℝ) ^ (-(1000 : ℝ))) = (L : ℝ) ^ (-(500 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLnn]
    norm_num
  rw [hsum]
  have hstep : Real.sqrt (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) ≤
      Real.sqrt c0 * cStar + (L : ℝ) ^ (-(500 : ℝ)) := by
    rw [← hdelta, ← hLhalf]
    exact hsplit
  have := mul_le_mul_of_nonneg_left hstep hCM
  linarith only [this]

/-- **The relative smallness condition `C(δ + L^{-1000})^{1/2} ≤ ¼c⋆`**
(`hSmallC` of `Terms.sstar_lower_bound_of_terms`).  The
first hypothesis is the print's choice of `c₀`, the second is the
threshold `e.L.vs.nu` taken large. -/
theorem smallness_relative {CM c0 cStar : ℝ} {L : ℕ}
    (hCM : 0 ≤ CM) (hc0 : 0 ≤ c0) (hcStar : 0 ≤ cStar)
    (hc0small : CM * Real.sqrt c0 ≤ 1 / 8)
    (hthr : CM * (L : ℝ) ^ (-(500 : ℝ)) ≤ cStar / 8) :
    CM * (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) ≤
      cStar / 4 := by
  have hmain := masterSmallness_le (CM := CM) (c0 := c0) (cStar := cStar) (L := L)
    hCM hc0 hcStar
  have hrw : CM * (Real.sqrt c0 * cStar) = CM * Real.sqrt c0 * cStar := by ring
  have hfirst : CM * Real.sqrt c0 * cStar ≤ 1 / 8 * cStar :=
    mul_le_mul_of_nonneg_right hc0small hcStar
  linarith only [hmain, hrw, hfirst, hthr]

/-- **The absolute bound `C(δ + L^{-1000})^{1/2} ≤ 2C + 1`** on the factor that
the print keeps on `σ̄_ℓ(cu_n)` in its display and absorbs into its
unspecified constant `c(d)` (`hFactor` of `Terms.sstar_lower_bound_of_terms`).
Only `δ ≤ 1` — the scale selection's own bound on the smallness parameter — and
`L ≥ 1` are used: no absolute smallness of `δ`
independent of `c⋆` is available, and the paper's `c⋆`, the nondegeneracy
constant of `a.j.nondeg` (`ShellLawJ5`), carries no upper bound. -/
theorem smallness_absolute {CM c0 cStar : ℝ} {L : ℕ}
    (hCM : 0 ≤ CM) (hc0 : 0 ≤ c0)
    (hdelta1 : smallnessParameter c0 cStar ≤ 1) (hL : 1 ≤ L) :
    CM * (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) ≤
      2 * CM + 1 := by
  have hd : (0 : ℝ) ≤ smallnessParameter c0 cStar := smallnessParameter_nonneg hc0
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLe : (L : ℝ) ^ (-(1000 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hsum : (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) =
      Real.sqrt (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) :=
    (Real.sqrt_eq_rpow _).symm
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hDE : (smallnessParameter c0 cStar + (L : ℝ) ^ (-(1000 : ℝ))) ^
      ((1 : ℝ) / 2) ≤ 2 := by
    rw [hsum, ← hsqrt4]
    exact Real.sqrt_le_sqrt (by linarith only [hdelta1, hLe])
  have hmul := mul_le_mul_of_nonneg_left hDE hCM
  linarith only [hmul, hd]

/-! ## The absorption of the lower-order term -/

/-- **`C(1 + K_nd + K log(ν⁻¹L)) ≤ ¼c⋆h`**, the second condition on the window,
which is used to absorb the lower-order term (`hLowerAbs` of
`Terms.sstar_lower_bound_of_terms`).  It follows from `e.h.optimized.size` and
the threshold `e.L.vs.nu`, in the form `hThreshAbs` — the printed threshold's
`c⋆^{-3}` and its `(1 + \nondegconst) log(3 + ν^{-1} + \nondegconst)` term
are exactly what this hypothesis records. -/
theorem lowerOrder_absorption {CM cStar Knd K c1 nu : ℝ} {L h : ℕ}
    (hcStar : 0 < cStar) (hlogpos : 0 < Real.log (nu⁻¹ * (L : ℝ)))
    (hHsize : c1 * cStar ^ (2 : ℕ) * (L : ℝ) ≤ (h : ℝ) * Real.log (nu⁻¹ * (L : ℝ)))
    (hThreshAbs : 4 * CM * (1 + Knd + K * Real.log (nu⁻¹ * (L : ℝ))) *
        Real.log (nu⁻¹ * (L : ℝ)) ≤ c1 * cStar ^ (3 : ℕ) * (L : ℝ)) :
    CM * (1 + Knd + K * Real.log (nu⁻¹ * (L : ℝ))) ≤ cStar * (h : ℝ) / 4 := by
  have hstep := mul_le_mul_of_nonneg_left hHsize (by linarith only [hcStar] :
    (0 : ℝ) ≤ cStar / 4)
  have e1 : cStar / 4 * (c1 * cStar ^ (2 : ℕ) * (L : ℝ)) =
      c1 * cStar ^ (3 : ℕ) * (L : ℝ) / 4 := by ring
  have e2 : cStar / 4 * ((h : ℝ) * Real.log (nu⁻¹ * (L : ℝ))) =
      cStar * (h : ℝ) / 4 * Real.log (nu⁻¹ * (L : ℝ)) := by ring
  have hmul : CM * (1 + Knd + K * Real.log (nu⁻¹ * (L : ℝ))) *
      Real.log (nu⁻¹ * (L : ℝ)) ≤
      cStar * (h : ℝ) / 4 * Real.log (nu⁻¹ * (L : ℝ)) := by
    linarith only [hstep, e1, e2, hThreshAbs]
  exact le_of_mul_le_mul_right hmul hlogpos

/-! ## The logarithmic envelope -/

/-- The constant `Cq` of the logarithmic envelope,
`(ℓ − n + log²(ν⁻¹ℓ))⁴ ≤ Cq log⁸(ν⁻¹L)`, produced by `a = ⌈K log(ν⁻¹L)⌉`. -/
def logEnvelopeConst (K : ℝ) : ℝ := (K + 2) ^ (4 : ℕ)

theorem logEnvelopeConst_pos {K : ℝ} (hK : 0 ≤ K) : 0 < logEnvelopeConst K := by
  rw [logEnvelopeConst]
  positivity

/-- **The logarithmic envelope** (`hQ` of
`Terms.sstar_lower_bound_of_terms`): with `ℓ − n = a ≤ K log(ν⁻¹L) + 1` and
`log(ν⁻¹ℓ) ≤ log(ν⁻¹L)`, the fourth power of `ℓ − n + log²(ν⁻¹ℓ)` is at most
`(K+2)⁴ log⁸(ν⁻¹L)`. -/
theorem q_envelope {K nu : ℝ} {S : ScaleSelection}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hK : (1 : ℝ) ≤ K)
    (hlog1 : (1 : ℝ) ≤ Real.log (nu⁻¹ * (S.L : ℝ)))
    (hell1 : 1 ≤ S.ell) (hellL : S.ell ≤ S.L)
    (haK : (S.a : ℝ) ≤ K * Real.log (nu⁻¹ * (S.L : ℝ)) + 1) :
    (((S.ell - S.n : ℕ) : ℝ) + Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ)) ^ (4 : ℕ) ≤
      logEnvelopeConst K * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (8 : ℕ) := by
  have hinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hell1R : (1 : ℝ) ≤ (S.ell : ℝ) := by exact_mod_cast hell1
  have hellLR : (S.ell : ℝ) ≤ (S.L : ℝ) := by exact_mod_cast hellL
  have hellpos : (0 : ℝ) < nu⁻¹ * (S.ell : ℝ) := by
    have : (0 : ℝ) < nu⁻¹ := by linarith only [hinv1]
    exact mul_pos this (by linarith only [hell1R])
  have hone : (1 : ℝ) ≤ nu⁻¹ * (S.ell : ℝ) := by
    have := mul_le_mul hinv1 hell1R zero_le_one (by linarith only [hinv1])
    linarith only [this]
  have hlogell0 : (0 : ℝ) ≤ Real.log (nu⁻¹ * (S.ell : ℝ)) := Real.log_nonneg hone
  have hlogellL : Real.log (nu⁻¹ * (S.ell : ℝ)) ≤ Real.log (nu⁻¹ * (S.L : ℝ)) := by
    refine Real.log_le_log hellpos ?_
    exact mul_le_mul_of_nonneg_left hellLR (by linarith only [hinv1])
  have hsq : Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ) ≤
      Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hlogell0 hlogellL 2
  have hLamsq : Real.log (nu⁻¹ * (S.L : ℝ)) ≤ Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) := by
    have := mul_le_mul_of_nonneg_left hlog1 (by linarith only [hlog1] :
      (0 : ℝ) ≤ Real.log (nu⁻¹ * (S.L : ℝ)))
    calc Real.log (nu⁻¹ * (S.L : ℝ)) = Real.log (nu⁻¹ * (S.L : ℝ)) * 1 := (mul_one _).symm
      _ ≤ Real.log (nu⁻¹ * (S.L : ℝ)) * Real.log (nu⁻¹ * (S.L : ℝ)) := by
          simpa only [mul_one] using this
      _ = Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) := by ring
  have hone2 : (1 : ℝ) ≤ Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) := by
    linarith only [hlog1, hLamsq]
  have haR : ((S.ell - S.n : ℕ) : ℝ) = (S.a : ℝ) := by rw [S.ell_sub_n]
  have hKnn : (0 : ℝ) ≤ K := by linarith only [hK]
  have hbase : ((S.ell - S.n : ℕ) : ℝ) + Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ) ≤
      (K + 2) * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) := by
    have hKmono : K * Real.log (nu⁻¹ * (S.L : ℝ)) ≤
        K * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hLamsq hKnn
    have hexp : (K + 2) * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) =
        K * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) +
          Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) +
          Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ) := by ring
    rw [haR, hexp]
    linarith only [haK, hKmono, hsq, hone2]
  have hbnn : (0 : ℝ) ≤ ((S.ell - S.n : ℕ) : ℝ) +
      Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ) := by positivity
  have hpow := pow_le_pow_left₀ hbnn hbase 4
  have hval : ((K + 2) * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (2 : ℕ)) ^ (4 : ℕ) =
      logEnvelopeConst K * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (8 : ℕ) := by
    rw [logEnvelopeConst]
    ring
  linarith only [hpow, hval]

/-! ## The comparability of the logarithms over the pigeonhole range -/

/-- **The comparability of the logarithms**: for `m` in the pigeonhole range,
`m ≥ ⌊L/4⌋ + 2h` with `h ≥ 1`, one has `log(ν⁻¹m) ≥ 1` and
`log(ν⁻¹L) ≤ 2 log(ν⁻¹m)`.  The constant `Clog` of
`Terms.sstar_lower_bound_of_terms` is therefore `2`. -/
theorem log_pigeon_range {nu : ℝ} {L m h : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hlog : (11 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ)))
    (hm : L / 4 + 2 * h ≤ m) (hh : 1 ≤ h) :
    (1 : ℝ) ≤ Real.log (nu⁻¹ * (m : ℝ)) ∧
      Real.log (nu⁻¹ * (L : ℝ)) ≤ 2 * Real.log (nu⁻¹ * (m : ℝ)) := by
  have hinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hinvpos : (0 : ℝ) < nu⁻¹ := by linarith only [hinv1]
  have hm1 : 1 ≤ m := by omega
  have hnat : L ≤ 4 * m := by omega
  have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hnatR : (L : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast hnat
  have hmpos : (0 : ℝ) < nu⁻¹ * (m : ℝ) := mul_pos hinvpos (by linarith only [hm1R])
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    rcases Nat.eq_zero_or_pos L with hz | hp
    · exfalso
      subst hz
      simp only [Nat.cast_zero, mul_zero, Real.log_zero] at hlog
      linarith only [hlog]
    · exact_mod_cast hp
  have hLpos : (0 : ℝ) < nu⁻¹ * (L : ℝ) := mul_pos hinvpos (by linarith only [hL1])
  have hle : nu⁻¹ * (L : ℝ) ≤ 4 * (nu⁻¹ * (m : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hnatR hinvpos.le
    linarith only [this]
  have hlogle : Real.log (nu⁻¹ * (L : ℝ)) ≤ Real.log (4 * (nu⁻¹ * (m : ℝ))) :=
    Real.log_le_log hLpos hle
  have hsplit : Real.log (4 * (nu⁻¹ * (m : ℝ))) =
      Real.log 4 + Real.log (nu⁻¹ * (m : ℝ)) :=
    Real.log_mul (by norm_num) (ne_of_gt hmpos)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith only [this]
  constructor
  · linarith only [hlogle, hsplit, hlog4, hlog]
  · linarith only [hlogle, hsplit, hlog4, hlog]

/-! ## The homogenization comparison `e.bell.vs.starell` at `(n, ℓ, L)` -/

/-- **The statement
`Frozen.Section3.sigmaBar_le_sigmaBarStar_homogenization` in the carriers of
the master argument** (`hbell` of `Terms.sstar_lower_bound_of_terms`): the
annealed upper-left scalar at `(ℓ, cu_n)` against the *inverse* of the annealed
lower scalar there, which is the form the master argument uses.  Only the
instantiation is done here. -/
theorem exists_bell_bound (d : ℕ) [NeZero d] :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d), ShellLawPrefix d P →
          ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ n l L : ℕ, 1 ≤ n → CB * Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) ≤ (n : ℝ) →
            n < l → l ≤ L →
            sigmaBarSeq nu l P n ≤
              CB * nu ^ (-(4 : ℝ)) *
                  (((l - n : ℕ) : ℝ) + Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ)) ^ (4 : ℕ) *
                (sigmaBarStarInvSeq nu l P n)⁻¹ := by
  obtain ⟨CB, hCB, hmain⟩ :=
    SuperdiffusionCLT.Frozen.Section3.sigmaBar_le_sigmaBarStar_homogenization d
  refine ⟨CB, hCB, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 n l L hn hnL hnl hlL
  have hkey := hmain nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 n L hn hnL l hnl hlL
  have hpos : 0 < sigmaBarStarInvScalar nu l P (cubeSet (originCube d (n : ℤ))) :=
    sigmaBarStarInvSeq_pos hnu l hPrefix hJ2 hJ3 hJ4 n
  rw [sigmaBarStarScalar_eq_inv hnu l hJ4 (n : ℤ) hpos] at hkey
  exact hkey

/-! ## The removal of the pigeonhole scale -/

section Removal

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **`σ̄_{L,*}^{-1}` is nonincreasing in the spatial scale**, so `σ̄_{L,*}` is
nondecreasing ("since `σ̄_{L,*}^{-1}` is nonincreasing in the spatial
scale and `m ≤ m̄`"). -/
theorem sigmaBarStarScalar_originCube_mono {m mbar : ℕ} (hle : m ≤ mbar) :
    sigmaBarStarScalar nu L P (cubeSet (originCube d (m : ℤ))) ≤
      sigmaBarStarScalar nu L P (cubeSet (originCube d (mbar : ℤ))) := by
  have hm : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (m : ℤ))) :=
    sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 m
  have hb : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d (mbar : ℤ))) :=
    sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 mbar
  rw [sigmaBarStarScalar_eq_inv hnu L hJ4 (m : ℤ) hm,
    sigmaBarStarScalar_eq_inv hnu L hJ4 (mbar : ℤ) hb]
  exact (inv_le_inv₀ hm hb).2
    (antitone_sigmaBarStarInvSeq hnu L hPrefix hJ2 hJ3 hJ4 hle)

end Removal

/-- `y^{-r} ≤ x^{-r}` for `0 < x ≤ y` and `r ≥ 0`. -/
private theorem rpow_neg_le_rpow_neg {x y r : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hr : 0 ≤ r) : y ^ (-r) ≤ x ^ (-r) := by
  have hy : (0 : ℝ) < y := lt_of_lt_of_le hx hxy
  have hxp : (0 : ℝ) < x ^ r := Real.rpow_pos_of_pos hx r
  have hyp : (0 : ℝ) < y ^ r := Real.rpow_pos_of_pos hy r
  rw [Real.rpow_neg hy.le, Real.rpow_neg hx.le]
  exact (inv_le_inv₀ hyp hxp).2 (Real.rpow_le_rpow hx.le hxy hr)

/-- The real-arithmetic core of the transfer: halving the
constant pays for the factor `2` between `m̄^{1/2}` and `m^{1/2}`, and the
logarithmic factor only improves. -/
private theorem transfer_arith {c A1 A2 B1 B2 G1 G2 Y : ℝ}
    (hc : 0 ≤ c) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hB : B2 ≤ 2 * B1) (hB2 : 0 ≤ B2)
    (hG : G2 ≤ G1) (hG1 : 0 ≤ G1)
    (hbound : c * A1 * A2 * B1 * G1 ≤ Y) :
    c / 2 * A1 * A2 * B2 * G2 ≤ Y := by
  have hcA : (0 : ℝ) ≤ c / 2 * A1 * A2 :=
    mul_nonneg (mul_nonneg (by linarith only [hc]) hA1) hA2
  have s1 : c / 2 * A1 * A2 * B2 * G2 ≤ c / 2 * A1 * A2 * B2 * G1 :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hcA hB2)
  have s2 : c / 2 * A1 * A2 * B2 * G1 ≤ c / 2 * A1 * A2 * (2 * B1) * G1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hcA) hG1
  have e : c / 2 * A1 * A2 * (2 * B1) * G1 = c * A1 * A2 * B1 * G1 := by ring
  linarith only [s1, s2, e, hbound]

/-- **The transfer of the lower bound from the pigeonhole scale `m` to the
prescribed scale `m̄`**: "since `m, m̄ ∈ [L/4, L]`, the factors
`m^{1/2}`, `m̄^{1/2}` and `L^{1/2}` are comparable, as are the corresponding
logarithmic factors".  The comparison is carried at the ratio `m̄ ≤ 4m`, which
the pigeonhole range `m ≥ L/4` and `m̄ ≤ L` give, and costs a factor `2` in the
constant. -/
theorem lower_bound_transfer {c cStar nu Y : ℝ} {m mbar : ℕ}
    (hc : 0 ≤ c) (hcStar : 0 ≤ cStar) (hnu : 0 < nu)
    (hm1 : (1 : ℝ) ≤ (m : ℝ))
    (hlogm : (0 : ℝ) < Real.log (nu⁻¹ * (m : ℝ)))
    (hmm : (m : ℝ) ≤ (mbar : ℝ)) (hmbar4 : (mbar : ℝ) ≤ 4 * (m : ℝ))
    (hbound : c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (m : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤ Y) :
    c / 2 * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) * (mbar : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (nu⁻¹ * (mbar : ℝ)) ^ (-((9 : ℝ) / 2)) ≤ Y := by
  have hinvpos : (0 : ℝ) < nu⁻¹ := inv_pos.2 hnu
  have hmbarnn : (0 : ℝ) ≤ (mbar : ℝ) := Nat.cast_nonneg _
  have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hB : (mbar : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 * (m : ℝ) ^ ((1 : ℝ) / 2) := by
    have hstep : (mbar : ℝ) ^ ((1 : ℝ) / 2) ≤ (4 * (m : ℝ)) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hmbarnn hmbar4 (by norm_num)
    have hsplit : (4 * (m : ℝ)) ^ ((1 : ℝ) / 2) =
        (4 : ℝ) ^ ((1 : ℝ) / 2) * (m : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.mul_rpow (by norm_num) (by linarith only [hm1])
    rw [hsplit, h4] at hstep
    exact hstep
  have hlogle : Real.log (nu⁻¹ * (m : ℝ)) ≤ Real.log (nu⁻¹ * (mbar : ℝ)) :=
    Real.log_le_log (mul_pos hinvpos (by linarith only [hm1]))
      (mul_le_mul_of_nonneg_left hmm hinvpos.le)
  have hG : Real.log (nu⁻¹ * (mbar : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
      Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2)) :=
    rpow_neg_le_rpow_neg hlogm hlogle (by norm_num)
  exact transfer_arith hc (Real.rpow_nonneg hcStar _) (Real.rpow_nonneg hnu.le _)
    hB (Real.rpow_nonneg hmbarnn _) hG (Real.rpow_nonneg hlogm.le _) hbound

/-! ## The master inequality at the selected scales -/

/-- **`Terms.master_inequality` with the scale conditions
discharged**: at a scale selection produced by
`exists_scaleSelection_of_threshold`, the conditions `hha`, `haK`, `hEta`,
`hCrude` and `hScaleCond` are all consequences of the selection, so what remains
are exactly
the five term bounds `l.LHS.term1`, `e.RHS.term1`-`e.RHS.term4` and the master
identity `e.ellsep.testing`.

The localization error is the print's own `η_L = Cν^{-5}L3^{-(L'-m)}` at the
selected gap `L' − m = 2a`, so `hT3` is stated with `localizationEta` in place
of the free `etaL` of `Terms.master_inequality`. -/
theorem master_inequality_of_selection {d : ℕ} [NeZero d]
    (CL C1 C2 C3 C4 Ceta K : ℝ) (hCL : 1 ≤ CL) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCeta : 0 ≤ Ceta) (hK : (1 : ℝ) ≤ K)
    (hKlog3 : 8056 ≤ K * Real.log 3)
    (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (cStar Knd delta : ℝ) (hcStar : 0 ≤ cStar) (hKnd : 0 ≤ Knd) (hdelta : 0 ≤ delta)
    (S : ScaleSelection) (hL : 1 ≤ S.L)
    (hlog1 : (1 : ℝ) ≤ Real.log (nu⁻¹ * (S.L : ℝ)))
    (hord : ScalesOrdering S) (hha : 100 * S.a ≤ S.h) (hhm : 2 * S.h ≤ S.m)
    (haeq : S.a = scaleOffset K nu S.L)
    (hCT1 : Ceta ≤ nu⁻¹ * (S.L : ℝ))
    (hCT2 : 2 * C1 + C2 + 4 * C3 ≤ nu⁻¹ * (S.L : ℝ))
    (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e) (q : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hLHS :
      |(∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal -
          cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
        (CL * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + Knd) * vecNormSq p)
    (hT1 :
      |∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uNGlued omega x) - q)) ∂P.toMeasure| ≤
        C1 * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
          ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
            (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))))
    (hT2 :
      |∫ omega : ShellSeq d,
          ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
            ∑ z ∈ largeCubeSubcubes d S.n S.m,
              volumeAverage (openCubeSet z)
                (fun y => vecDot ((w omega).toH1Function.grad y)
                  (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                    (coefficientCutoff nu omega S.ell).toCoeffField y)
                    (uNGlued omega y - p))) ∂P.toMeasure| ≤
        C2 * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)))
    (hT3 :
      ∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot ((w omega).toH1Function.grad y)
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
        C3 * (delta + localizationEta Ceta nu S.L (2 * S.a)) ^ ((1 : ℝ) / 2) *
            Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) *
                (sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) +
              (sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) +
          C3 * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
            ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
              (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
              (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 8))))
    (hT4 :
      |∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
        ∂P.toMeasure| ≤ C4 * (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ))
    (hIdentity :
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal =
        ((∫ omega : ShellSeq d,
              volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
                (fun x => vecDot ((w omega).toH1Function.grad x)
                  (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (uNGlued omega x) - q)) ∂P.toMeasure +
            ∫ omega : ShellSeq d,
              ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
                ∑ z ∈ largeCubeSubcubes d S.n S.m,
                  volumeAverage (openCubeSet z)
                    (fun y => vecDot ((w omega).toH1Function.grad y)
                      (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                        (coefficientCutoff nu omega S.ell).toCoeffField y)
                        (uNGlued omega y - p))) ∂P.toMeasure) +
            ∫ omega : ShellSeq d,
              volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
                (fun y => vecDot ((w omega).toH1Function.grad y)
                  (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                    (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure) -
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                  streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
            ∂P.toMeasure) :
    cStar * (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n ≤
      masterConst CL C3 C4 (crudeLowerConst d) *
          (delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) *
          (sigmaBarSeq nu S.ell P S.n +
            (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n) +
        masterConst CL C3 C4 (crudeLowerConst d) *
          (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) *
          sigmaBarStarInvSeq nu S.LPrime P S.n := by
  have hL1 : (1 : ℝ) ≤ (S.L : ℝ) := by exact_mod_cast hL
  have hlogpos : (0 : ℝ) < Real.log (nu⁻¹ * (S.L : ℝ)) := by linarith only [hlog1]
  have hKlog : (0 : ℝ) ≤ K * Real.log (nu⁻¹ * (S.L : ℝ)) := by
    have : (0 : ℝ) < K := by linarith only [hK]
    positivity
  have ha : K * Real.log (nu⁻¹ * (S.L : ℝ)) ≤ (S.a : ℝ) := by
    rw [haeq]; exact le_scaleOffset K nu S.L
  have haK : ((S.a : ℕ) : ℝ) ≤ K * Real.log (nu⁻¹ * (S.L : ℝ)) + 1 := by
    rw [haeq]; exact le_of_lt (scaleOffset_lt_add_one hKlog)
  have hLPL : S.LPrime ≤ S.L := le_of_lt hord.LPrime_lt_L
  have hellL : S.ell ≤ S.L := by
    have h1 := hord.ell_lt_ellPrime
    have h2 := hord.ellPrime_lt_m
    have h3 := hord.m_lt_LPrime
    have h4 := hord.LPrime_lt_L
    omega
  have hhL : S.h ≤ S.L := by
    have h2 := hord.m_lt_LPrime
    have h4 := hord.LPrime_lt_L
    omega
  have hah : S.a ≤ S.h := by omega
  have hetaL : (0 : ℝ) ≤ localizationEta Ceta nu S.L (2 * S.a) := by
    rw [localizationEta]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCeta (Real.rpow_nonneg hnu.le _))
      (Nat.cast_nonneg _)) (Real.rpow_nonneg (by norm_num) _)
  exact master_inequality CL C1 C2 C3 C4 (crudeLowerConst d) hCL hC3 hC4
    (crudeLowerConst_pos d) nu hnu P hPrefix hJ2 hJ3 hJ4 cStar Knd K delta
    (localizationEta Ceta nu S.L (2 * S.a)) hcStar hKnd hdelta hetaL S hL1 hKlog
    e he p hp q w uMgrad uNGlued hha haK
    (localizationEta_le hnu hnu1 hL hCeta hCT1 hKlog3 ha)
    (crude_lower_bound hnu S.LPrime hPrefix hJ2 hJ3 hJ4 hnu1 hL hLPL)
    (scale_condition_of_selection hC1 hC2 hC3 hnu hnu1 hL hellL hLPL hhL hah hKlog3
      ha hCT2)
    hLHS hT1 hT2 hT3 hT4 hIdentity

/-! ## The assembled lower bound -/

end

end SuperdiffusionCLT.Section3.Setup
