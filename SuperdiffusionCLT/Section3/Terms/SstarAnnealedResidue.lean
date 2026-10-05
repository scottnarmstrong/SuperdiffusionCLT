/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.SstarLowerBoundCloseB

/-!
# The annealed residue `hAnnealed`: the printed display, the survey, and the threshold gap

## The printed statement

The paper's `p.sstar.lower.bound` ("Suboptimal lower bound estimate").  The threshold is the
display `e.L.vs.nu`:

```
L >= m >= 1/2 L    and    m >= C cStar^{-3} ( log^3 (3 + nu^{-1}) log log (3 + nu^{-1})
                                          + (1 + nondegconst) log(3 + nu^{-1} + nondegconst) )
```

and the annealed display `e.sstar.lower.bound` is

```
sigmaBar_L >= sigmaBar_{L,*}(cu_m) >= c cStar^{3/2} nu^2 m^{1/2} log^{-9/2}(nu^{-1} m) .
```

Ours (the hypothesis `hAnnealed` of the lower-bound assembly) reads, with `K` the J5
constant `nondegconst`:

```
sstarPackConst d CM CB * cStar^(3/2) * nu^2 * m^(1/2) * log(nu^{-1} m)^{-9/2}
    <= sigmaBarStarScalar nu L P (cubeSet (originCube d m))
```

under `m <= L`, `L <= 2 * m` and the threshold
`sstarCloseThrConst d * cStar^{-3} * eLvsNuTerm nu cStar K <= m`.

**Term-by-term comparison.**  The exponent `m^{1/2}`: printed `m^{\nf12}`, ours
`(m : ℝ) ^ ((1 : ℝ) / 2)` — identical.  The logarithmic factor: printed
`log^{-9/2}(nu^{-1} m)`, ours `Real.log (nu⁻¹ * (m : ℝ)) ^ (-((9 : ℝ) / 2))` —
identical.  The prefactors: printed `c cStar^{3/2} nu^2`, ours
`sstarPackConst d CM CB * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ)` — identical, with
the printed existential `c(d)` replaced by the named assembly constant (the
printed `c` is existential, so naming it is faithful).  The bound direction and
the two-conjunct conclusion (the paper's display also adds `sigmaBar_L >= sigmaBar_{L,*}`,
which is discharged separately by
`sigmaBarStarScalar_originCube_le_sigmaBarInfinite_frozen`) agree.  The range
condition `L >= m >= 1/2 L` is ours `m <= L`, `L <= 2 * m`.  The threshold has
the same shape; the only difference is inside the two iterated logarithms, where
ours carries `3 + nu^{-1} + cStar^{-1}` in place of the printed `3 + nu^{-1}`.
This replacement is a correction of the printed text (see `ERRATA.md`), recorded by
`Section3/Setup/ThresholdTranslation.lean` as the definition of `eLvsNuTerm`; the
printed bracket without the correction is *weaker*, since
`log(3 + nu^{-1} + cStar^{-1}) >= log(3 + nu^{-1})`, so the correction makes the
hypothesis harder, not easier.

**Conclusion of the comparison: `hAnnealed` matches the printed display**
(modulo the correction above and the naming of the constant).  Nothing in the
display is stronger than the print.

## Related results

* The closest available statement is the assembly of the *whole*
  proposition at the print's own constants, whose residual hypotheses are the master inequality
  `hMaster`, the localization anchor `hLocAnchor`, and the print's own data (`c_0`, `Cenv`, `K`,
  `CL`, `Ceta`, and the eleven threshold shapes of `e.L.vs.nu` listed in
  `Section3/Setup/ThresholdTranslation.lean`).
* `hLocAnchor` is discharged by `sstarCloseCL_anchor` (in `SstarLowerBoundCloseB.lean`) at the
  `d`-only constant `sstarCloseCL d hd`.
* The constant transfer from the assembly's constant to `sstarPackConst d CM CB` is
  `sstarPackConst_bracket_of_assembled` (in `SstarLowerBoundWorkB.lean`).
* The scale shapes `sstarCloseB_scale_le_m`, `sstarCloseB_eleven_le_log` and
  `sstarCloseB_six_log_le_inner` of `Section3/Terms/SstarLowerBoundCloseB.lean` all need a
  threshold constant of at least `10 ^ 8`.

## The threshold and the assembly

The threshold constant of the residue is the *work* constant
`sstarCloseThrConst d = max 10 ^ 6 (2 * sstarWorkEnvelopeConst d + 1)`.  With the range
`cStar <= 2` and `0 < K` the threshold gives `cStar^{-3} >= 1/8` and `eLvsNuTerm >= 1`, hence
only `m >= sstarCloseThrConst d / 8` (`sstarAnnealedResidue_eighth_le_scale` below), while the
assembly's envelope shape is `sstarWorkEnvelopeConst d <= nu^{-1} * L`.  The threshold is therefore
short of that shape by a factor up to `4`; the caller's constant `sstarCloseBThrConst d hd c`
(at least `10 ^ 8 + 16 * sstarCloseThrConst d`) dominates it, so the residue is better stated at
that constant than at the work constant.

The work constant `sstarWorkC0 CM = min (1/2) ((1/(8 CM))^2)` is calibrated for `cStar <= 1`,
while the available upper bound is `cStar <= 2` (`ShellLawJ5.cStar_le_two`, from the display
`e.cstar.bound`); at `CM = 1/16` and `cStar = 2` the assembly's hypothesis
`smallnessParameter c0 cStar <= 1` therefore fails at the work `c_0`, and the truncation must be
`1/4`.  Finally, the threshold constants `sstarCloseThrConst d` and
`sstarCloseBThrConst d hd c` are functions of `d`, `hd`, `c` alone, while the assembly's window
shape, depth shape and tail shape are stated in terms of `CM`, `1/c_0(CM)` and the homogenization
anchor `CB`; a reduction through the assembly therefore needs a constant dominating those anchors
as well.
-/

@[expose] public section

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Setup

namespace SuperdiffusionCLT.Section3.Terms

/-! ## The quantitative core of the printed threshold -/

/-- **The only shape the printed threshold gives about the scale.**  With the
range `cStar <= 2` the factor `cStar ^ (-3)` is at least `1/8`
(`sstarCloseB_rpow_neg_three_ge`) and with `K > 0` the bracket `eLvsNuTerm` is at
least `1` (`sstarCloseB_eLvsNuTerm_ge_one`), so from
`T * cStar ^ (-3) * eLvsNuTerm nu cStar K <= m` with `0 <= T` one gets only
`T / 8 <= m`.  Nothing about `nu` or `K` survives besides those two bounds: this
is all that `e.L.vs.nu` contributes to the comparison of `m` with the named
constants. -/
theorem sstarAnnealedResidue_eighth_le_scale {T nu cStar K : ℝ} {m : ℕ}
    (hT : 0 ≤ T) (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar)
    (hcStar2 : cStar ≤ 2) (hK : 0 < K)
    (hft : T * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K ≤ (m : ℝ)) :
    T / 8 ≤ (m : ℝ) := by
  have hE : (1 : ℝ) ≤ eLvsNuTerm nu cStar K :=
    sstarCloseB_eLvsNuTerm_ge_one hnu hnu1 hcStar hK
  have hS : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) :=
    sstarCloseB_rpow_neg_three_ge hcStar hcStar2
  have hU : (1 / 8 : ℝ) ≤ cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K := by
    have h1 : (1 : ℝ) * (1 / 8) ≤ eLvsNuTerm nu cStar K * (1 / 8) :=
      mul_le_mul_of_nonneg_right hE (by norm_num)
    have h2 : eLvsNuTerm nu cStar K * (1 / 8) ≤
        eLvsNuTerm nu cStar K * cStar ^ (-(3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hS (le_trans zero_le_one hE)
    have h3 : eLvsNuTerm nu cStar K * cStar ^ (-(3 : ℝ)) =
        cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K := mul_comm _ _
    rw [one_mul] at h1
    rw [h3] at h2
    exact le_trans h1 h2
  have hmul : T * (1 / 8 : ℝ) ≤
      T * (cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K) :=
    mul_le_mul_of_nonneg_left hU hT
  have he : T * (cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K) =
      T * cStar ^ (-(3 : ℝ)) * eLvsNuTerm nu cStar K := by ring
  rw [he] at hmul
  have h := le_trans hmul hft
  have hdiv : T * (1 / 8 : ℝ) = T / 8 := by ring
  rwa [hdiv] at h

/-- From `0 < nu <= 1` and `m <= L` one gets `m <= nu^{-1} * L`: the only use of
the standing range `0 < nu <= 1` in the scale shapes below. -/
theorem sstarAnnealedResidue_scale_le_inv_mul_scale {nu : ℝ} {m L : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hmL : m ≤ L) :
    (m : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
  have hn1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnu1
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hmL' : (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast hmL
  calc (m : ℝ) ≤ (L : ℝ) := hmL'
    _ = 1 * (L : ℝ) := by ring
    _ ≤ nu⁻¹ * (L : ℝ) := mul_le_mul_of_nonneg_right hn1 hLnn

end SuperdiffusionCLT.Section3.Terms
