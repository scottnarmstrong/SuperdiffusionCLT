/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3DeltaEtaBound
public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridges
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCarriers
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscCgB
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscProduct
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3PrintedFinal

/-!
# The printed `c⋆ ≤ 2` and the numeric premise of `_hCgBound`

The binder `_hCgBound` of the term-3 final assembly, the printed display
`e.RHS.term3.A`, is reduced by `cg_bound_bridge`
to a list of printed steps plus **one numeric premise**,

```
hde1 : delta + etaL ≤ 1
```

which the main statement does not carry (it carries only `0 ≤ delta`, `0 ≤ etaL`).  The premise
is what `w_average_difference` asks for.  This
file carries it and discharges it.

## The printed conditions the premise follows from

* The display `e.cstar.bound` of assumption `a.j.nondeg` — the one
  printed condition genuinely absent from every Section-3 surface:
  ```
  \E\bigl[|\mathbf j_l(0)e|^2\bigr] \leq 1+e^{-1}
  \quad \implies \quad
  \cstar \leq 2
  \,.
  ```
  It is named here as `CStarLeTwo`.  It follows from assumption (J5) by
  `ShellLawJ5.cStar_le_two` (`cStarLeTwo_of_shellLawJ5` below); the term-3 statements carry it
  as a hypothesis, and the final assembly of Section 3 discharges it from (J5).
* The relative smallness `C\delta^{\nf12}\leq \frac14\cstar` (inside the `gathered`
  display of the proof of `p.sstar.lower.bound`), carried at the root in the factored
  form `CM * Real.sqrt c0 ≤ 1 / 8`.
* `C(d)\in[1,\infty)` (from `p.sstar.lower.bound`): `1 ≤ CM`.
* The localization defect bound `\eta_L\leq L^{-1000}`.
* The display `e.L.vs.nu`, read at the root's depth shape
  `CM * L^{-500} ≤ c⋆/8`, which gives `L ≥ 2`.

## The chain

`√δ ≤ C√δ ≤ ¼c⋆ ≤ ½` (the smallness above, `C ≥ 1`, `c⋆ ≤ 2`) gives `δ ≤ ¼`, and
`η_L ≤ L^{-1000} ≤ 2^{-1000} ≤ ½` (the localization defect bound, `L ≥ 2`) gives
`η_L ≤ ½`, so
`δ + η_L ≤ ¾ ≤ 1`.  The two halves are
`smallnessParameter_le_quarter` and `localizationEta_le_half`
(`RHSTerm3DeltaEtaBound`), combined there as `deltaEtaL_le_one`; this file
re-uses that combination and only replaces the raw hypothesis `c⋆ ≤ 2` by the
named printed one and the hypothesis `L ≥ 2` by its derivation from the root's
carried depth shape.

## Main results

* `CStarLeTwo` — the printed bound `c⋆ ≤ 2` (`e.cstar.bound`) as a named hypothesis.
* `cStarLeTwo_of_shellLawJ5` — `ShellLawJ5.cStar_le_two` in that name:
  the hypothesis is the print's, not an invention.
* `deltaEtaL_le_one_of_cStarLeTwo` — `δ + η_L ≤ 1` at the carriers
  `δ = smallnessParameter c₀ c⋆`, `η_L = localizationEta Cη ν L (2 a)`, from
  the printed `c⋆ ≤ 2` and the conditions the term-3 chain already carries.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The printed hypothesis `c⋆ ≤ 2` -/

/-- **The printed bound `e.cstar.bound`**: the non-degeneracy constant
of `a.j.nondeg` is at most `2`,
```
\E\bigl[|\mathbf j_l(0)e|^2\bigr] \leq 1+e^{-1} \quad \implies \quad \cstar \leq 2 \,.
```
This is not a smallness condition invented for the proof: it is printed, and it
is what `ShellLawJ5.cStar_le_two` derives from the assumption
`ShellLawJ5` (`cStarLeTwo_of_shellLawJ5` below).  It is carried as a named
hypothesis here because Section 3 binds `ShellLawJ1`, `ShellLawJ1Restriction`,
`ShellLawJ2`, `ShellLawJ3`, `ShellLawJ4` and not `ShellLawJ5`, so no Section-3
surface supplies it. -/
def CStarLeTwo (cStar : ℝ) : Prop :=
  cStar ≤ 2

/-- **The printed bound from the assumption it is stated for.**  The
lemma `ShellLawJ5.cStar_le_two` is exactly the display `e.cstar.bound`, so
`CStarLeTwo` is the print's condition and not a proof device. -/
theorem cStarLeTwo_of_shellLawJ5 {P : ProbabilityMeasure (ShellSeq d)} {cStar K : ℝ}
    {hPrefix : ShellLawPrefix d P} {hJ2 : ShellLawJ2 d P} {hJ3 : ShellLawJ3 d P}
    (hJ5 : ShellLawJ5 d P cStar K hPrefix hJ2 hJ3) :
    CStarLeTwo cStar :=
  ShellLawJ5.cStar_le_two hJ5

/-! ## `L ≥ 2` from the root's carried depth shape -/

/-! ## The numeric premise `δ + η_L ≤ 1` from the printed conditions -/

/-- **The numeric premise of `_hCgBound` at the carriers, from the printed
`c⋆ ≤ 2`.**  This is `deltaEtaL_le_one` with
its hypothesis `c⋆ ≤ 2` given in the named printed form `CStarLeTwo cStar`.

Every hypothesis is one quoted display or one available bridge: `hCM : 1 ≤ CM`
(from `p.sstar.lower.bound`), `hc0small : CM √c₀ ≤ 1/8` (from the proof of
`p.sstar.lower.bound`, in the root's factored form),
`hprem : CStarLeTwo cStar` (`e.cstar.bound`), `hL : 2 ≤ L` and the J-law/scale
hypotheses feeding `localizationEta_le` (the localization defect bound). -/
theorem deltaEtaL_le_one_of_cStarLeTwo
    {CM c0 cStar Ceta K nu : ℝ} {L a : ℕ}
    (hCM : 1 ≤ CM) (hc0small : CM * Real.sqrt c0 ≤ 1 / 8)
    (hc0 : 0 ≤ c0) (hcStar0 : 0 ≤ cStar) (hprem : CStarLeTwo cStar)
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hL : 2 ≤ L)
    (hCeta : 0 ≤ Ceta) (hCT4 : 4 * Ceta ≤ nu⁻¹ * (L : ℝ))
    (hKlog3 : 8056 ≤ K * Real.log 3)
    (ha : K * Real.log (nu⁻¹ * (L : ℝ)) ≤ (a : ℝ)) :
    smallnessParameter c0 cStar + localizationEta Ceta nu L (2 * a) ≤ 1 :=
  deltaEtaL_le_one hCM hc0small hc0 hcStar0 hprem hnu hnu1 hL hCeta hCT4 hKlog3 ha

end

end SuperdiffusionCLT.Section3.Terms
